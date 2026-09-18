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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_process_child_kill(lean_object*, lean_object*);
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
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
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
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__4;
static lean_once_cell_t l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__5;
static const lean_ctor_object l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__6 = (const lean_object*)&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__6_value;
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___boxed(lean_object*, lean_object*);
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
static lean_object* _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_182_ = lean_string_utf8_byte_size(v___x_181_);
return v___x_182_;
}
}
static uint8_t _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1);
v___x_185_ = lean_nat_dec_eq(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_186_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1, &l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1_once, _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_187_);
lean_ctor_set(v___x_189_, 2, v___x_186_);
return v___x_189_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3);
v___x_191_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__4, &l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__4_once, _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__4);
v___x_194_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3);
v___x_195_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 2, v___x_192_);
lean_ctor_set(v___x_195_, 3, v___x_192_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(lean_object* v_s_198_, lean_object* v_replacement_199_){
_start:
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__0));
v___x_201_ = lean_uint8_once(&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__5, &l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__5_once, _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__5);
v___x_203_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(v_s_198_, v_replacement_199_, v___x_202_, v___x_200_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__6));
v___x_205_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(v_s_198_, v_replacement_199_, v___x_204_, v___x_200_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___boxed(lean_object* v_s_206_, lean_object* v_replacement_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(v_s_206_, v_replacement_207_);
lean_dec_ref(v_replacement_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(lean_object* v_s_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_211_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_212_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote___closed__0));
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_string_utf8_byte_size(v_s_210_);
v___x_215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_215_, 0, v_s_210_);
lean_ctor_set(v___x_215_, 1, v___x_213_);
lean_ctor_set(v___x_215_, 2, v___x_214_);
v___x_216_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(v___x_215_, v___x_212_);
v___x_217_ = lean_string_append(v___x_211_, v___x_216_);
lean_dec_ref(v___x_216_);
v___x_218_ = lean_string_append(v___x_217_, v___x_211_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0(lean_object* v_s_219_, lean_object* v_pattern_220_, lean_object* v_replacement_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(v_s_219_, v_replacement_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___boxed(lean_object* v_s_223_, lean_object* v_pattern_224_, lean_object* v_replacement_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0(v_s_223_, v_pattern_224_, v_replacement_225_);
lean_dec_ref(v_replacement_225_);
lean_dec_ref(v_pattern_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0(lean_object* v_s_227_, lean_object* v_replacement_228_, lean_object* v_inst_229_, lean_object* v_R_230_, lean_object* v_a_231_, lean_object* v_b_232_, lean_object* v_c_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(v_s_227_, v_replacement_228_, v_a_231_, v_b_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___boxed(lean_object* v_s_235_, lean_object* v_replacement_236_, lean_object* v_inst_237_, lean_object* v_R_238_, lean_object* v_a_239_, lean_object* v_b_240_, lean_object* v_c_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0(v_s_235_, v_replacement_236_, v_inst_237_, v_R_238_, v_a_239_, v_b_240_, v_c_241_);
lean_dec_ref(v_replacement_236_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1(lean_object* v_s_243_, lean_object* v_pos_244_){
_start:
{
lean_object* v_str_245_; lean_object* v_startInclusive_246_; lean_object* v_endExclusive_247_; lean_object* v___x_248_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v_decide_259_; 
v_str_245_ = lean_ctor_get(v_s_243_, 0);
v_startInclusive_246_ = lean_ctor_get(v_s_243_, 1);
v_endExclusive_247_ = lean_ctor_get(v_s_243_, 2);
v___x_248_ = lean_nat_add(v_startInclusive_246_, v_pos_244_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_nat_sub(v_endExclusive_247_, v___x_248_);
v_decide_259_ = lean_nat_dec_eq(v___x_257_, v___x_258_);
lean_dec(v___x_258_);
if (v_decide_259_ == 0)
{
uint32_t v___x_260_; uint8_t v___y_267_; uint32_t v___x_272_; uint8_t v___x_273_; 
v___x_260_ = lean_string_utf8_get_fast(v_str_245_, v___x_248_);
v___x_272_ = 65;
v___x_273_ = lean_uint32_dec_le(v___x_272_, v___x_260_);
if (v___x_273_ == 0)
{
v___y_267_ = v___x_273_;
goto v___jp_266_;
}
else
{
uint32_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = 90;
v___x_275_ = lean_uint32_dec_le(v___x_260_, v___x_274_);
v___y_267_ = v___x_275_;
goto v___jp_266_;
}
v___jp_261_:
{
uint32_t v___x_262_; uint8_t v___x_263_; 
v___x_262_ = 48;
v___x_263_ = lean_uint32_dec_le(v___x_262_, v___x_260_);
if (v___x_263_ == 0)
{
lean_dec(v___x_248_);
return v_pos_244_;
}
else
{
uint32_t v___x_264_; uint8_t v___x_265_; 
v___x_264_ = 57;
v___x_265_ = lean_uint32_dec_le(v___x_260_, v___x_264_);
if (v___x_265_ == 0)
{
lean_dec(v___x_248_);
return v_pos_244_;
}
else
{
goto v___jp_249_;
}
}
}
v___jp_266_:
{
if (v___y_267_ == 0)
{
uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 97;
v___x_269_ = lean_uint32_dec_le(v___x_268_, v___x_260_);
if (v___x_269_ == 0)
{
goto v___jp_261_;
}
else
{
uint32_t v___x_270_; uint8_t v___x_271_; 
v___x_270_ = 122;
v___x_271_ = lean_uint32_dec_le(v___x_260_, v___x_270_);
if (v___x_271_ == 0)
{
goto v___jp_261_;
}
else
{
goto v___jp_249_;
}
}
}
else
{
goto v___jp_249_;
}
}
}
else
{
lean_dec(v___x_248_);
return v_pos_244_;
}
v___jp_249_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_250_ = lean_string_utf8_next_fast(v_str_245_, v___x_248_);
v___x_251_ = lean_nat_sub(v___x_250_, v___x_248_);
lean_dec(v___x_248_);
v___x_252_ = lean_nat_add(v_pos_244_, v___x_251_);
lean_dec(v___x_251_);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v_pos_244_, v___x_253_);
v___x_255_ = lean_nat_dec_le(v___x_254_, v___x_252_);
lean_dec(v___x_254_);
if (v___x_255_ == 0)
{
lean_dec(v___x_252_);
return v_pos_244_;
}
else
{
lean_dec(v_pos_244_);
v_pos_244_ = v___x_252_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1___boxed(lean_object* v_s_276_, lean_object* v_pos_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1(v_s_276_, v_pos_277_);
lean_dec_ref(v_s_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(lean_object* v_decoded_279_, lean_object* v___x_280_, lean_object* v___x_281_, lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_box(0);
switch(lean_obj_tag(v_a_282_))
{
case 0:
{
lean_object* v_pos_285_; lean_object* v___x_286_; 
v_pos_285_ = lean_ctor_get(v_a_282_, 0);
lean_inc(v_pos_285_);
lean_dec_ref_known(v_a_282_, 1);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v_pos_285_);
return v___x_286_;
}
case 1:
{
lean_object* v_pos_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_296_; 
v_pos_287_ = lean_ctor_get(v_a_282_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_a_282_);
if (v_isSharedCheck_296_ == 0)
{
v___x_289_ = v_a_282_;
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_pos_287_);
lean_dec(v_a_282_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = lean_string_utf8_next_fast(v_decoded_279_, v_pos_287_);
lean_dec(v_pos_287_);
if (v_isShared_290_ == 0)
{
lean_ctor_set_tag(v___x_289_, 0);
lean_ctor_set(v___x_289_, 0, v___x_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_295_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
v_a_282_ = v___x_293_;
v_b_283_ = v___x_284_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_297_; lean_object* v_table_298_; lean_object* v_stackPos_299_; lean_object* v_needlePos_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_353_; 
v_needle_297_ = lean_ctor_get(v_a_282_, 0);
v_table_298_ = lean_ctor_get(v_a_282_, 1);
v_stackPos_299_ = lean_ctor_get(v_a_282_, 2);
v_needlePos_300_ = lean_ctor_get(v_a_282_, 3);
v_isSharedCheck_353_ = !lean_is_exclusive(v_a_282_);
if (v_isSharedCheck_353_ == 0)
{
v___x_302_ = v_a_282_;
v_isShared_303_ = v_isSharedCheck_353_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_needlePos_300_);
lean_inc(v_stackPos_299_);
lean_inc(v_table_298_);
lean_inc(v_needle_297_);
lean_dec(v_a_282_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_353_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_str_304_; lean_object* v_startInclusive_305_; lean_object* v_endExclusive_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_str_304_ = lean_ctor_get(v_needle_297_, 0);
v_startInclusive_305_ = lean_ctor_get(v_needle_297_, 1);
v_endExclusive_306_ = lean_ctor_get(v_needle_297_, 2);
v___x_307_ = lean_nat_sub(v_stackPos_299_, v_needlePos_300_);
v___x_308_ = lean_nat_sub(v_endExclusive_306_, v_startInclusive_305_);
v___x_309_ = lean_nat_add(v___x_307_, v___x_308_);
v___x_310_ = lean_nat_dec_le(v___x_309_, v___x_281_);
lean_dec(v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
lean_dec(v___x_308_);
lean_del_object(v___x_302_);
lean_dec(v_needlePos_300_);
lean_dec(v_stackPos_299_);
lean_dec_ref(v_table_298_);
lean_dec_ref(v_needle_297_);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_add(v___x_307_, v___x_311_);
lean_dec(v___x_307_);
v___x_313_ = lean_nat_dec_le(v___x_312_, v___x_281_);
lean_dec(v___x_312_);
if (v___x_313_ == 0)
{
lean_inc(v_b_283_);
return v_b_283_;
}
else
{
lean_object* v___x_314_; 
v___x_314_ = lean_box(3);
v_a_282_ = v___x_314_;
v_b_283_ = v___x_284_;
goto _start;
}
}
else
{
uint8_t v_stackByte_316_; lean_object* v___x_317_; uint8_t v_patByte_318_; uint8_t v___x_319_; 
lean_dec(v___x_307_);
lean_inc(v_stackPos_299_);
v_stackByte_316_ = lean_string_get_byte_fast(v_decoded_279_, v_stackPos_299_);
v___x_317_ = lean_nat_add(v_startInclusive_305_, v_needlePos_300_);
v_patByte_318_ = lean_string_get_byte_fast(v_str_304_, v___x_317_);
v___x_319_ = lean_uint8_dec_eq(v_stackByte_316_, v_patByte_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; uint8_t v_decide_321_; 
lean_dec(v___x_308_);
v___x_320_ = lean_unsigned_to_nat(0u);
v_decide_321_ = lean_nat_dec_eq(v_needlePos_300_, v___x_320_);
if (v_decide_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_newNeedlePos_324_; uint8_t v___x_325_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_sub(v_needlePos_300_, v___x_322_);
lean_dec(v_needlePos_300_);
v_newNeedlePos_324_ = lean_array_fget_borrowed(v_table_298_, v___x_323_);
lean_dec(v___x_323_);
v___x_325_ = lean_nat_dec_eq(v_newNeedlePos_324_, v___x_320_);
if (v___x_325_ == 0)
{
lean_object* v___x_327_; 
lean_inc(v_newNeedlePos_324_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 3, v_newNeedlePos_324_);
v___x_327_ = v___x_302_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_needle_297_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_table_298_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v_stackPos_299_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v_newNeedlePos_324_);
v___x_327_ = v_reuseFailAlloc_329_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
v_a_282_ = v___x_327_;
v_b_283_ = v___x_284_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_330_; lean_object* v___x_332_; 
v_nextStackPos_330_ = l_String_Slice_posGE___redArg(v___x_280_, v_stackPos_299_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 3, v___x_320_);
lean_ctor_set(v___x_302_, 2, v_nextStackPos_330_);
v___x_332_ = v___x_302_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_needle_297_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_table_298_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_nextStackPos_330_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v___x_320_);
v___x_332_ = v_reuseFailAlloc_334_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
v_a_282_ = v___x_332_;
v_b_283_ = v___x_284_;
goto _start;
}
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_nextStackPos_337_; lean_object* v___x_339_; 
lean_dec(v_needlePos_300_);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_add(v_stackPos_299_, v___x_335_);
lean_dec(v_stackPos_299_);
v_nextStackPos_337_ = l_String_Slice_posGE___redArg(v___x_280_, v___x_336_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 3, v___x_320_);
lean_ctor_set(v___x_302_, 2, v_nextStackPos_337_);
v___x_339_ = v___x_302_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_needle_297_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_table_298_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_nextStackPos_337_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v___x_320_);
v___x_339_ = v_reuseFailAlloc_341_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
v_a_282_ = v___x_339_;
v_b_283_ = v___x_284_;
goto _start;
}
}
}
else
{
lean_object* v___x_342_; lean_object* v_nextStackPos_343_; lean_object* v_nextNeedlePos_344_; uint8_t v_decide_345_; 
v___x_342_ = lean_unsigned_to_nat(1u);
v_nextStackPos_343_ = lean_nat_add(v_stackPos_299_, v___x_342_);
lean_dec(v_stackPos_299_);
v_nextNeedlePos_344_ = lean_nat_add(v_needlePos_300_, v___x_342_);
lean_dec(v_needlePos_300_);
v_decide_345_ = lean_nat_dec_eq(v_nextNeedlePos_344_, v___x_308_);
lean_dec(v___x_308_);
if (v_decide_345_ == 0)
{
lean_object* v___x_347_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 3, v_nextNeedlePos_344_);
lean_ctor_set(v___x_302_, 2, v_nextStackPos_343_);
v___x_347_ = v___x_302_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_needle_297_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_table_298_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_nextStackPos_343_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v_nextNeedlePos_344_);
v___x_347_ = v_reuseFailAlloc_349_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
v_a_282_ = v___x_347_;
goto _start;
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_del_object(v___x_302_);
lean_dec_ref(v_table_298_);
lean_dec_ref(v_needle_297_);
v___x_350_ = lean_nat_sub(v_nextStackPos_343_, v_nextNeedlePos_344_);
lean_dec(v_nextNeedlePos_344_);
lean_dec(v_nextStackPos_343_);
v___x_351_ = l_String_Slice_pos_x21(v___x_280_, v___x_350_);
lean_dec(v___x_350_);
v___x_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
}
}
}
default: 
{
lean_inc(v_b_283_);
return v_b_283_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg___boxed(lean_object* v_decoded_354_, lean_object* v___x_355_, lean_object* v___x_356_, lean_object* v_a_357_, lean_object* v_b_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(v_decoded_354_, v___x_355_, v___x_356_, v_a_357_, v_b_358_);
lean_dec(v_b_358_);
lean_dec(v___x_356_);
lean_dec_ref(v___x_355_);
lean_dec_ref(v_decoded_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(lean_object* v_output_362_, lean_object* v_port_363_){
_start:
{
lean_object* v_decoded_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_serverUrl_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___y_374_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_decoded_364_ = l_System_Uri_unescapeUri(v_output_362_);
v___x_365_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__0));
v___x_366_ = l_Nat_reprFast(v_port_363_);
v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
lean_dec_ref(v___x_366_);
v___x_368_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__1));
v_serverUrl_369_ = lean_string_append(v___x_367_, v___x_368_);
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = lean_string_utf8_byte_size(v_decoded_364_);
lean_inc_ref(v_decoded_364_);
v___x_372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_372_, 0, v_decoded_364_);
lean_ctor_set(v___x_372_, 1, v___x_370_);
lean_ctor_set(v___x_372_, 2, v___x_371_);
v___x_399_ = lean_string_utf8_byte_size(v_serverUrl_369_);
v___x_400_ = lean_nat_dec_eq(v___x_399_, v___x_370_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_inc_ref(v_serverUrl_369_);
v___x_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_401_, 0, v_serverUrl_369_);
lean_ctor_set(v___x_401_, 1, v___x_370_);
lean_ctor_set(v___x_401_, 2, v___x_399_);
v___x_402_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_401_);
v___x_403_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
lean_ctor_set(v___x_403_, 2, v___x_370_);
lean_ctor_set(v___x_403_, 3, v___x_370_);
v___y_374_ = v___x_403_;
goto v___jp_373_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__6));
v___y_374_ = v___x_404_;
goto v___jp_373_;
}
v___jp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_box(0);
v___x_376_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(v_decoded_364_, v___x_372_, v___x_371_, v___y_374_, v___x_375_);
lean_dec_ref_known(v___x_372_, 3);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_dec_ref(v_serverUrl_369_);
lean_dec_ref(v_decoded_364_);
return v___x_375_;
}
else
{
lean_object* v_val_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_398_; 
v_val_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_398_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_398_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_val_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_398_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_381_ = lean_string_utf8_byte_size(v_serverUrl_369_);
v___x_382_ = lean_nat_sub(v___x_371_, v_val_377_);
v___x_383_ = lean_nat_dec_le(v___x_381_, v___x_382_);
lean_dec(v___x_382_);
if (v___x_383_ == 0)
{
lean_del_object(v___x_379_);
lean_dec(v_val_377_);
lean_dec_ref(v_serverUrl_369_);
lean_dec_ref(v_decoded_364_);
return v___x_375_;
}
else
{
uint8_t v___x_384_; 
v___x_384_ = lean_string_memcmp(v_decoded_364_, v_serverUrl_369_, v_val_377_, v___x_370_, v___x_381_);
lean_dec_ref(v_serverUrl_369_);
if (v___x_384_ == 0)
{
lean_del_object(v___x_379_);
lean_dec(v_val_377_);
lean_dec_ref(v_decoded_364_);
return v___x_375_;
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
lean_inc(v_val_377_);
lean_inc_ref_n(v_decoded_364_, 2);
v___x_385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_385_, 0, v_decoded_364_);
lean_ctor_set(v___x_385_, 1, v_val_377_);
lean_ctor_set(v___x_385_, 2, v___x_371_);
v___x_386_ = l_String_Slice_pos_x21(v___x_385_, v___x_381_);
lean_dec_ref_known(v___x_385_, 3);
v___x_387_ = lean_nat_add(v_val_377_, v___x_386_);
lean_dec(v___x_386_);
lean_dec(v_val_377_);
lean_inc(v___x_387_);
v___x_388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_388_, 0, v_decoded_364_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
lean_ctor_set(v___x_388_, 2, v___x_371_);
v___x_389_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1(v___x_388_, v___x_370_);
lean_dec_ref_known(v___x_388_, 3);
v___x_390_ = lean_nat_add(v___x_387_, v___x_389_);
lean_dec(v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_391_, 0, v_decoded_364_);
lean_ctor_set(v___x_391_, 1, v___x_387_);
lean_ctor_set(v___x_391_, 2, v___x_390_);
v___x_392_ = l_String_Slice_toString(v___x_391_);
lean_dec_ref_known(v___x_391_, 3);
v___x_393_ = lean_string_utf8_byte_size(v___x_392_);
v___x_394_ = lean_nat_dec_eq(v___x_393_, v___x_370_);
if (v___x_394_ == 0)
{
lean_object* v___x_396_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_392_);
v___x_396_ = v___x_379_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_392_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
else
{
lean_dec_ref(v___x_392_);
lean_del_object(v___x_379_);
return v___x_375_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___boxed(lean_object* v_output_405_, lean_object* v_port_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(v_output_405_, v_port_406_);
lean_dec_ref(v_output_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0(lean_object* v_decoded_408_, lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v_inst_411_, lean_object* v_R_412_, lean_object* v_a_413_, lean_object* v_b_414_, lean_object* v_c_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(v_decoded_408_, v___x_409_, v___x_410_, v_a_413_, v_b_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___boxed(lean_object* v_decoded_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v_inst_420_, lean_object* v_R_421_, lean_object* v_a_422_, lean_object* v_b_423_, lean_object* v_c_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0(v_decoded_417_, v___x_418_, v___x_419_, v_inst_420_, v_R_421_, v_a_422_, v_b_423_, v_c_424_);
lean_dec(v_b_423_);
lean_dec(v___x_419_);
lean_dec_ref(v___x_418_);
lean_dec_ref(v_decoded_417_);
return v_res_425_;
}
}
static lean_object* _init_l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l_instInhabitedError;
v___x_427_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_427_, 0, lean_box(0));
lean_closure_set(v___x_427_, 1, lean_box(0));
lean_closure_set(v___x_427_, 2, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(lean_object* v_msg_428_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_1178__overap_431_; lean_object* v___x_432_; 
v___x_430_ = lean_obj_once(&l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0, &l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0_once, _init_l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0);
v___x_1178__overap_431_ = lean_panic_fn_borrowed(v___x_430_, v_msg_428_);
v___x_432_ = lean_apply_1(v___x_1178__overap_431_, lean_box(0));
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___boxed(lean_object* v_msg_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(v_msg_433_);
return v_res_435_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__2));
v___x_440_ = lean_mk_io_user_error(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(lean_object* v_val_441_, lean_object* v_timeoutMs_442_, lean_object* v_cfg_443_, lean_object* v_proc_444_, lean_object* v_logFile_445_, lean_object* v_port_446_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_448_ = lean_box(0);
v___x_449_ = lean_io_mono_ms_now();
v___x_450_ = lean_nat_sub(v___x_449_, v_val_441_);
lean_dec(v___x_449_);
v___x_451_ = lean_nat_dec_lt(v_timeoutMs_442_, v___x_450_);
lean_dec(v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
v___x_452_ = lean_io_process_child_try_wait(v_cfg_443_, v_proc_444_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
if (lean_obj_tag(v_a_453_) == 1)
{
lean_object* v_val_454_; lean_object* v___x_455_; 
lean_dec(v_port_446_);
v_val_454_ = lean_ctor_get(v_a_453_, 0);
lean_inc(v_val_454_);
lean_dec_ref_known(v_a_453_, 1);
v___x_455_ = l_IO_FS_readFile(v_logFile_445_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_472_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_472_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_472_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_472_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; uint32_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_460_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__0));
v___x_461_ = lean_unbox_uint32(v_val_454_);
lean_dec(v_val_454_);
v___x_462_ = lean_uint32_to_nat(v___x_461_);
v___x_463_ = l_Nat_reprFast(v___x_462_);
v___x_464_ = lean_string_append(v___x_460_, v___x_463_);
lean_dec_ref(v___x_463_);
v___x_465_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__1));
v___x_466_ = lean_string_append(v___x_464_, v___x_465_);
v___x_467_ = lean_string_append(v___x_466_, v_a_456_);
lean_dec(v_a_456_);
v___x_468_ = lean_mk_io_user_error(v___x_467_);
if (v_isShared_459_ == 0)
{
lean_ctor_set_tag(v___x_458_, 1);
lean_ctor_set(v___x_458_, 0, v___x_468_);
v___x_470_ = v___x_458_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v_val_454_);
v_a_473_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_455_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_455_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
else
{
lean_object* v___x_481_; 
lean_dec(v_a_453_);
v___x_481_ = l_IO_FS_readFile(v_logFile_445_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_494_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_494_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_494_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; 
lean_inc(v_port_446_);
v___x_486_ = l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(v_a_482_, v_port_446_);
lean_dec(v_a_482_);
if (lean_obj_tag(v___x_486_) == 1)
{
lean_object* v___x_487_; lean_object* v___x_489_; 
lean_dec(v_port_446_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_448_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_487_);
v___x_489_ = v___x_484_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
else
{
uint32_t v___x_491_; lean_object* v___x_492_; 
lean_dec(v___x_486_);
lean_del_object(v___x_484_);
v___x_491_ = 200;
v___x_492_ = l_IO_sleep(v___x_491_);
goto _start;
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec(v_port_446_);
v_a_495_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_481_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_481_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec(v_port_446_);
v_a_503_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_452_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_452_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_port_446_);
v___x_511_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___boxed(lean_object* v_val_513_, lean_object* v_timeoutMs_514_, lean_object* v_cfg_515_, lean_object* v_proc_516_, lean_object* v_logFile_517_, lean_object* v_port_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v_val_513_, v_timeoutMs_514_, v_cfg_515_, v_proc_516_, v_logFile_517_, v_port_518_);
lean_dec_ref(v_logFile_517_);
lean_dec_ref(v_proc_516_);
lean_dec_ref(v_cfg_515_);
lean_dec(v_timeoutMs_514_);
lean_dec(v_val_513_);
return v_res_520_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_524_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__2));
v___x_525_ = lean_unsigned_to_nat(2u);
v___x_526_ = lean_unsigned_to_nat(58u);
v___x_527_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__1));
v___x_528_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__0));
v___x_529_ = l_mkPanicMessageWithDecl(v___x_528_, v___x_527_, v___x_526_, v___x_525_, v___x_524_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(lean_object* v_cfg_530_, lean_object* v_logFile_531_, lean_object* v_proc_532_, lean_object* v_port_533_, lean_object* v_timeoutMs_534_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_io_mono_ms_now();
v___x_537_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v___x_536_, v_timeoutMs_534_, v_cfg_530_, v_proc_532_, v_logFile_531_, v_port_533_);
lean_dec(v___x_536_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_549_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_549_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_549_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_549_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_fst_542_; 
v_fst_542_ = lean_ctor_get(v_a_538_, 0);
lean_inc(v_fst_542_);
lean_dec(v_a_538_);
if (lean_obj_tag(v_fst_542_) == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_del_object(v___x_540_);
v___x_543_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3, &l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3);
v___x_544_ = l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(v___x_543_);
return v___x_544_;
}
else
{
lean_object* v_val_545_; lean_object* v___x_547_; 
v_val_545_ = lean_ctor_get(v_fst_542_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v_fst_542_, 1);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v_val_545_);
v___x_547_ = v___x_540_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_val_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_a_550_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_537_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_537_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___boxed(lean_object* v_cfg_558_, lean_object* v_logFile_559_, lean_object* v_proc_560_, lean_object* v_port_561_, lean_object* v_timeoutMs_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(v_cfg_558_, v_logFile_559_, v_proc_560_, v_port_561_, v_timeoutMs_562_);
lean_dec(v_timeoutMs_562_);
lean_dec_ref(v_proc_560_);
lean_dec_ref(v_logFile_559_);
lean_dec_ref(v_cfg_558_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(lean_object* v_val_565_, lean_object* v_timeoutMs_566_, lean_object* v_cfg_567_, lean_object* v_proc_568_, lean_object* v_logFile_569_, lean_object* v_port_570_, lean_object* v_inst_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v_val_565_, v_timeoutMs_566_, v_cfg_567_, v_proc_568_, v_logFile_569_, v_port_570_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___boxed(lean_object* v_val_575_, lean_object* v_timeoutMs_576_, lean_object* v_cfg_577_, lean_object* v_proc_578_, lean_object* v_logFile_579_, lean_object* v_port_580_, lean_object* v_inst_581_, lean_object* v_a_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(v_val_575_, v_timeoutMs_576_, v_cfg_577_, v_proc_578_, v_logFile_579_, v_port_580_, v_inst_581_, v_a_582_);
lean_dec_ref(v_a_582_);
lean_dec_ref(v_logFile_579_);
lean_dec_ref(v_proc_578_);
lean_dec_ref(v_cfg_577_);
lean_dec(v_timeoutMs_576_);
lean_dec(v_val_575_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(lean_object* v_j_585_, lean_object* v_k_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l_Lean_Json_getObjValD(v_j_585_, v_k_586_);
v___x_588_ = l_Lean_Json_getStr_x3f(v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0___boxed(lean_object* v_j_589_, lean_object* v_k_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_j_589_, v_k_590_);
lean_dec_ref(v_k_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(lean_object* v_e_592_){
_start:
{
if (lean_obj_tag(v_e_592_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_602_; 
v_a_594_ = lean_ctor_get(v_e_592_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v_e_592_);
if (v_isSharedCheck_602_ == 0)
{
v___x_596_ = v_e_592_;
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v_e_592_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = lean_mk_io_user_error(v_a_594_);
if (v_isShared_597_ == 0)
{
lean_ctor_set_tag(v___x_596_, 1);
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_603_ = lean_ctor_get(v_e_592_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_e_592_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v_e_592_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v_e_592_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 0);
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg___boxed(lean_object* v_e_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v_e_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(lean_object* v_00_u03b1_614_, lean_object* v_e_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v_e_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___boxed(lean_object* v_00_u03b1_618_, lean_object* v_e_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(v_00_u03b1_618_, v_e_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(size_t v_sz_622_, size_t v_i_623_, lean_object* v_bs_624_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = lean_usize_dec_lt(v_i_623_, v_sz_622_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v_bs_624_);
return v___x_626_;
}
else
{
lean_object* v_v_627_; lean_object* v___x_628_; lean_object* v_bs_x27_629_; size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
v_v_627_ = lean_array_uget(v_bs_624_, v_i_623_);
v___x_628_ = lean_unsigned_to_nat(0u);
v_bs_x27_629_ = lean_array_uset(v_bs_624_, v_i_623_, v___x_628_);
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_add(v_i_623_, v___x_630_);
v___x_632_ = lean_array_uset(v_bs_x27_629_, v_i_623_, v_v_627_);
v_i_623_ = v___x_631_;
v_bs_624_ = v___x_632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_634_, lean_object* v_i_635_, lean_object* v_bs_636_){
_start:
{
size_t v_sz_boxed_637_; size_t v_i_boxed_638_; lean_object* v_res_639_; 
v_sz_boxed_637_ = lean_unbox_usize(v_sz_634_);
lean_dec(v_sz_634_);
v_i_boxed_638_ = lean_unbox_usize(v_i_635_);
lean_dec(v_i_635_);
v_res_639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(v_sz_boxed_637_, v_i_boxed_638_, v_bs_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(lean_object* v_x_641_){
_start:
{
if (lean_obj_tag(v_x_641_) == 4)
{
lean_object* v_elems_642_; size_t v_sz_643_; size_t v___x_644_; lean_object* v___x_645_; 
v_elems_642_ = lean_ctor_get(v_x_641_, 0);
lean_inc_ref(v_elems_642_);
lean_dec_ref_known(v_x_641_, 1);
v_sz_643_ = lean_array_size(v_elems_642_);
v___x_644_ = ((size_t)0ULL);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(v_sz_643_, v___x_644_, v_elems_642_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_646_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_647_ = lean_unsigned_to_nat(80u);
v___x_648_ = l_Lean_Json_pretty(v_x_641_, v___x_647_);
v___x_649_ = lean_string_append(v___x_646_, v___x_648_);
lean_dec_ref(v___x_648_);
v___x_650_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_651_ = lean_string_append(v___x_649_, v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(lean_object* v_j_653_, lean_object* v_k_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = l_Lean_Json_getObjValD(v_j_653_, v_k_654_);
v___x_656_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3___boxed(lean_object* v_j_657_, lean_object* v_k_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_j_657_, v_k_658_);
lean_dec_ref(v_k_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(size_t v_sz_660_, size_t v_i_661_, lean_object* v_bs_662_){
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
v___x_666_ = l_Lean_Json_getNat_x3f(v_v_665_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9___boxed(lean_object* v_sz_682_, lean_object* v_i_683_, lean_object* v_bs_684_){
_start:
{
size_t v_sz_boxed_685_; size_t v_i_boxed_686_; lean_object* v_res_687_; 
v_sz_boxed_685_ = lean_unbox_usize(v_sz_682_);
lean_dec(v_sz_682_);
v_i_boxed_686_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(v_sz_boxed_685_, v_i_boxed_686_, v_bs_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7(lean_object* v_x_688_){
_start:
{
if (lean_obj_tag(v_x_688_) == 4)
{
lean_object* v_elems_689_; size_t v_sz_690_; size_t v___x_691_; lean_object* v___x_692_; 
v_elems_689_ = lean_ctor_get(v_x_688_, 0);
lean_inc_ref(v_elems_689_);
lean_dec_ref_known(v_x_688_, 1);
v_sz_690_ = lean_array_size(v_elems_689_);
v___x_691_ = ((size_t)0ULL);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(v_sz_690_, v___x_691_, v_elems_689_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_693_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_694_ = lean_unsigned_to_nat(80u);
v___x_695_ = l_Lean_Json_pretty(v_x_688_, v___x_694_);
v___x_696_ = lean_string_append(v___x_693_, v___x_695_);
lean_dec_ref(v___x_695_);
v___x_697_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_698_ = lean_string_append(v___x_696_, v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(lean_object* v_j_700_, lean_object* v_k_701_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = l_Lean_Json_getObjValD(v_j_700_, v_k_701_);
v___x_703_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5___boxed(lean_object* v_j_704_, lean_object* v_k_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_j_704_, v_k_705_);
lean_dec_ref(v_k_705_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(size_t v_sz_707_, size_t v_i_708_, lean_object* v_bs_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = lean_usize_dec_lt(v_i_708_, v_sz_707_);
if (v___x_710_ == 0)
{
return v_bs_709_;
}
else
{
lean_object* v_v_711_; lean_object* v___x_712_; lean_object* v_bs_x27_713_; lean_object* v___x_714_; lean_object* v___x_715_; size_t v___x_716_; size_t v___x_717_; lean_object* v___x_718_; 
v_v_711_ = lean_array_uget(v_bs_709_, v_i_708_);
v___x_712_ = lean_unsigned_to_nat(0u);
v_bs_x27_713_ = lean_array_uset(v_bs_709_, v_i_708_, v___x_712_);
v___x_714_ = l_Lean_JsonNumber_fromNat(v_v_711_);
v___x_715_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
v___x_716_ = ((size_t)1ULL);
v___x_717_ = lean_usize_add(v_i_708_, v___x_716_);
v___x_718_ = lean_array_uset(v_bs_x27_713_, v_i_708_, v___x_715_);
v_i_708_ = v___x_717_;
v_bs_709_ = v___x_718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13___boxed(lean_object* v_sz_720_, lean_object* v_i_721_, lean_object* v_bs_722_){
_start:
{
size_t v_sz_boxed_723_; size_t v_i_boxed_724_; lean_object* v_res_725_; 
v_sz_boxed_723_ = lean_unbox_usize(v_sz_720_);
lean_dec(v_sz_720_);
v_i_boxed_724_ = lean_unbox_usize(v_i_721_);
lean_dec(v_i_721_);
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(v_sz_boxed_723_, v_i_boxed_724_, v_bs_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(lean_object* v_a_726_){
_start:
{
size_t v_sz_727_; size_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_sz_727_ = lean_array_size(v_a_726_);
v___x_728_ = ((size_t)0ULL);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(v_sz_727_, v___x_728_, v_a_726_);
v___x_730_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(lean_object* v_a_731_, lean_object* v_x_732_){
_start:
{
if (lean_obj_tag(v_x_732_) == 0)
{
uint8_t v___x_733_; 
v___x_733_ = 0;
return v___x_733_;
}
else
{
lean_object* v_key_734_; lean_object* v_tail_735_; uint8_t v___x_736_; 
v_key_734_ = lean_ctor_get(v_x_732_, 0);
v_tail_735_ = lean_ctor_get(v_x_732_, 2);
v___x_736_ = lean_nat_dec_eq(v_key_734_, v_a_731_);
if (v___x_736_ == 0)
{
v_x_732_ = v_tail_735_;
goto _start;
}
else
{
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg___boxed(lean_object* v_a_738_, lean_object* v_x_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_738_, v_x_739_);
lean_dec(v_x_739_);
lean_dec(v_a_738_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(lean_object* v_m_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_buckets_744_; lean_object* v___x_745_; uint64_t v___x_746_; uint64_t v___x_747_; uint64_t v___x_748_; uint64_t v_fold_749_; uint64_t v___x_750_; uint64_t v___x_751_; uint64_t v___x_752_; size_t v___x_753_; size_t v___x_754_; size_t v___x_755_; size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_buckets_744_ = lean_ctor_get(v_m_742_, 1);
v___x_745_ = lean_array_get_size(v_buckets_744_);
v___x_746_ = lean_uint64_of_nat(v_a_743_);
v___x_747_ = 32ULL;
v___x_748_ = lean_uint64_shift_right(v___x_746_, v___x_747_);
v_fold_749_ = lean_uint64_xor(v___x_746_, v___x_748_);
v___x_750_ = 16ULL;
v___x_751_ = lean_uint64_shift_right(v_fold_749_, v___x_750_);
v___x_752_ = lean_uint64_xor(v_fold_749_, v___x_751_);
v___x_753_ = lean_uint64_to_usize(v___x_752_);
v___x_754_ = lean_usize_of_nat(v___x_745_);
v___x_755_ = ((size_t)1ULL);
v___x_756_ = lean_usize_sub(v___x_754_, v___x_755_);
v___x_757_ = lean_usize_land(v___x_753_, v___x_756_);
v___x_758_ = lean_array_uget_borrowed(v_buckets_744_, v___x_757_);
v___x_759_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_743_, v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg___boxed(lean_object* v_m_760_, lean_object* v_a_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_m_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_m_760_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
if (lean_obj_tag(v_x_765_) == 0)
{
return v_x_764_;
}
else
{
lean_object* v_key_766_; lean_object* v_value_767_; lean_object* v_tail_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_791_; 
v_key_766_ = lean_ctor_get(v_x_765_, 0);
v_value_767_ = lean_ctor_get(v_x_765_, 1);
v_tail_768_ = lean_ctor_get(v_x_765_, 2);
v_isSharedCheck_791_ = !lean_is_exclusive(v_x_765_);
if (v_isSharedCheck_791_ == 0)
{
v___x_770_ = v_x_765_;
v_isShared_771_ = v_isSharedCheck_791_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_tail_768_);
lean_inc(v_value_767_);
lean_inc(v_key_766_);
lean_dec(v_x_765_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_791_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; uint64_t v___x_773_; uint64_t v___x_774_; uint64_t v___x_775_; uint64_t v_fold_776_; uint64_t v___x_777_; uint64_t v___x_778_; uint64_t v___x_779_; size_t v___x_780_; size_t v___x_781_; size_t v___x_782_; size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_772_ = lean_array_get_size(v_x_764_);
v___x_773_ = lean_uint64_of_nat(v_key_766_);
v___x_774_ = 32ULL;
v___x_775_ = lean_uint64_shift_right(v___x_773_, v___x_774_);
v_fold_776_ = lean_uint64_xor(v___x_773_, v___x_775_);
v___x_777_ = 16ULL;
v___x_778_ = lean_uint64_shift_right(v_fold_776_, v___x_777_);
v___x_779_ = lean_uint64_xor(v_fold_776_, v___x_778_);
v___x_780_ = lean_uint64_to_usize(v___x_779_);
v___x_781_ = lean_usize_of_nat(v___x_772_);
v___x_782_ = ((size_t)1ULL);
v___x_783_ = lean_usize_sub(v___x_781_, v___x_782_);
v___x_784_ = lean_usize_land(v___x_780_, v___x_783_);
v___x_785_ = lean_array_uget_borrowed(v_x_764_, v___x_784_);
lean_inc(v___x_785_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 2, v___x_785_);
v___x_787_ = v___x_770_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_key_766_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_value_767_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v___x_785_);
v___x_787_ = v_reuseFailAlloc_790_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; 
v___x_788_ = lean_array_uset(v_x_764_, v___x_784_, v___x_787_);
v_x_764_ = v___x_788_;
v_x_765_ = v_tail_768_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(lean_object* v_i_792_, lean_object* v_source_793_, lean_object* v_target_794_){
_start:
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = lean_array_get_size(v_source_793_);
v___x_796_ = lean_nat_dec_lt(v_i_792_, v___x_795_);
if (v___x_796_ == 0)
{
lean_dec_ref(v_source_793_);
lean_dec(v_i_792_);
return v_target_794_;
}
else
{
lean_object* v_es_797_; lean_object* v___x_798_; lean_object* v_source_799_; lean_object* v_target_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_es_797_ = lean_array_fget(v_source_793_, v_i_792_);
v___x_798_ = lean_box(0);
v_source_799_ = lean_array_fset(v_source_793_, v_i_792_, v___x_798_);
v_target_800_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(v_target_794_, v_es_797_);
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_i_792_, v___x_801_);
lean_dec(v_i_792_);
v_i_792_ = v___x_802_;
v_source_793_ = v_source_799_;
v_target_794_ = v_target_800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(lean_object* v_data_804_){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v_nbuckets_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_805_ = lean_array_get_size(v_data_804_);
v___x_806_ = lean_unsigned_to_nat(2u);
v_nbuckets_807_ = lean_nat_mul(v___x_805_, v___x_806_);
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = lean_box(0);
v___x_810_ = lean_mk_array(v_nbuckets_807_, v___x_809_);
v___x_811_ = lean_array_propagate_mark(v_data_804_, v___x_810_);
v___x_812_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(v___x_808_, v_data_804_, v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(lean_object* v_m_813_, lean_object* v_a_814_, lean_object* v_b_815_){
_start:
{
lean_object* v_size_816_; lean_object* v_buckets_817_; lean_object* v___x_818_; uint64_t v___x_819_; uint64_t v___x_820_; uint64_t v___x_821_; uint64_t v_fold_822_; uint64_t v___x_823_; uint64_t v___x_824_; uint64_t v___x_825_; size_t v___x_826_; size_t v___x_827_; size_t v___x_828_; size_t v___x_829_; size_t v___x_830_; lean_object* v_bkt_831_; uint8_t v___x_832_; 
v_size_816_ = lean_ctor_get(v_m_813_, 0);
v_buckets_817_ = lean_ctor_get(v_m_813_, 1);
v___x_818_ = lean_array_get_size(v_buckets_817_);
v___x_819_ = lean_uint64_of_nat(v_a_814_);
v___x_820_ = 32ULL;
v___x_821_ = lean_uint64_shift_right(v___x_819_, v___x_820_);
v_fold_822_ = lean_uint64_xor(v___x_819_, v___x_821_);
v___x_823_ = 16ULL;
v___x_824_ = lean_uint64_shift_right(v_fold_822_, v___x_823_);
v___x_825_ = lean_uint64_xor(v_fold_822_, v___x_824_);
v___x_826_ = lean_uint64_to_usize(v___x_825_);
v___x_827_ = lean_usize_of_nat(v___x_818_);
v___x_828_ = ((size_t)1ULL);
v___x_829_ = lean_usize_sub(v___x_827_, v___x_828_);
v___x_830_ = lean_usize_land(v___x_826_, v___x_829_);
v_bkt_831_ = lean_array_uget_borrowed(v_buckets_817_, v___x_830_);
v___x_832_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_814_, v_bkt_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_853_; 
lean_inc_ref(v_buckets_817_);
lean_inc(v_size_816_);
v_isSharedCheck_853_ = !lean_is_exclusive(v_m_813_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; lean_object* v_unused_855_; 
v_unused_854_ = lean_ctor_get(v_m_813_, 1);
lean_dec(v_unused_854_);
v_unused_855_ = lean_ctor_get(v_m_813_, 0);
lean_dec(v_unused_855_);
v___x_834_ = v_m_813_;
v_isShared_835_ = v_isSharedCheck_853_;
goto v_resetjp_833_;
}
else
{
lean_dec(v_m_813_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_853_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v_size_x27_837_; lean_object* v___x_838_; lean_object* v_buckets_x27_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_836_ = lean_unsigned_to_nat(1u);
v_size_x27_837_ = lean_nat_add(v_size_816_, v___x_836_);
lean_dec(v_size_816_);
lean_inc(v_bkt_831_);
v___x_838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_838_, 0, v_a_814_);
lean_ctor_set(v___x_838_, 1, v_b_815_);
lean_ctor_set(v___x_838_, 2, v_bkt_831_);
v_buckets_x27_839_ = lean_array_uset(v_buckets_817_, v___x_830_, v___x_838_);
v___x_840_ = lean_unsigned_to_nat(4u);
v___x_841_ = lean_nat_mul(v_size_x27_837_, v___x_840_);
v___x_842_ = lean_unsigned_to_nat(3u);
v___x_843_ = lean_nat_div(v___x_841_, v___x_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_array_get_size(v_buckets_x27_839_);
v___x_845_ = lean_nat_dec_le(v___x_843_, v___x_844_);
lean_dec(v___x_843_);
if (v___x_845_ == 0)
{
lean_object* v_val_846_; lean_object* v___x_848_; 
v_val_846_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(v_buckets_x27_839_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v_val_846_);
lean_ctor_set(v___x_834_, 0, v_size_x27_837_);
v___x_848_ = v___x_834_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_size_x27_837_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_val_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
else
{
lean_object* v___x_851_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v_buckets_x27_839_);
lean_ctor_set(v___x_834_, 0, v_size_x27_837_);
v___x_851_ = v___x_834_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_size_x27_837_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_buckets_x27_839_);
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
else
{
lean_dec(v_b_815_);
lean_dec(v_a_814_);
return v_m_813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_as_859_, size_t v_sz_860_, size_t v_i_861_, lean_object* v_b_862_){
_start:
{
lean_object* v_a_865_; uint8_t v___x_869_; 
v___x_869_ = lean_usize_dec_lt(v_i_861_, v_sz_860_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v_b_862_);
return v___x_870_;
}
else
{
lean_object* v_snd_871_; lean_object* v_snd_872_; lean_object* v_snd_873_; lean_object* v_fst_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_958_; 
v_snd_871_ = lean_ctor_get(v_b_862_, 1);
lean_inc(v_snd_871_);
v_snd_872_ = lean_ctor_get(v_snd_871_, 1);
lean_inc(v_snd_872_);
v_snd_873_ = lean_ctor_get(v_snd_872_, 1);
lean_inc(v_snd_873_);
v_fst_874_ = lean_ctor_get(v_b_862_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v_b_862_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v_b_862_, 1);
lean_dec(v_unused_959_);
v___x_876_ = v_b_862_;
v_isShared_877_ = v_isSharedCheck_958_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_fst_874_);
lean_dec(v_b_862_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_958_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_fst_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_956_; 
v_fst_878_ = lean_ctor_get(v_snd_871_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_snd_871_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v_snd_871_, 1);
lean_dec(v_unused_957_);
v___x_880_ = v_snd_871_;
v_isShared_881_ = v_isSharedCheck_956_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_fst_878_);
lean_dec(v_snd_871_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_956_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_fst_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_954_; 
v_fst_882_ = lean_ctor_get(v_snd_872_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_snd_872_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; 
v_unused_955_ = lean_ctor_get(v_snd_872_, 1);
lean_dec(v_unused_955_);
v___x_884_ = v_snd_872_;
v_isShared_885_ = v_isSharedCheck_954_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_fst_882_);
lean_dec(v_snd_872_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_954_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_array_886_; lean_object* v_start_887_; lean_object* v_stop_888_; uint8_t v___x_889_; 
v_array_886_ = lean_ctor_get(v_snd_873_, 0);
v_start_887_ = lean_ctor_get(v_snd_873_, 1);
v_stop_888_ = lean_ctor_get(v_snd_873_, 2);
v___x_889_ = lean_nat_dec_lt(v_start_887_, v_stop_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_891_; 
if (v_isShared_885_ == 0)
{
v___x_891_ = v___x_884_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_fst_882_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_snd_873_);
v___x_891_ = v_reuseFailAlloc_899_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_893_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_891_);
v___x_893_ = v___x_880_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_fst_878_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_891_);
v___x_893_ = v_reuseFailAlloc_898_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___x_893_);
v___x_895_ = v___x_876_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_fst_874_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___x_893_);
v___x_895_ = v_reuseFailAlloc_897_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
}
}
else
{
lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_950_; 
lean_inc(v_stop_888_);
lean_inc(v_start_887_);
lean_inc_ref(v_array_886_);
v_isSharedCheck_950_ = !lean_is_exclusive(v_snd_873_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; lean_object* v_unused_952_; lean_object* v_unused_953_; 
v_unused_951_ = lean_ctor_get(v_snd_873_, 2);
lean_dec(v_unused_951_);
v_unused_952_ = lean_ctor_get(v_snd_873_, 1);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_snd_873_, 0);
lean_dec(v_unused_953_);
v___x_901_ = v_snd_873_;
v_isShared_902_ = v_isSharedCheck_950_;
goto v_resetjp_900_;
}
else
{
lean_dec(v_snd_873_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_950_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v_a_903_ = lean_array_uget_borrowed(v_as_859_, v_i_861_);
v___x_904_ = lean_array_fget(v_array_886_, v_start_887_);
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_add(v_start_887_, v___x_905_);
lean_dec(v_start_887_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v___x_906_);
v___x_908_ = v___x_901_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_array_886_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_stop_888_);
v___x_908_ = v_reuseFailAlloc_949_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
uint8_t v___x_919_; 
v___x_919_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_fst_874_, v_a_903_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Json_getNat_x3f(v___x_904_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_dec_ref_known(v___x_920_, 1);
goto v___jp_909_;
}
else
{
lean_object* v_a_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = lean_array_get_size(v_a_856_);
v___x_923_ = lean_nat_dec_lt(v_a_903_, v___x_922_);
if (v___x_923_ == 0)
{
lean_dec(v_a_921_);
goto v___jp_909_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_array_fget_borrowed(v_a_856_, v_a_903_);
lean_inc(v___x_924_);
v___x_925_ = l_Lean_Json_getNat_x3f(v___x_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_dec_ref_known(v___x_925_, 1);
lean_dec(v_a_921_);
goto v___jp_909_;
}
else
{
lean_object* v_a_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = lean_array_get_size(v_a_857_);
v___x_928_ = lean_nat_dec_lt(v_a_926_, v___x_927_);
if (v___x_928_ == 0)
{
lean_dec(v_a_926_);
lean_dec(v_a_921_);
goto v___jp_909_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_array_fget_borrowed(v_a_857_, v_a_926_);
lean_dec(v_a_926_);
lean_inc(v___x_929_);
v___x_930_ = l_Lean_Json_getNat_x3f(v___x_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_dec_ref_known(v___x_930_, 1);
lean_dec(v_a_921_);
goto v___jp_909_;
}
else
{
lean_object* v_a_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v___x_930_, 1);
v___x_932_ = lean_array_get_size(v_a_858_);
v___x_933_ = lean_nat_dec_lt(v_a_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_dec(v_a_931_);
lean_dec(v_a_921_);
goto v___jp_909_;
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_del_object(v___x_884_);
lean_del_object(v___x_880_);
lean_del_object(v___x_876_);
v___x_934_ = lean_box(0);
lean_inc_n(v_a_903_, 2);
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(v_fst_874_, v_a_903_, v___x_934_);
v___x_936_ = lean_unsigned_to_nat(2u);
v___x_937_ = lean_mk_empty_array_with_capacity(v___x_936_);
v___x_938_ = lean_array_push(v___x_937_, v_a_931_);
v___x_939_ = lean_array_push(v___x_938_, v_a_921_);
v___x_940_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(v___x_939_);
v___x_941_ = lean_array_push(v_fst_878_, v___x_940_);
v___x_942_ = lean_array_push(v_fst_882_, v_a_903_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_908_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_941_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_935_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v_a_865_ = v___x_945_;
goto v___jp_864_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec(v___x_904_);
lean_del_object(v___x_884_);
lean_del_object(v___x_880_);
lean_del_object(v___x_876_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_fst_882_);
lean_ctor_set(v___x_946_, 1, v___x_908_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v_fst_878_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v_fst_874_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v_a_865_ = v___x_948_;
goto v___jp_864_;
}
v___jp_909_:
{
lean_object* v___x_911_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v___x_908_);
v___x_911_ = v___x_884_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_fst_882_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v___x_908_);
v___x_911_ = v_reuseFailAlloc_918_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_913_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_911_);
v___x_913_ = v___x_880_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_fst_878_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v___x_911_);
v___x_913_ = v_reuseFailAlloc_917_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_915_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___x_913_);
v___x_915_ = v___x_876_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_fst_874_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
v_a_865_ = v___x_915_;
goto v___jp_864_;
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
v___jp_864_:
{
size_t v___x_866_; size_t v___x_867_; 
v___x_866_ = ((size_t)1ULL);
v___x_867_ = lean_usize_add(v_i_861_, v___x_866_);
v_i_861_ = v___x_867_;
v_b_862_ = v_a_865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9___boxed(lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_as_963_, lean_object* v_sz_964_, lean_object* v_i_965_, lean_object* v_b_966_, lean_object* v___y_967_){
_start:
{
size_t v_sz_boxed_968_; size_t v_i_boxed_969_; lean_object* v_res_970_; 
v_sz_boxed_968_ = lean_unbox_usize(v_sz_964_);
lean_dec(v_sz_964_);
v_i_boxed_969_ = lean_unbox_usize(v_i_965_);
lean_dec(v_i_965_);
v_res_970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(v_a_960_, v_a_961_, v_a_962_, v_as_963_, v_sz_boxed_968_, v_i_boxed_969_, v_b_966_);
lean_dec_ref(v_as_963_);
lean_dec_ref(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec_ref(v_a_960_);
return v_res_970_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_box(0);
v___x_981_ = lean_unsigned_to_nat(16u);
v___x_982_ = lean_mk_array(v___x_981_, v___x_980_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8);
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(lean_object* v_a_986_, lean_object* v_as_987_, size_t v_sz_988_, size_t v_i_989_, lean_object* v_b_990_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = lean_usize_dec_lt(v_i_989_, v_sz_988_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v_b_990_);
return v___x_993_;
}
else
{
lean_object* v_fst_994_; lean_object* v_snd_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1124_; 
v_fst_994_ = lean_ctor_get(v_b_990_, 0);
v_snd_995_ = lean_ctor_get(v_b_990_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_b_990_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_997_ = v_b_990_;
v_isShared_998_ = v_isSharedCheck_1124_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_snd_995_);
lean_inc(v_fst_994_);
lean_dec(v_b_990_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1124_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__0));
v_a_1001_ = lean_array_uget_borrowed(v_as_987_, v_i_989_);
v___x_1002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__1));
lean_inc(v_a_1001_);
v___x_1003_ = l_Lean_Json_getObjVal_x3f(v_a_1001_, v___x_1002_);
v___x_1004_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2));
lean_inc(v_a_1001_);
v___x_1007_ = l_Lean_Json_getObjVal_x3f(v_a_1001_, v___x_1006_);
v___x_1008_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__3));
lean_inc(v_a_1001_);
v___x_1011_ = l_Lean_Json_getObjVal_x3f(v_a_1001_, v___x_1010_);
v___x_1012_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1011_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__4));
lean_inc(v_a_1005_);
v___x_1015_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_a_1005_, v___x_1014_);
v___x_1016_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1015_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__5));
v___x_1019_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_1005_, v___x_1018_);
v___x_1020_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1019_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__6));
v___x_1023_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_1009_, v___x_1022_);
v___x_1024_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1023_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__7));
v___x_1027_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_1013_, v___x_1026_);
v___x_1028_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1027_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v___x_1030_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9);
v___x_1031_ = lean_array_get_size(v_a_1021_);
v___x_1032_ = l_Array_toSubarray___redArg(v_a_1021_, v___x_999_, v___x_1031_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_1032_);
lean_ctor_set(v___x_997_, 0, v___x_1000_);
v___x_1034_ = v___x_997_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; size_t v_sz_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1000_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1030_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v_sz_1037_ = lean_array_size(v_a_1017_);
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(v_a_1025_, v_a_1029_, v_a_986_, v_a_1017_, v_sz_1037_, v___x_1038_, v___x_1036_);
lean_dec(v_a_1017_);
lean_dec(v_a_1029_);
lean_dec(v_a_1025_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v_snd_1041_; lean_object* v_snd_1042_; lean_object* v_fst_1043_; lean_object* v_fst_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1057_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v_snd_1041_ = lean_ctor_get(v_a_1040_, 1);
lean_inc(v_snd_1041_);
lean_dec(v_a_1040_);
v_snd_1042_ = lean_ctor_get(v_snd_1041_, 1);
lean_inc(v_snd_1042_);
v_fst_1043_ = lean_ctor_get(v_snd_1041_, 0);
lean_inc(v_fst_1043_);
lean_dec(v_snd_1041_);
v_fst_1044_ = lean_ctor_get(v_snd_1042_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_snd_1042_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v_snd_1042_, 1);
lean_dec(v_unused_1058_);
v___x_1046_ = v_snd_1042_;
v_isShared_1047_ = v_isSharedCheck_1057_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_fst_1044_);
lean_dec(v_snd_1042_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1057_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1048_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_fst_1043_);
v___x_1049_ = lean_array_push(v_fst_994_, v___x_1048_);
v___x_1050_ = lean_array_push(v_snd_995_, v_fst_1044_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v___x_1050_);
lean_ctor_set(v___x_1046_, 0, v___x_1049_);
v___x_1052_ = v___x_1046_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
size_t v___x_1053_; size_t v___x_1054_; 
v___x_1053_ = ((size_t)1ULL);
v___x_1054_ = lean_usize_add(v_i_989_, v___x_1053_);
v_i_989_ = v___x_1054_;
v_b_990_ = v___x_1052_;
goto _start;
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v_snd_995_);
lean_dec(v_fst_994_);
v_a_1059_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1039_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1039_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_a_1025_);
lean_dec(v_a_1021_);
lean_dec(v_a_1017_);
lean_del_object(v___x_997_);
lean_dec(v_snd_995_);
lean_dec(v_fst_994_);
v_a_1068_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1028_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1028_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v_a_1021_);
lean_dec(v_a_1017_);
lean_dec(v_a_1013_);
lean_del_object(v___x_997_);
lean_dec(v_snd_995_);
lean_dec(v_fst_994_);
v_a_1076_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1024_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1024_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_a_1017_);
lean_dec(v_a_1013_);
lean_dec(v_a_1009_);
lean_del_object(v___x_997_);
lean_dec(v_snd_995_);
lean_dec(v_fst_994_);
v_a_1084_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1020_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1020_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
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
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_a_1013_);
lean_dec(v_a_1009_);
lean_dec(v_a_1005_);
lean_del_object(v___x_997_);
lean_dec(v_snd_995_);
lean_dec(v_fst_994_);
v_a_1092_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1016_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1016_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
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
lean_dec(v_a_1009_);
lean_dec(v_a_1005_);
lean_del_object(v___x_997_);
lean_dec(v_snd_995_);
lean_dec(v_fst_994_);
v_a_1100_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1012_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1012_);
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
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_a_1005_);
lean_del_object(v___x_997_);
lean_dec(v_snd_995_);
lean_dec(v_fst_994_);
v_a_1108_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1008_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1008_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_del_object(v___x_997_);
lean_dec(v_snd_995_);
lean_dec(v_fst_994_);
v_a_1116_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1004_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1004_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___boxed(lean_object* v_a_1125_, lean_object* v_as_1126_, lean_object* v_sz_1127_, lean_object* v_i_1128_, lean_object* v_b_1129_, lean_object* v___y_1130_){
_start:
{
size_t v_sz_boxed_1131_; size_t v_i_boxed_1132_; lean_object* v_res_1133_; 
v_sz_boxed_1131_ = lean_unbox_usize(v_sz_1127_);
lean_dec(v_sz_1127_);
v_i_boxed_1132_ = lean_unbox_usize(v_i_1128_);
lean_dec(v_i_1128_);
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(v_a_1125_, v_as_1126_, v_sz_boxed_1131_, v_i_boxed_1132_, v_b_1129_);
lean_dec_ref(v_as_1126_);
lean_dec_ref(v_a_1125_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(size_t v_sz_1134_, size_t v_i_1135_, lean_object* v_bs_1136_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_usize_dec_lt(v_i_1135_, v_sz_1134_);
if (v___x_1137_ == 0)
{
return v_bs_1136_;
}
else
{
lean_object* v_v_1138_; lean_object* v___x_1139_; lean_object* v_bs_x27_1140_; lean_object* v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; lean_object* v___x_1144_; 
v_v_1138_ = lean_array_uget(v_bs_1136_, v_i_1135_);
v___x_1139_ = lean_unsigned_to_nat(0u);
v_bs_x27_1140_ = lean_array_uset(v_bs_1136_, v_i_1135_, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_v_1138_);
v___x_1142_ = ((size_t)1ULL);
v___x_1143_ = lean_usize_add(v_i_1135_, v___x_1142_);
v___x_1144_ = lean_array_uset(v_bs_x27_1140_, v_i_1135_, v___x_1141_);
v_i_1135_ = v___x_1143_;
v_bs_1136_ = v___x_1144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2___boxed(lean_object* v_sz_1146_, lean_object* v_i_1147_, lean_object* v_bs_1148_){
_start:
{
size_t v_sz_boxed_1149_; size_t v_i_boxed_1150_; lean_object* v_res_1151_; 
v_sz_boxed_1149_ = lean_unbox_usize(v_sz_1146_);
lean_dec(v_sz_1146_);
v_i_boxed_1150_ = lean_unbox_usize(v_i_1147_);
lean_dec(v_i_1147_);
v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(v_sz_boxed_1149_, v_i_boxed_1150_, v_bs_1148_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(lean_object* v_a_1152_){
_start:
{
size_t v_sz_1153_; size_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_sz_1153_ = lean_array_size(v_a_1152_);
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(v_sz_1153_, v___x_1154_, v_a_1152_);
v___x_1156_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(size_t v_sz_1159_, size_t v_i_1160_, lean_object* v_bs_1161_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_lt(v_i_1160_, v_sz_1159_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_bs_1161_);
return v___x_1164_;
}
else
{
lean_object* v_v_1165_; lean_object* v___x_1166_; lean_object* v_bs_x27_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_v_1165_ = lean_array_uget(v_bs_1161_, v_i_1160_);
v___x_1166_ = lean_unsigned_to_nat(0u);
v_bs_x27_1167_ = lean_array_uset(v_bs_1161_, v_i_1160_, v___x_1166_);
v___x_1168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__0));
lean_inc(v_v_1165_);
v___x_1169_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_v_1165_, v___x_1168_);
v___x_1170_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1169_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__1));
v___x_1173_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_v_1165_, v___x_1172_);
v___x_1174_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1173_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; lean_object* v___x_1183_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = lean_unsigned_to_nat(2u);
v___x_1177_ = lean_mk_empty_array_with_capacity(v___x_1176_);
v___x_1178_ = lean_array_push(v___x_1177_, v_a_1171_);
v___x_1179_ = lean_array_push(v___x_1178_, v_a_1175_);
v___x_1180_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(v___x_1179_);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_add(v_i_1160_, v___x_1181_);
v___x_1183_ = lean_array_uset(v_bs_x27_1167_, v_i_1160_, v___x_1180_);
v_i_1160_ = v___x_1182_;
v_bs_1161_ = v___x_1183_;
goto _start;
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_a_1171_);
lean_dec_ref(v_bs_x27_1167_);
v_a_1185_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1174_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1174_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v_bs_x27_1167_);
lean_dec(v_v_1165_);
v_a_1193_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1170_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1170_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___boxed(lean_object* v_sz_1201_, lean_object* v_i_1202_, lean_object* v_bs_1203_, lean_object* v___y_1204_){
_start:
{
size_t v_sz_boxed_1205_; size_t v_i_boxed_1206_; lean_object* v_res_1207_; 
v_sz_boxed_1205_ = lean_unbox_usize(v_sz_1201_);
lean_dec(v_sz_1201_);
v_i_boxed_1206_ = lean_unbox_usize(v_i_1202_);
lean_dec(v_i_1202_);
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(v_sz_boxed_1205_, v_i_boxed_1206_, v_bs_1203_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(lean_object* v_profile_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__0));
lean_inc(v_profile_1214_);
v___x_1217_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1214_, v___x_1216_);
v___x_1218_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1217_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; size_t v_sz_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc_n(v_a_1219_, 2);
lean_dec_ref_known(v___x_1218_, 1);
v_sz_1220_ = lean_array_size(v_a_1219_);
v___x_1221_ = ((size_t)0ULL);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(v_sz_1220_, v___x_1221_, v_a_1219_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v___x_1224_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1));
v___x_1225_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1214_, v___x_1224_);
v___x_1226_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1225_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1228_; size_t v_sz_1229_; lean_object* v___x_1230_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v___x_1228_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__2));
v_sz_1229_ = lean_array_size(v_a_1227_);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(v_a_1219_, v_a_1227_, v_sz_1229_, v___x_1221_, v___x_1228_);
lean_dec(v_a_1227_);
lean_dec(v_a_1219_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1257_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1257_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1257_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v_fst_1235_; lean_object* v_snd_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1256_; 
v_fst_1235_ = lean_ctor_get(v_a_1231_, 0);
v_snd_1236_ = lean_ctor_get(v_a_1231_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_a_1231_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1238_ = v_a_1231_;
v_isShared_1239_ = v_isSharedCheck_1256_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_snd_1236_);
lean_inc(v_fst_1235_);
lean_dec(v_a_1231_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1256_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1240_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__3));
v___x_1241_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_a_1223_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v___x_1241_);
lean_ctor_set(v___x_1238_, 0, v___x_1240_);
v___x_1243_ = v___x_1238_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1244_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4));
v___x_1245_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_fst_1235_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1243_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = l_Lean_Json_mkObj(v___x_1249_);
lean_dec_ref_known(v___x_1249_, 2);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v_snd_1236_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1251_);
v___x_1253_ = v___x_1233_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_a_1223_);
v_a_1258_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1230_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1230_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_a_1223_);
lean_dec(v_a_1219_);
v_a_1266_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1226_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1226_);
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
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec(v_a_1219_);
lean_dec(v_profile_1214_);
v_a_1274_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1222_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1222_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_profile_1214_);
v_a_1282_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1218_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1218_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___boxed(lean_object* v_profile_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(v_profile_1290_);
return v_res_1292_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(lean_object* v_00_u03b2_1293_, lean_object* v_m_1294_, lean_object* v_a_1295_){
_start:
{
uint8_t v___x_1296_; 
v___x_1296_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_m_1294_, v_a_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___boxed(lean_object* v_00_u03b2_1297_, lean_object* v_m_1298_, lean_object* v_a_1299_){
_start:
{
uint8_t v_res_1300_; lean_object* v_r_1301_; 
v_res_1300_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(v_00_u03b2_1297_, v_m_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_m_1298_);
v_r_1301_ = lean_box(v_res_1300_);
return v_r_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7(lean_object* v_00_u03b2_1302_, lean_object* v_m_1303_, lean_object* v_a_1304_, lean_object* v_b_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(v_m_1303_, v_a_1304_, v_b_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(lean_object* v_00_u03b2_1307_, lean_object* v_a_1308_, lean_object* v_x_1309_){
_start:
{
uint8_t v___x_1310_; 
v___x_1310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_1308_, v_x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1311_, lean_object* v_a_1312_, lean_object* v_x_1313_){
_start:
{
uint8_t v_res_1314_; lean_object* v_r_1315_; 
v_res_1314_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(v_00_u03b2_1311_, v_a_1312_, v_x_1313_);
lean_dec(v_x_1313_);
lean_dec(v_a_1312_);
v_r_1315_ = lean_box(v_res_1314_);
return v_r_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11(lean_object* v_00_u03b2_1316_, lean_object* v_data_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(v_data_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14(lean_object* v_00_u03b2_1319_, lean_object* v_i_1320_, lean_object* v_source_1321_, lean_object* v_target_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(v_i_1320_, v_source_1321_, v_target_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18(lean_object* v_00_u03b2_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(v_x_1325_, v_x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(size_t v_sz_1328_, size_t v_i_1329_, lean_object* v_bs_1330_){
_start:
{
uint8_t v___x_1331_; 
v___x_1331_ = lean_usize_dec_lt(v_i_1329_, v_sz_1328_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_bs_1330_);
return v___x_1332_;
}
else
{
lean_object* v_v_1333_; lean_object* v___x_1334_; 
v_v_1333_ = lean_array_uget_borrowed(v_bs_1330_, v_i_1329_);
lean_inc(v_v_1333_);
v___x_1334_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(v_v_1333_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_bs_1330_);
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1344_; lean_object* v_bs_x27_1345_; size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v_a_1343_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1334_, 1);
v___x_1344_ = lean_unsigned_to_nat(0u);
v_bs_x27_1345_ = lean_array_uset(v_bs_1330_, v_i_1329_, v___x_1344_);
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_add(v_i_1329_, v___x_1346_);
v___x_1348_ = lean_array_uset(v_bs_x27_1345_, v_i_1329_, v_a_1343_);
v_i_1329_ = v___x_1347_;
v_bs_1330_ = v___x_1348_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1350_, lean_object* v_i_1351_, lean_object* v_bs_1352_){
_start:
{
size_t v_sz_boxed_1353_; size_t v_i_boxed_1354_; lean_object* v_res_1355_; 
v_sz_boxed_1353_ = lean_unbox_usize(v_sz_1350_);
lean_dec(v_sz_1350_);
v_i_boxed_1354_ = lean_unbox_usize(v_i_1351_);
lean_dec(v_i_1351_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(v_sz_boxed_1353_, v_i_boxed_1354_, v_bs_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0(lean_object* v_x_1356_){
_start:
{
if (lean_obj_tag(v_x_1356_) == 4)
{
lean_object* v_elems_1357_; size_t v_sz_1358_; size_t v___x_1359_; lean_object* v___x_1360_; 
v_elems_1357_ = lean_ctor_get(v_x_1356_, 0);
lean_inc_ref(v_elems_1357_);
lean_dec_ref_known(v_x_1356_, 1);
v_sz_1358_ = lean_array_size(v_elems_1357_);
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(v_sz_1358_, v___x_1359_, v_elems_1357_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1361_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_1362_ = lean_unsigned_to_nat(80u);
v___x_1363_ = l_Lean_Json_pretty(v_x_1356_, v___x_1362_);
v___x_1364_ = lean_string_append(v___x_1361_, v___x_1363_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_1366_ = lean_string_append(v___x_1364_, v___x_1365_);
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(lean_object* v_j_1368_, lean_object* v_k_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = l_Lean_Json_getObjValD(v_j_1368_, v_k_1369_);
v___x_1371_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0(v___x_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0___boxed(lean_object* v_j_1372_, lean_object* v_k_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(v_j_1372_, v_k_1373_);
lean_dec_ref(v_k_1373_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(size_t v_sz_1375_, size_t v_i_1376_, lean_object* v_bs_1377_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_usize_dec_lt(v_i_1376_, v_sz_1375_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_bs_1377_);
return v___x_1379_;
}
else
{
lean_object* v_v_1380_; lean_object* v___x_1381_; 
v_v_1380_ = lean_array_uget_borrowed(v_bs_1377_, v_i_1376_);
lean_inc(v_v_1380_);
v___x_1381_ = l_Lean_Json_getStr_x3f(v_v_1380_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v_bs_1377_);
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1391_; lean_object* v_bs_x27_1392_; size_t v___x_1393_; size_t v___x_1394_; lean_object* v___x_1395_; 
v_a_1390_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1391_ = lean_unsigned_to_nat(0u);
v_bs_x27_1392_ = lean_array_uset(v_bs_1377_, v_i_1376_, v___x_1391_);
v___x_1393_ = ((size_t)1ULL);
v___x_1394_ = lean_usize_add(v_i_1376_, v___x_1393_);
v___x_1395_ = lean_array_uset(v_bs_x27_1392_, v_i_1376_, v_a_1390_);
v_i_1376_ = v___x_1394_;
v_bs_1377_ = v___x_1395_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_1397_, lean_object* v_i_1398_, lean_object* v_bs_1399_){
_start:
{
size_t v_sz_boxed_1400_; size_t v_i_boxed_1401_; lean_object* v_res_1402_; 
v_sz_boxed_1400_ = lean_unbox_usize(v_sz_1397_);
lean_dec(v_sz_1397_);
v_i_boxed_1401_ = lean_unbox_usize(v_i_1398_);
lean_dec(v_i_1398_);
v_res_1402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(v_sz_boxed_1400_, v_i_boxed_1401_, v_bs_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2(lean_object* v_x_1403_){
_start:
{
if (lean_obj_tag(v_x_1403_) == 4)
{
lean_object* v_elems_1404_; size_t v_sz_1405_; size_t v___x_1406_; lean_object* v___x_1407_; 
v_elems_1404_ = lean_ctor_get(v_x_1403_, 0);
lean_inc_ref(v_elems_1404_);
lean_dec_ref_known(v_x_1403_, 1);
v_sz_1405_ = lean_array_size(v_elems_1404_);
v___x_1406_ = ((size_t)0ULL);
v___x_1407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(v_sz_1405_, v___x_1406_, v_elems_1404_);
return v___x_1407_;
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1408_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_1409_ = lean_unsigned_to_nat(80u);
v___x_1410_ = l_Lean_Json_pretty(v_x_1403_, v___x_1409_);
v___x_1411_ = lean_string_append(v___x_1408_, v___x_1410_);
lean_dec_ref(v___x_1410_);
v___x_1412_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_1413_ = lean_string_append(v___x_1411_, v___x_1412_);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(lean_object* v_j_1415_, lean_object* v_k_1416_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = l_Lean_Json_getObjValD(v_j_1415_, v_k_1416_);
v___x_1418_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2(v___x_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1___boxed(lean_object* v_j_1419_, lean_object* v_k_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(v_j_1419_, v_k_1420_);
lean_dec_ref(v_k_1420_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(lean_object* v_as_1423_, size_t v_sz_1424_, size_t v_i_1425_, lean_object* v_b_1426_){
_start:
{
lean_object* v_a_1429_; uint8_t v___x_1433_; 
v___x_1433_ = lean_usize_dec_lt(v_i_1425_, v_sz_1424_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v_b_1426_);
return v___x_1434_;
}
else
{
lean_object* v_snd_1435_; lean_object* v_snd_1436_; lean_object* v_fst_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1497_; 
v_snd_1435_ = lean_ctor_get(v_b_1426_, 1);
lean_inc(v_snd_1435_);
v_snd_1436_ = lean_ctor_get(v_snd_1435_, 1);
lean_inc(v_snd_1436_);
v_fst_1437_ = lean_ctor_get(v_b_1426_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_b_1426_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v_b_1426_, 1);
lean_dec(v_unused_1498_);
v___x_1439_ = v_b_1426_;
v_isShared_1440_ = v_isSharedCheck_1497_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_fst_1437_);
lean_dec(v_b_1426_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1497_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_fst_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1495_; 
v_fst_1441_ = lean_ctor_get(v_snd_1435_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_snd_1435_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; 
v_unused_1496_ = lean_ctor_get(v_snd_1435_, 1);
lean_dec(v_unused_1496_);
v___x_1443_ = v_snd_1435_;
v_isShared_1444_ = v_isSharedCheck_1495_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_fst_1441_);
lean_dec(v_snd_1435_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1495_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v_array_1445_; lean_object* v_start_1446_; lean_object* v_stop_1447_; uint8_t v___x_1448_; 
v_array_1445_ = lean_ctor_get(v_snd_1436_, 0);
v_start_1446_ = lean_ctor_get(v_snd_1436_, 1);
v_stop_1447_ = lean_ctor_get(v_snd_1436_, 2);
v___x_1448_ = lean_nat_dec_lt(v_start_1446_, v_stop_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1450_; 
if (v_isShared_1444_ == 0)
{
v___x_1450_ = v___x_1443_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_fst_1441_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_snd_1436_);
v___x_1450_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1450_);
v___x_1452_ = v___x_1439_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_fst_1437_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
}
else
{
lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1491_; 
lean_inc(v_stop_1447_);
lean_inc(v_start_1446_);
lean_inc_ref(v_array_1445_);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_snd_1436_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; lean_object* v_unused_1493_; lean_object* v_unused_1494_; 
v_unused_1492_ = lean_ctor_get(v_snd_1436_, 2);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_snd_1436_, 1);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_snd_1436_, 0);
lean_dec(v_unused_1494_);
v___x_1457_ = v_snd_1436_;
v_isShared_1458_ = v_isSharedCheck_1491_;
goto v_resetjp_1456_;
}
else
{
lean_dec(v_snd_1436_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1491_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_a_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v_a_1459_ = lean_array_uget_borrowed(v_as_1423_, v_i_1425_);
v___x_1460_ = lean_array_fget(v_array_1445_, v_start_1446_);
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1462_ = lean_nat_add(v_start_1446_, v___x_1461_);
lean_dec(v_start_1446_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 1, v___x_1462_);
v___x_1464_ = v___x_1457_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_array_1445_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_stop_1447_);
v___x_1464_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___y_1466_; lean_object* v___y_1477_; lean_object* v___x_1487_; 
lean_inc(v___x_1460_);
v___x_1487_ = l_Lean_Json_getStr_x3f(v___x_1460_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref_known(v___x_1487_, 1);
v___x_1488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___closed__0));
v___x_1489_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v___x_1460_, v___x_1488_);
v___y_1477_ = v___x_1489_;
goto v___jp_1476_;
}
else
{
lean_dec(v___x_1460_);
v___y_1477_ = v___x_1487_;
goto v___jp_1476_;
}
v___jp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1467_ = lean_array_get_size(v_fst_1441_);
v___x_1468_ = lean_array_fset(v_fst_1437_, v_a_1459_, v___x_1467_);
v___x_1469_ = lean_array_push(v_fst_1441_, v___y_1466_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v___x_1464_);
lean_ctor_set(v___x_1443_, 0, v___x_1469_);
v___x_1471_ = v___x_1443_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v___x_1464_);
v___x_1471_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1473_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1471_);
lean_ctor_set(v___x_1439_, 0, v___x_1468_);
v___x_1473_ = v___x_1439_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
v_a_1429_ = v___x_1473_;
goto v___jp_1428_;
}
}
}
v___jp_1476_:
{
if (lean_obj_tag(v___y_1477_) == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec_ref_known(v___y_1477_, 1);
lean_del_object(v___x_1443_);
lean_del_object(v___x_1439_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_fst_1441_);
lean_ctor_set(v___x_1478_, 1, v___x_1464_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_fst_1437_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v_a_1429_ = v___x_1479_;
goto v___jp_1428_;
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v_a_1480_ = lean_ctor_get(v___y_1477_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___y_1477_, 1);
v___x_1481_ = lean_array_get_size(v_fst_1437_);
v___x_1482_ = lean_nat_dec_lt(v_a_1459_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec(v_a_1480_);
lean_del_object(v___x_1443_);
lean_del_object(v___x_1439_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_fst_1441_);
lean_ctor_set(v___x_1483_, 1, v___x_1464_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_fst_1437_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v_a_1429_ = v___x_1484_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1485_; 
lean_inc(v_a_1480_);
v___x_1485_ = l_Lean_Name_Demangle_demangleSymbol(v_a_1480_);
if (lean_obj_tag(v___x_1485_) == 0)
{
v___y_1466_ = v_a_1480_;
goto v___jp_1465_;
}
else
{
lean_object* v_val_1486_; 
lean_dec(v_a_1480_);
v_val_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v___y_1466_ = v_val_1486_;
goto v___jp_1465_;
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
v___jp_1428_:
{
size_t v___x_1430_; size_t v___x_1431_; 
v___x_1430_ = ((size_t)1ULL);
v___x_1431_ = lean_usize_add(v_i_1425_, v___x_1430_);
v_i_1425_ = v___x_1431_;
v_b_1426_ = v_a_1429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___boxed(lean_object* v_as_1499_, lean_object* v_sz_1500_, lean_object* v_i_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_){
_start:
{
size_t v_sz_boxed_1504_; size_t v_i_boxed_1505_; lean_object* v_res_1506_; 
v_sz_boxed_1504_ = lean_unbox_usize(v_sz_1500_);
lean_dec(v_sz_1500_);
v_i_boxed_1505_ = lean_unbox_usize(v_i_1501_);
lean_dec(v_i_1501_);
v_res_1506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(v_as_1499_, v_sz_boxed_1504_, v_i_boxed_1505_, v_b_1502_);
lean_dec_ref(v_as_1499_);
return v_res_1506_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Array_instInhabited___redArg();
return v___x_1507_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__1));
v___x_1510_ = lean_mk_io_user_error(v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(lean_object* v_a_1513_, lean_object* v_funcMaps_1514_, size_t v_sz_1515_, size_t v_i_1516_, lean_object* v_bs_1517_){
_start:
{
uint8_t v___x_1519_; 
v___x_1519_ = lean_usize_dec_lt(v_i_1516_, v_sz_1515_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_bs_1517_);
return v___x_1520_;
}
else
{
lean_object* v___x_1521_; lean_object* v_v_1522_; lean_object* v___x_1523_; lean_object* v_bs_x27_1524_; lean_object* v_a_1526_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1521_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0);
v_v_1522_ = lean_array_uget(v_bs_1517_, v_i_1516_);
v___x_1523_ = lean_unsigned_to_nat(0u);
v_bs_x27_1524_ = lean_array_uset(v_bs_1517_, v_i_1516_, v___x_1523_);
v___x_1531_ = lean_usize_to_nat(v_i_1516_);
v___x_1532_ = lean_array_get_borrowed(v___x_1521_, v_a_1513_, v___x_1531_);
v___x_1533_ = lean_array_get_borrowed(v___x_1521_, v_funcMaps_1514_, v___x_1531_);
lean_dec(v___x_1531_);
v___x_1534_ = lean_array_get_size(v___x_1532_);
v___x_1535_ = lean_array_get_size(v___x_1533_);
v___x_1536_ = lean_nat_dec_eq(v___x_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec_ref(v_bs_x27_1524_);
lean_dec(v_v_1522_);
v___x_1537_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2);
v___x_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2));
lean_inc(v_v_1522_);
v___x_1540_ = l_Lean_Json_getObjVal_x3f(v_v_1522_, v___x_1539_);
v___x_1541_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1540_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc_n(v_a_1542_, 2);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__3));
v___x_1544_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_a_1542_, v___x_1543_);
v___x_1545_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1544_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__4));
lean_inc(v_v_1522_);
v___x_1548_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(v_v_1522_, v___x_1547_);
v___x_1549_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1548_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; size_t v_sz_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
lean_inc(v___x_1532_);
v___x_1551_ = l_Array_toSubarray___redArg(v___x_1532_, v___x_1523_, v___x_1534_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_a_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_a_1546_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v_sz_1554_ = lean_array_size(v___x_1533_);
v___x_1555_ = ((size_t)0ULL);
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(v___x_1533_, v_sz_1554_, v___x_1555_, v___x_1553_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v_snd_1558_; lean_object* v_fst_1559_; lean_object* v_fst_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v_snd_1558_ = lean_ctor_get(v_a_1557_, 1);
lean_inc(v_snd_1558_);
v_fst_1559_ = lean_ctor_get(v_a_1557_, 0);
lean_inc(v_fst_1559_);
lean_dec(v_a_1557_);
v_fst_1560_ = lean_ctor_get(v_snd_1558_, 0);
lean_inc(v_fst_1560_);
lean_dec(v_snd_1558_);
v___x_1561_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(v_fst_1559_);
v___x_1562_ = l_Lean_Json_setObjVal_x21(v_a_1542_, v___x_1543_, v___x_1561_);
v___x_1563_ = l_Lean_Json_setObjVal_x21(v_v_1522_, v___x_1539_, v___x_1562_);
v___x_1564_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(v_fst_1560_);
v___x_1565_ = l_Lean_Json_setObjVal_x21(v___x_1563_, v___x_1547_, v___x_1564_);
v_a_1526_ = v___x_1565_;
goto v___jp_1525_;
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v_a_1542_);
lean_dec_ref(v_bs_x27_1524_);
lean_dec(v_v_1522_);
v_a_1566_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1556_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1556_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec(v_a_1546_);
lean_dec(v_a_1542_);
lean_dec_ref(v_bs_x27_1524_);
lean_dec(v_v_1522_);
v_a_1574_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1549_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1549_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_a_1542_);
lean_dec_ref(v_bs_x27_1524_);
lean_dec(v_v_1522_);
v_a_1582_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1545_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1545_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_dec(v_v_1522_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1590_; 
v_a_1590_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1541_, 1);
v_a_1526_ = v_a_1590_;
goto v___jp_1525_;
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v_bs_x27_1524_);
v_a_1591_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1541_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1541_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
v___jp_1525_:
{
size_t v___x_1527_; size_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = ((size_t)1ULL);
v___x_1528_ = lean_usize_add(v_i_1516_, v___x_1527_);
v___x_1529_ = lean_array_uset(v_bs_x27_1524_, v_i_1516_, v_a_1526_);
v_i_1516_ = v___x_1528_;
v_bs_1517_ = v___x_1529_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___boxed(lean_object* v_a_1599_, lean_object* v_funcMaps_1600_, lean_object* v_sz_1601_, lean_object* v_i_1602_, lean_object* v_bs_1603_, lean_object* v___y_1604_){
_start:
{
size_t v_sz_boxed_1605_; size_t v_i_boxed_1606_; lean_object* v_res_1607_; 
v_sz_boxed_1605_ = lean_unbox_usize(v_sz_1601_);
lean_dec(v_sz_1601_);
v_i_boxed_1606_ = lean_unbox_usize(v_i_1602_);
lean_dec(v_i_1602_);
v_res_1607_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1599_, v_funcMaps_1600_, v_sz_boxed_1605_, v_i_boxed_1606_, v_bs_1603_);
lean_dec_ref(v_funcMaps_1600_);
lean_dec_ref(v_a_1599_);
return v_res_1607_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__1));
v___x_1611_ = lean_mk_io_user_error(v___x_1610_);
return v___x_1611_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__3));
v___x_1614_ = lean_mk_io_user_error(v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(lean_object* v_profile_1617_, lean_object* v_response_1618_, lean_object* v_funcMaps_1619_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__0));
v___x_1622_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_response_1618_, v___x_1621_);
v___x_1623_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1622_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1703_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1703_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1703_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1628_ = lean_unsigned_to_nat(0u);
v___x_1629_ = lean_array_get_size(v_a_1624_);
v___x_1630_ = lean_nat_dec_lt(v___x_1628_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
lean_dec(v_a_1624_);
lean_dec(v_profile_1617_);
v___x_1631_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2, &l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2);
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 1);
lean_ctor_set(v___x_1626_, 0, v___x_1631_);
v___x_1633_ = v___x_1626_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_del_object(v___x_1626_);
v___x_1635_ = lean_array_fget(v_a_1624_, v___x_1628_);
lean_dec(v_a_1624_);
v___x_1636_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4));
v___x_1637_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(v___x_1635_, v___x_1636_);
v___x_1638_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1637_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1));
lean_inc(v_profile_1617_);
v___x_1641_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1617_, v___x_1640_);
v___x_1642_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1641_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1686_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1686_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1686_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1652_ = lean_array_get_size(v_a_1639_);
v___x_1653_ = lean_array_get_size(v_a_1643_);
v___x_1654_ = lean_nat_dec_eq(v___x_1652_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_dec(v_a_1643_);
lean_dec(v_a_1639_);
lean_dec(v_profile_1617_);
goto v___jp_1647_;
}
else
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = lean_array_get_size(v_funcMaps_1619_);
v___x_1656_ = lean_nat_dec_eq(v___x_1655_, v___x_1653_);
if (v___x_1656_ == 0)
{
lean_dec(v_a_1643_);
lean_dec(v_a_1639_);
lean_dec(v_profile_1617_);
goto v___jp_1647_;
}
else
{
size_t v_sz_1657_; size_t v___x_1658_; lean_object* v___x_1659_; 
lean_del_object(v___x_1645_);
v_sz_1657_ = lean_array_size(v_a_1643_);
v___x_1658_ = ((size_t)0ULL);
v___x_1659_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1639_, v_funcMaps_1619_, v_sz_1657_, v___x_1658_, v_a_1643_);
lean_dec(v_a_1639_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1661_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__5));
lean_inc(v_profile_1617_);
v___x_1662_ = l_Lean_Json_getObjVal_x3f(v_profile_1617_, v___x_1661_);
v___x_1663_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1662_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1677_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1677_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1677_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1668_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1668_, 0, v_a_1660_);
v___x_1669_ = l_Lean_Json_setObjVal_x21(v_profile_1617_, v___x_1640_, v___x_1668_);
v___x_1670_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__6));
v___x_1671_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1671_, 0, v___x_1656_);
v___x_1672_ = l_Lean_Json_setObjVal_x21(v_a_1664_, v___x_1670_, v___x_1671_);
v___x_1673_ = l_Lean_Json_setObjVal_x21(v___x_1669_, v___x_1661_, v___x_1672_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1673_);
v___x_1675_ = v___x_1666_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_dec(v_a_1660_);
lean_dec(v_profile_1617_);
return v___x_1663_;
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_profile_1617_);
v_a_1678_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1659_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1659_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
v___jp_1647_:
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4, &l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4);
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 1);
lean_ctor_set(v___x_1645_, 0, v___x_1648_);
v___x_1650_ = v___x_1645_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_a_1639_);
lean_dec(v_profile_1617_);
v_a_1687_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1642_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1642_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v_profile_1617_);
v_a_1695_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1638_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1638_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_profile_1617_);
v_a_1704_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1623_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1623_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___boxed(lean_object* v_profile_1712_, lean_object* v_response_1713_, lean_object* v_funcMaps_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(v_profile_1712_, v_response_1713_, v_funcMaps_1714_);
lean_dec_ref(v_funcMaps_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(lean_object* v_a_1717_, lean_object* v_funcMaps_1718_, lean_object* v_as_1719_, size_t v_sz_1720_, size_t v_i_1721_, lean_object* v_bs_1722_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1717_, v_funcMaps_1718_, v_sz_1720_, v_i_1721_, v_bs_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___boxed(lean_object* v_a_1725_, lean_object* v_funcMaps_1726_, lean_object* v_as_1727_, lean_object* v_sz_1728_, lean_object* v_i_1729_, lean_object* v_bs_1730_, lean_object* v___y_1731_){
_start:
{
size_t v_sz_boxed_1732_; size_t v_i_boxed_1733_; lean_object* v_res_1734_; 
v_sz_boxed_1732_ = lean_unbox_usize(v_sz_1728_);
lean_dec(v_sz_1728_);
v_i_boxed_1733_ = lean_unbox_usize(v_i_1729_);
lean_dec(v_i_1729_);
v_res_1734_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(v_a_1725_, v_funcMaps_1726_, v_as_1727_, v_sz_boxed_1732_, v_i_boxed_1733_, v_bs_1730_);
lean_dec_ref(v_as_1727_);
lean_dec_ref(v_funcMaps_1726_);
lean_dec_ref(v_a_1725_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(lean_object* v_cfg_1735_, lean_object* v_proc_1736_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_io_process_child_kill(v_cfg_1735_, v_proc_1736_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v___x_1742_; 
lean_dec_ref_known(v___x_1741_, 1);
v___x_1742_ = lean_io_process_child_wait(v_cfg_1735_, v_proc_1736_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1750_; 
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v___x_1742_, 0);
lean_dec(v_unused_1751_);
v___x_1744_ = v___x_1742_;
v_isShared_1745_ = v_isSharedCheck_1750_;
goto v_resetjp_1743_;
}
else
{
lean_dec(v___x_1742_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1750_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1746_ = lean_box(0);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1746_);
v___x_1748_ = v___x_1744_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
else
{
lean_dec_ref_known(v___x_1742_, 1);
goto v___jp_1738_;
}
}
else
{
if (lean_obj_tag(v___x_1741_) == 0)
{
return v___x_1741_;
}
else
{
lean_dec_ref_known(v___x_1741_, 1);
goto v___jp_1738_;
}
}
v___jp_1738_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_box(0);
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
return v___x_1740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe___boxed(lean_object* v_cfg_1752_, lean_object* v_proc_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v_cfg_1752_, v_proc_1753_);
lean_dec_ref(v_proc_1753_);
lean_dec_ref(v_cfg_1752_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(lean_object* v_as_1757_, lean_object* v_j_1758_){
_start:
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = lean_array_get_size(v_as_1757_);
v___x_1760_ = lean_nat_dec_lt(v_j_1758_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
lean_dec(v_j_1758_);
v___x_1761_ = lean_box(0);
return v___x_1761_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1762_ = lean_array_fget_borrowed(v_as_1757_, v_j_1758_);
v___x_1763_ = ((lean_object*)(l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0));
v___x_1764_ = lean_string_dec_eq(v___x_1762_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = lean_nat_add(v_j_1758_, v___x_1765_);
lean_dec(v_j_1758_);
v_j_1758_ = v___x_1766_;
goto _start;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_j_1758_);
return v___x_1768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___boxed(lean_object* v_as_1769_, lean_object* v_j_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(v_as_1769_, v_j_1770_);
lean_dec_ref(v_as_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash(lean_object* v_args_1774_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(v_args_1774_, v___x_1775_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash___closed__0));
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v_args_1774_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
return v___x_1778_;
}
else
{
lean_object* v_val_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_val_1779_ = lean_ctor_get(v___x_1776_, 0);
lean_inc_n(v_val_1779_, 2);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1780_ = l_Array_extract___redArg(v_args_1774_, v___x_1775_, v_val_1779_);
v___x_1781_ = lean_unsigned_to_nat(1u);
v___x_1782_ = lean_nat_add(v_val_1779_, v___x_1781_);
lean_dec(v_val_1779_);
v___x_1783_ = lean_array_get_size(v_args_1774_);
v___x_1784_ = l_Array_extract___redArg(v_args_1774_, v___x_1782_, v___x_1783_);
lean_dec_ref(v_args_1774_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1780_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(lean_object* v_f_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_io_create_tempdir();
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v_r_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc_n(v_a_1789_, 2);
lean_dec_ref_known(v___x_1788_, 1);
v_r_1790_ = lean_apply_2(v_f_1786_, v_a_1789_, lean_box(0));
if (lean_obj_tag(v_r_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_ctor_get(v_r_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v_r_1790_, 1);
v___x_1792_ = l_IO_FS_removeDirAll(v_a_1789_);
lean_dec(v_a_1789_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1799_ == 0)
{
lean_object* v_unused_1800_; 
v_unused_1800_ = lean_ctor_get(v___x_1792_, 0);
lean_dec(v_unused_1800_);
v___x_1794_ = v___x_1792_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_dec(v___x_1792_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v_a_1791_);
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1791_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v_a_1791_);
v_a_1801_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1792_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1792_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1810_; 
v_a_1809_ = lean_ctor_get(v_r_1790_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v_r_1790_, 1);
v___x_1810_ = l_IO_FS_removeDirAll(v_a_1789_);
lean_dec(v_a_1789_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v___x_1810_, 0);
lean_dec(v_unused_1818_);
v___x_1812_ = v___x_1810_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_dec(v___x_1810_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set_tag(v___x_1812_, 1);
lean_ctor_set(v___x_1812_, 0, v_a_1809_);
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1809_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_a_1809_);
v_a_1819_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1810_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1810_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec_ref(v_f_1786_);
v_a_1827_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1788_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1788_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg___boxed(lean_object* v_f_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v_f_1835_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(lean_object* v_00_u03b1_1838_, lean_object* v_f_1839_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v_f_1839_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___boxed(lean_object* v_00_u03b1_1842_, lean_object* v_f_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(v_00_u03b1_1842_, v_f_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__0(lean_object* v___y_1846_, lean_object* v_____r_1847_){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___y_1846_);
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__0___boxed(lean_object* v___y_1851_, lean_object* v_____r_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lake_Samply_run___lam__0(v___y_1851_, v_____r_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(lean_object* v_s_1855_){
_start:
{
lean_object* v___x_1857_; lean_object* v_putStr_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_get_stderr();
v_putStr_1858_ = lean_ctor_get(v___x_1857_, 4);
lean_inc_ref(v_putStr_1858_);
lean_dec_ref(v___x_1857_);
v___x_1859_ = lean_apply_2(v_putStr_1858_, v_s_1855_, lean_box(0));
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0___boxed(lean_object* v_s_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(v_s_1860_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0(lean_object* v_s_1863_){
_start:
{
uint32_t v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1865_ = 10;
v___x_1866_ = lean_string_push(v_s_1863_, v___x_1865_);
v___x_1867_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(v___x_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0___boxed(lean_object* v_s_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v_s_1868_);
return v_res_1870_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1876_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__2));
v___x_1877_ = lean_unsigned_to_nat(4u);
v___x_1878_ = lean_mk_empty_array_with_capacity(v___x_1877_);
v___x_1879_ = lean_array_push(v___x_1878_, v___x_1876_);
return v___x_1879_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__3));
v___x_1881_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__5, &l_Lake_Samply_run___lam__1___closed__5_once, _init_l_Lake_Samply_run___lam__1___closed__5);
v___x_1882_ = lean_array_push(v___x_1881_, v___x_1880_);
return v___x_1882_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__4));
v___x_1884_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__6, &l_Lake_Samply_run___lam__1___closed__6_once, _init_l_Lake_Samply_run___lam__1___closed__6);
v___x_1885_ = lean_array_push(v___x_1884_, v___x_1883_);
return v___x_1885_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1886_ = ((lean_object*)(l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0));
v___x_1887_ = lean_unsigned_to_nat(2u);
v___x_1888_ = lean_mk_empty_array_with_capacity(v___x_1887_);
v___x_1889_ = lean_array_push(v___x_1888_, v___x_1886_);
return v___x_1889_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__20(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1902_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__19));
v___x_1903_ = lean_unsigned_to_nat(2u);
v___x_1904_ = lean_mk_empty_array_with_capacity(v___x_1903_);
v___x_1905_ = lean_array_push(v___x_1904_, v___x_1902_);
return v___x_1905_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__31(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1916_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__22));
v___x_1917_ = lean_unsigned_to_nat(9u);
v___x_1918_ = lean_mk_empty_array_with_capacity(v___x_1917_);
v___x_1919_ = lean_array_push(v___x_1918_, v___x_1916_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__32(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__23));
v___x_1921_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__31, &l_Lake_Samply_run___lam__1___closed__31_once, _init_l_Lake_Samply_run___lam__1___closed__31);
v___x_1922_ = lean_array_push(v___x_1921_, v___x_1920_);
return v___x_1922_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__33(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__24));
v___x_1924_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__32, &l_Lake_Samply_run___lam__1___closed__32_once, _init_l_Lake_Samply_run___lam__1___closed__32);
v___x_1925_ = lean_array_push(v___x_1924_, v___x_1923_);
return v___x_1925_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__34(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__25));
v___x_1927_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__33, &l_Lake_Samply_run___lam__1___closed__33_once, _init_l_Lake_Samply_run___lam__1___closed__33);
v___x_1928_ = lean_array_push(v___x_1927_, v___x_1926_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__1(lean_object* v_passthrough_1941_, lean_object* v_binary_1942_, lean_object* v___x_1943_, lean_object* v_env_1944_, uint8_t v_raw_1945_, lean_object* v_port_1946_, lean_object* v___x_1947_, uint8_t v_serve_1948_, lean_object* v_outputPath_1949_, lean_object* v_tmpDir_1950_){
_start:
{
lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v_a_1955_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___y_1999_; 
v___x_1996_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__0));
lean_inc_ref(v_tmpDir_1950_);
v___x_1997_ = l_System_FilePath_join(v_tmpDir_1950_, v___x_1996_);
if (lean_obj_tag(v_outputPath_1949_) == 0)
{
if (v_raw_1945_ == 0)
{
lean_object* v___x_2255_; 
v___x_2255_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__45));
v___y_1999_ = v___x_2255_;
goto v___jp_1998_;
}
else
{
lean_object* v___x_2256_; 
v___x_2256_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__46));
v___y_1999_ = v___x_2256_;
goto v___jp_1998_;
}
}
else
{
lean_object* v_val_2257_; 
v_val_2257_ = lean_ctor_get(v_outputPath_1949_, 0);
lean_inc(v_val_2257_);
lean_dec_ref_known(v_outputPath_1949_, 1);
v___y_1999_ = v_val_2257_;
goto v___jp_1998_;
}
v___jp_1952_:
{
lean_object* v___x_1956_; 
v___x_1956_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v___y_1954_, v___y_1953_);
lean_dec_ref(v___y_1953_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v___x_1956_, 0);
lean_dec(v_unused_1964_);
v___x_1958_ = v___x_1956_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_dec(v___x_1956_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set_tag(v___x_1958_, 1);
lean_ctor_set(v___x_1958_, 0, v_a_1955_);
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1955_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec(v_a_1955_);
v_a_1965_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1956_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1956_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
v___jp_1973_:
{
lean_object* v_a_1977_; lean_object* v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___y_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref(v___y_1976_);
v___x_1978_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v___y_1975_, v___y_1974_);
lean_dec_ref(v___y_1974_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1986_; 
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; 
v_unused_1987_ = lean_ctor_get(v___x_1978_, 0);
lean_dec(v_unused_1987_);
v___x_1980_ = v___x_1978_;
v_isShared_1981_ = v_isSharedCheck_1986_;
goto v_resetjp_1979_;
}
else
{
lean_dec(v___x_1978_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1986_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_a_1982_; lean_object* v___x_1984_; 
v_a_1982_ = lean_ctor_get(v_a_1977_, 0);
lean_inc(v_a_1982_);
lean_dec(v_a_1977_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v_a_1982_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_a_1977_);
v_a_1988_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1978_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1978_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
v___jp_1998_:
{
lean_object* v___x_2000_; lean_object* v_fst_2001_; lean_object* v_snd_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2000_ = l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash(v_passthrough_1941_);
v_fst_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_fst_2001_);
v_snd_2002_ = lean_ctor_get(v___x_2000_, 1);
lean_inc(v_snd_2002_);
lean_dec_ref(v___x_2000_);
v___x_2003_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__1));
v___x_2004_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2003_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_dec_ref_known(v___x_2004_, 1);
v___x_2005_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__0));
v___x_2006_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__7, &l_Lake_Samply_run___lam__1___closed__7_once, _init_l_Lake_Samply_run___lam__1___closed__7);
lean_inc_ref(v___x_1997_);
v___x_2007_ = lean_array_push(v___x_2006_, v___x_1997_);
v___x_2008_ = l_Array_append___redArg(v___x_2007_, v_fst_2001_);
lean_dec(v_fst_2001_);
v___x_2009_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__8, &l_Lake_Samply_run___lam__1___closed__8_once, _init_l_Lake_Samply_run___lam__1___closed__8);
v___x_2010_ = lean_array_push(v___x_2009_, v_binary_1942_);
v___x_2011_ = l_Array_append___redArg(v___x_2008_, v___x_2010_);
lean_dec_ref(v___x_2010_);
v___x_2012_ = l_Array_append___redArg(v___x_2011_, v_snd_2002_);
lean_dec(v_snd_2002_);
v___x_2013_ = lean_box(0);
v___x_2014_ = 1;
v___x_2015_ = 0;
v___x_2016_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2016_, 0, v___x_2005_);
lean_ctor_set(v___x_2016_, 1, v___x_1943_);
lean_ctor_set(v___x_2016_, 2, v___x_2012_);
lean_ctor_set(v___x_2016_, 3, v___x_2013_);
lean_ctor_set(v___x_2016_, 4, v_env_1944_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*5, v___x_2014_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*5 + 1, v___x_2015_);
v___x_2017_ = lean_io_process_spawn(v___x_2016_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = lean_io_process_child_wait(v___x_2005_, v_a_2018_);
lean_dec(v_a_2018_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2230_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2230_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2230_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
uint32_t v___x_2024_; uint32_t v___x_2025_; uint8_t v___x_2026_; 
v___x_2024_ = 0;
v___x_2025_ = lean_unbox_uint32(v_a_2020_);
v___x_2026_ = lean_uint32_dec_eq(v___x_2025_, v___x_2024_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; uint32_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
lean_dec(v_port_1946_);
v___x_2027_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__9));
v___x_2028_ = lean_unbox_uint32(v_a_2020_);
lean_dec(v_a_2020_);
v___x_2029_ = lean_uint32_to_nat(v___x_2028_);
v___x_2030_ = l_Nat_reprFast(v___x_2029_);
v___x_2031_ = lean_string_append(v___x_2027_, v___x_2030_);
lean_dec_ref(v___x_2030_);
v___x_2032_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__10));
v___x_2033_ = lean_string_append(v___x_2031_, v___x_2032_);
v___x_2034_ = lean_mk_io_user_error(v___x_2033_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 1);
lean_ctor_set(v___x_2022_, 0, v___x_2034_);
v___x_2036_ = v___x_2022_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
else
{
lean_del_object(v___x_2022_);
lean_dec(v_a_2020_);
if (v_raw_1945_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__11));
v___x_2039_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2038_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_dec_ref_known(v___x_2039_, 1);
v___x_2040_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__12));
lean_inc_ref(v_tmpDir_1950_);
v___x_2041_ = l_System_FilePath_join(v_tmpDir_1950_, v___x_2040_);
v___x_2042_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__0));
v___x_2043_ = l_IO_FS_writeFile(v___x_2041_, v___x_2042_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec_ref_known(v___x_2043_, 1);
v___x_2044_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__13));
v___x_2045_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__1));
v___x_2046_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__14));
lean_inc(v_port_1946_);
v___x_2047_ = l_Nat_reprFast(v_port_1946_);
v___x_2048_ = lean_string_append(v___x_2046_, v___x_2047_);
v___x_2049_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__15));
v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
lean_inc_ref(v___x_1997_);
v___x_2051_ = l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(v___x_1997_);
v___x_2052_ = lean_string_append(v___x_2050_, v___x_2051_);
lean_dec_ref(v___x_2051_);
v___x_2053_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__16));
v___x_2054_ = lean_string_append(v___x_2052_, v___x_2053_);
lean_inc_ref(v___x_2041_);
v___x_2055_ = l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(v___x_2041_);
v___x_2056_ = lean_string_append(v___x_2054_, v___x_2055_);
lean_dec_ref(v___x_2055_);
v___x_2057_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__17));
v___x_2058_ = lean_string_append(v___x_2056_, v___x_2057_);
v___x_2059_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4, &l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4);
v___x_2060_ = lean_array_push(v___x_2059_, v___x_2058_);
v___x_2061_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__5));
v___x_2062_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2062_, 0, v___x_2044_);
lean_ctor_set(v___x_2062_, 1, v___x_2045_);
lean_ctor_set(v___x_2062_, 2, v___x_2060_);
lean_ctor_set(v___x_2062_, 3, v___x_2013_);
lean_ctor_set(v___x_2062_, 4, v___x_2061_);
lean_ctor_set_uint8(v___x_2062_, sizeof(void*)*5, v___x_2014_);
lean_ctor_set_uint8(v___x_2062_, sizeof(void*)*5 + 1, v___x_2015_);
v___x_2063_ = lean_io_process_spawn(v___x_2062_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2065_ = lean_unsigned_to_nat(30000u);
v___x_2066_ = l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(v___x_2044_, v___x_2041_, v_a_2064_, v_port_1946_, v___x_2065_);
lean_dec_ref(v___x_2041_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2068_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__0));
v___x_2069_ = lean_string_append(v___x_2068_, v___x_2047_);
lean_dec_ref(v___x_2047_);
v___x_2070_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__1));
v___x_2071_ = lean_string_append(v___x_2069_, v___x_2070_);
v___x_2072_ = lean_string_append(v___x_2071_, v_a_2067_);
lean_dec(v_a_2067_);
v___x_2073_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__18));
v___x_2074_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2073_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec_ref_known(v___x_2074_, 1);
v___x_2075_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__20, &l_Lake_Samply_run___lam__1___closed__20_once, _init_l_Lake_Samply_run___lam__1___closed__20);
lean_inc_ref(v___x_1997_);
v___x_2076_ = lean_array_push(v___x_2075_, v___x_1997_);
lean_inc_ref(v___x_1947_);
v___x_2077_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2077_, 0, v___x_2005_);
lean_ctor_set(v___x_2077_, 1, v___x_1947_);
lean_ctor_set(v___x_2077_, 2, v___x_2076_);
lean_ctor_set(v___x_2077_, 3, v___x_2013_);
lean_ctor_set(v___x_2077_, 4, v___x_2061_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*5, v___x_2014_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*5 + 1, v___x_2015_);
v___x_2078_ = l_IO_Process_run(v___x_2077_, v___x_2013_);
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
lean_inc_n(v_a_2082_, 2);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2083_ = l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(v_a_2082_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2172_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2172_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2172_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_fst_2088_; lean_object* v_snd_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v_fst_2088_ = lean_ctor_get(v_a_2084_, 0);
lean_inc(v_fst_2088_);
v_snd_2089_ = lean_ctor_get(v_a_2084_, 1);
lean_inc(v_snd_2089_);
lean_dec(v_a_2084_);
v___x_2090_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__21));
v___x_2091_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__26));
lean_inc_ref(v___x_2072_);
v___x_2092_ = lean_string_append(v___x_2072_, v___x_2091_);
v___x_2093_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__27));
v___x_2094_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__28));
v___x_2095_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__29));
v___x_2096_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__30));
v___x_2097_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__34, &l_Lake_Samply_run___lam__1___closed__34_once, _init_l_Lake_Samply_run___lam__1___closed__34);
v___x_2098_ = lean_array_push(v___x_2097_, v___x_2092_);
v___x_2099_ = lean_array_push(v___x_2098_, v___x_2093_);
v___x_2100_ = lean_array_push(v___x_2099_, v___x_2094_);
v___x_2101_ = lean_array_push(v___x_2100_, v___x_2095_);
v___x_2102_ = lean_array_push(v___x_2101_, v___x_2096_);
v___x_2103_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2103_, 0, v___x_2005_);
lean_ctor_set(v___x_2103_, 1, v___x_2090_);
lean_ctor_set(v___x_2103_, 2, v___x_2102_);
lean_ctor_set(v___x_2103_, 3, v___x_2013_);
lean_ctor_set(v___x_2103_, 4, v___x_2061_);
lean_ctor_set_uint8(v___x_2103_, sizeof(void*)*5, v___x_2014_);
lean_ctor_set_uint8(v___x_2103_, sizeof(void*)*5 + 1, v___x_2015_);
v___x_2104_ = l_Lean_Json_compress(v_fst_2088_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set_tag(v___x_2086_, 1);
lean_ctor_set(v___x_2086_, 0, v___x_2104_);
v___x_2106_ = v___x_2086_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_IO_Process_run(v___x_2103_, v___x_2106_);
lean_dec_ref(v___x_2106_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = l_Lean_Json_parse(v_a_2108_);
v___x_2110_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_2109_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2112_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(v_a_2082_, v_a_2111_, v_snd_2089_);
lean_dec(v_snd_2089_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2114_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__35));
lean_inc_ref(v_tmpDir_1950_);
v___x_2115_ = l_System_FilePath_join(v_tmpDir_1950_, v___x_2114_);
v___x_2116_ = l_Lean_Json_compress(v_a_2113_);
v___x_2117_ = l_IO_FS_writeFile(v___x_2115_, v___x_2116_);
lean_dec_ref(v___x_2116_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec_ref_known(v___x_2117_, 1);
v___x_2118_ = lean_unsigned_to_nat(1u);
v___x_2119_ = lean_mk_empty_array_with_capacity(v___x_2118_);
v___x_2120_ = lean_array_push(v___x_2119_, v___x_2115_);
v___x_2121_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2121_, 0, v___x_2005_);
lean_ctor_set(v___x_2121_, 1, v___x_1947_);
lean_ctor_set(v___x_2121_, 2, v___x_2120_);
lean_ctor_set(v___x_2121_, 3, v___x_2013_);
lean_ctor_set(v___x_2121_, 4, v___x_2061_);
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*5, v___x_2014_);
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*5 + 1, v___x_2015_);
v___x_2122_ = l_IO_Process_run(v___x_2121_, v___x_2013_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec_ref_known(v___x_2122_, 1);
v___x_2123_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__36));
v___x_2124_ = l_System_FilePath_join(v_tmpDir_1950_, v___x_2123_);
v___x_2125_ = lean_io_rename(v___x_2124_, v___x_1997_);
lean_dec_ref(v___x_2124_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v___x_2126_; 
lean_dec_ref_known(v___x_2125_, 1);
v___x_2126_ = l_Lake_copyFile(v___x_1997_, v___y_1999_);
lean_dec_ref(v___x_1997_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec_ref_known(v___x_2126_, 1);
v___x_2127_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__37));
v___x_2128_ = lean_string_append(v___x_2127_, v___y_1999_);
v___x_2129_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2128_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_dec_ref_known(v___x_2129_, 1);
if (v_serve_1948_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_dec_ref(v___x_2072_);
v___x_2130_ = lean_box(0);
v___x_2131_ = l_Lake_Samply_run___lam__0(v___y_1999_, v___x_2130_);
v___y_1974_ = v_a_2064_;
v___y_1975_ = v___x_2044_;
v___y_1976_ = v___x_2131_;
goto v___jp_1973_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2132_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__38));
v___x_2133_ = lean_string_append(v___x_2132_, v___x_2072_);
v___x_2134_ = lean_string_append(v___x_2133_, v___x_2070_);
v___x_2135_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2134_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_dec_ref_known(v___x_2135_, 1);
v___x_2136_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__39));
v___x_2137_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2136_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec_ref_known(v___x_2137_, 1);
v___x_2138_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__40));
v___x_2139_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__41));
v___x_2140_ = lean_string_append(v___x_2072_, v___x_2139_);
v___x_2141_ = l_Lake_uriEncode(v___x_2140_, v___x_2042_);
lean_dec_ref(v___x_2140_);
v___x_2142_ = lean_string_append(v___x_2138_, v___x_2141_);
lean_dec_ref(v___x_2141_);
v___x_2143_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2142_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec_ref_known(v___x_2143_, 1);
v___x_2144_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__42));
v___x_2145_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2144_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2146_; 
lean_dec_ref_known(v___x_2145_, 1);
v___x_2146_ = lean_io_process_child_wait(v___x_2044_, v_a_2064_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; uint32_t v___x_2148_; uint8_t v___x_2149_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = lean_unbox_uint32(v_a_2147_);
v___x_2149_ = lean_uint32_dec_eq(v___x_2148_, v___x_2024_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; uint32_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec_ref(v___y_1999_);
v___x_2150_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__43));
v___x_2151_ = lean_unbox_uint32(v_a_2147_);
lean_dec(v_a_2147_);
v___x_2152_ = lean_uint32_to_nat(v___x_2151_);
v___x_2153_ = l_Nat_reprFast(v___x_2152_);
v___x_2154_ = lean_string_append(v___x_2150_, v___x_2153_);
lean_dec_ref(v___x_2153_);
v___x_2155_ = lean_mk_io_user_error(v___x_2154_);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v___x_2155_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec(v_a_2147_);
v___x_2156_ = lean_box(0);
v___x_2157_ = l_Lake_Samply_run___lam__0(v___y_1999_, v___x_2156_);
v___y_1974_ = v_a_2064_;
v___y_1975_ = v___x_2044_;
v___y_1976_ = v___x_2157_;
goto v___jp_1973_;
}
}
else
{
lean_object* v_a_2158_; 
lean_dec_ref(v___y_1999_);
v_a_2158_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2146_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2158_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2159_; 
lean_dec_ref(v___y_1999_);
v_a_2159_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2145_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2159_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2160_; 
lean_dec_ref(v___y_1999_);
v_a_2160_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2143_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2160_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2161_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
v_a_2161_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2137_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2161_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2162_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
v_a_2162_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2135_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2162_;
goto v___jp_1952_;
}
}
}
else
{
lean_object* v_a_2163_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
v_a_2163_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2129_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2163_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2164_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
v_a_2164_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2126_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2164_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2165_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
v_a_2165_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2125_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2165_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2166_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
v_a_2166_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2122_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2166_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2167_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
v_a_2167_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2117_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2167_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2168_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
v_a_2168_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2112_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2168_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2169_; 
lean_dec(v_snd_2089_);
lean_dec(v_a_2082_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
v_a_2169_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2110_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2169_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2170_; 
lean_dec(v_snd_2089_);
lean_dec(v_a_2082_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
v_a_2170_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2107_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2170_;
goto v___jp_1952_;
}
}
}
}
else
{
lean_object* v_a_2173_; 
lean_dec(v_a_2082_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
v_a_2173_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2083_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2173_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2174_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
v_a_2174_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2081_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2174_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2175_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
v_a_2175_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2078_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2175_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2176_; 
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
v_a_2176_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2074_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2176_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2177_; 
lean_dec_ref(v___x_2047_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
v_a_2177_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2066_, 1);
v___y_1953_ = v_a_2064_;
v___y_1954_ = v___x_2044_;
v_a_1955_ = v_a_2177_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec_ref(v___x_2047_);
lean_dec_ref(v___x_2041_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
lean_dec(v_port_1946_);
v_a_2178_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2063_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2063_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v___x_2041_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
lean_dec(v_port_1946_);
v_a_2186_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2043_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2043_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
lean_dec(v_port_1946_);
v_a_2194_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2039_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2039_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_object* v___x_2202_; 
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
lean_dec(v_port_1946_);
v___x_2202_ = l_Lake_copyFile(v___x_1997_, v___y_1999_);
lean_dec_ref(v___x_1997_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec_ref_known(v___x_2202_, 1);
v___x_2203_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__44));
v___x_2204_ = lean_string_append(v___x_2203_, v___y_1999_);
v___x_2205_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v___x_2205_, 0);
lean_dec(v_unused_2213_);
v___x_2207_ = v___x_2205_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v___x_2205_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___y_1999_);
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___y_1999_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref(v___y_1999_);
v_a_2214_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2205_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2205_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v___y_1999_);
v_a_2222_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2202_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2202_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
lean_dec(v_port_1946_);
v_a_2231_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2019_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2019_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
lean_dec(v_port_1946_);
v_a_2239_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2017_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2017_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_snd_2002_);
lean_dec(v_fst_2001_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_tmpDir_1950_);
lean_dec_ref(v___x_1947_);
lean_dec(v_port_1946_);
lean_dec_ref(v_env_1944_);
lean_dec_ref(v___x_1943_);
lean_dec_ref(v_binary_1942_);
v_a_2247_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2004_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2004_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__1___boxed(lean_object* v_passthrough_2258_, lean_object* v_binary_2259_, lean_object* v___x_2260_, lean_object* v_env_2261_, lean_object* v_raw_2262_, lean_object* v_port_2263_, lean_object* v___x_2264_, lean_object* v_serve_2265_, lean_object* v_outputPath_2266_, lean_object* v_tmpDir_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v_raw_boxed_2269_; uint8_t v_serve_boxed_2270_; lean_object* v_res_2271_; 
v_raw_boxed_2269_ = lean_unbox(v_raw_2262_);
v_serve_boxed_2270_ = lean_unbox(v_serve_2265_);
v_res_2271_ = l_Lake_Samply_run___lam__1(v_passthrough_2258_, v_binary_2259_, v___x_2260_, v_env_2261_, v_raw_boxed_2269_, v_port_2263_, v___x_2264_, v_serve_boxed_2270_, v_outputPath_2266_, v_tmpDir_2267_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run(lean_object* v_binary_2277_, lean_object* v_passthrough_2278_, lean_object* v_outputPath_2279_, lean_object* v_port_2280_, uint8_t v_raw_2281_, uint8_t v_serve_2282_, lean_object* v_env_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = ((lean_object*)(l_Lake_Samply_run___closed__0));
v___x_2286_ = ((lean_object*)(l_Lake_Samply_run___closed__1));
v___x_2287_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2285_, v___x_2286_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___f_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec_ref_known(v___x_2287_, 1);
v___x_2288_ = ((lean_object*)(l_Lake_Samply_run___closed__2));
v___x_2289_ = lean_box(v_raw_2281_);
v___x_2290_ = lean_box(v_serve_2282_);
v___f_2291_ = lean_alloc_closure((void*)(l_Lake_Samply_run___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2291_, 0, v_passthrough_2278_);
lean_closure_set(v___f_2291_, 1, v_binary_2277_);
lean_closure_set(v___f_2291_, 2, v___x_2285_);
lean_closure_set(v___f_2291_, 3, v_env_2283_);
lean_closure_set(v___f_2291_, 4, v___x_2289_);
lean_closure_set(v___f_2291_, 5, v_port_2280_);
lean_closure_set(v___f_2291_, 6, v___x_2288_);
lean_closure_set(v___f_2291_, 7, v___x_2290_);
lean_closure_set(v___f_2291_, 8, v_outputPath_2279_);
v___x_2292_ = ((lean_object*)(l_Lake_Samply_run___closed__3));
v___x_2293_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2288_, v___x_2292_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_dec_ref_known(v___x_2293_, 1);
if (v_raw_2281_ == 0)
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__21));
v___x_2295_ = ((lean_object*)(l_Lake_Samply_run___closed__4));
v___x_2296_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2294_, v___x_2295_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v___x_2297_; 
lean_dec_ref_known(v___x_2296_, 1);
v___x_2297_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v___f_2291_);
return v___x_2297_;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v___f_2291_);
v_a_2298_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2296_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2296_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v___x_2306_; 
v___x_2306_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v___f_2291_);
return v___x_2306_;
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v___f_2291_);
v_a_2307_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2293_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2293_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v_env_2283_);
lean_dec(v_port_2280_);
lean_dec(v_outputPath_2279_);
lean_dec_ref(v_passthrough_2278_);
lean_dec_ref(v_binary_2277_);
v_a_2315_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2287_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2287_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___boxed(lean_object* v_binary_2323_, lean_object* v_passthrough_2324_, lean_object* v_outputPath_2325_, lean_object* v_port_2326_, lean_object* v_raw_2327_, lean_object* v_serve_2328_, lean_object* v_env_2329_, lean_object* v_a_2330_){
_start:
{
uint8_t v_raw_boxed_2331_; uint8_t v_serve_boxed_2332_; lean_object* v_res_2333_; 
v_raw_boxed_2331_ = lean_unbox(v_raw_2327_);
v_serve_boxed_2332_ = lean_unbox(v_serve_2328_);
v_res_2333_ = l_Lake_Samply_run(v_binary_2323_, v_passthrough_2324_, v_outputPath_2325_, v_port_2326_, v_raw_boxed_2331_, v_serve_boxed_2332_, v_env_2329_);
return v_res_2333_;
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
