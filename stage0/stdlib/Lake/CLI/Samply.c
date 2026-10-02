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
uint32_t v___x_250_; uint8_t v___y_257_; uint32_t v___x_262_; uint8_t v___x_263_; 
v___x_250_ = lean_string_utf8_get_fast(v_str_235_, v___x_238_);
v___x_262_ = 65;
v___x_263_ = lean_uint32_dec_le(v___x_262_, v___x_250_);
if (v___x_263_ == 0)
{
v___y_257_ = v___x_263_;
goto v___jp_256_;
}
else
{
uint32_t v___x_264_; uint8_t v___x_265_; 
v___x_264_ = 90;
v___x_265_ = lean_uint32_dec_le(v___x_250_, v___x_264_);
v___y_257_ = v___x_265_;
goto v___jp_256_;
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
if (v___y_257_ == 0)
{
uint32_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = 97;
v___x_259_ = lean_uint32_dec_le(v___x_258_, v___x_250_);
if (v___x_259_ == 0)
{
goto v___jp_251_;
}
else
{
uint32_t v___x_260_; uint8_t v___x_261_; 
v___x_260_ = 122;
v___x_261_ = lean_uint32_dec_le(v___x_250_, v___x_260_);
if (v___x_261_ == 0)
{
goto v___jp_251_;
}
else
{
goto v___jp_239_;
}
}
}
else
{
goto v___jp_239_;
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1___boxed(lean_object* v_s_266_, lean_object* v_pos_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1(v_s_266_, v_pos_267_);
lean_dec_ref(v_s_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(lean_object* v_decoded_269_, lean_object* v___x_270_, lean_object* v___x_271_, lean_object* v_a_272_, lean_object* v_b_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_box(0);
switch(lean_obj_tag(v_a_272_))
{
case 0:
{
lean_object* v_pos_275_; lean_object* v___x_276_; 
v_pos_275_ = lean_ctor_get(v_a_272_, 0);
lean_inc(v_pos_275_);
lean_dec_ref_known(v_a_272_, 1);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v_pos_275_);
return v___x_276_;
}
case 1:
{
lean_object* v_pos_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_286_; 
v_pos_277_ = lean_ctor_get(v_a_272_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_a_272_);
if (v_isSharedCheck_286_ == 0)
{
v___x_279_ = v_a_272_;
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_pos_277_);
lean_dec(v_a_272_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_string_utf8_next_fast(v_decoded_269_, v_pos_277_);
lean_dec(v_pos_277_);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 0);
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_285_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
v_a_272_ = v___x_283_;
v_b_273_ = v___x_274_;
goto _start;
}
}
}
case 2:
{
lean_object* v_needle_287_; lean_object* v_table_288_; lean_object* v_stackPos_289_; lean_object* v_needlePos_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_343_; 
v_needle_287_ = lean_ctor_get(v_a_272_, 0);
v_table_288_ = lean_ctor_get(v_a_272_, 1);
v_stackPos_289_ = lean_ctor_get(v_a_272_, 2);
v_needlePos_290_ = lean_ctor_get(v_a_272_, 3);
v_isSharedCheck_343_ = !lean_is_exclusive(v_a_272_);
if (v_isSharedCheck_343_ == 0)
{
v___x_292_ = v_a_272_;
v_isShared_293_ = v_isSharedCheck_343_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_needlePos_290_);
lean_inc(v_stackPos_289_);
lean_inc(v_table_288_);
lean_inc(v_needle_287_);
lean_dec(v_a_272_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_343_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_str_294_; lean_object* v_startInclusive_295_; lean_object* v_endExclusive_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_str_294_ = lean_ctor_get(v_needle_287_, 0);
v_startInclusive_295_ = lean_ctor_get(v_needle_287_, 1);
v_endExclusive_296_ = lean_ctor_get(v_needle_287_, 2);
v___x_297_ = lean_nat_sub(v_stackPos_289_, v_needlePos_290_);
v___x_298_ = lean_nat_sub(v_endExclusive_296_, v_startInclusive_295_);
v___x_299_ = lean_nat_add(v___x_297_, v___x_298_);
v___x_300_ = lean_nat_dec_le(v___x_299_, v___x_271_);
lean_dec(v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
lean_dec(v___x_298_);
lean_del_object(v___x_292_);
lean_dec(v_needlePos_290_);
lean_dec(v_stackPos_289_);
lean_dec_ref(v_table_288_);
lean_dec_ref(v_needle_287_);
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v___x_297_, v___x_301_);
lean_dec(v___x_297_);
v___x_303_ = lean_nat_dec_le(v___x_302_, v___x_271_);
lean_dec(v___x_302_);
if (v___x_303_ == 0)
{
lean_inc(v_b_273_);
return v_b_273_;
}
else
{
lean_object* v___x_304_; 
v___x_304_ = lean_box(3);
v_a_272_ = v___x_304_;
v_b_273_ = v___x_274_;
goto _start;
}
}
else
{
uint8_t v_stackByte_306_; lean_object* v___x_307_; uint8_t v_patByte_308_; uint8_t v___x_309_; 
lean_dec(v___x_297_);
lean_inc(v_stackPos_289_);
v_stackByte_306_ = lean_string_get_byte_fast(v_decoded_269_, v_stackPos_289_);
v___x_307_ = lean_nat_add(v_startInclusive_295_, v_needlePos_290_);
v_patByte_308_ = lean_string_get_byte_fast(v_str_294_, v___x_307_);
v___x_309_ = lean_uint8_dec_eq(v_stackByte_306_, v_patByte_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; uint8_t v_decide_311_; 
lean_dec(v___x_298_);
v___x_310_ = lean_unsigned_to_nat(0u);
v_decide_311_ = lean_nat_dec_eq(v_needlePos_290_, v___x_310_);
if (v_decide_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_newNeedlePos_314_; uint8_t v___x_315_; 
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_sub(v_needlePos_290_, v___x_312_);
lean_dec(v_needlePos_290_);
v_newNeedlePos_314_ = lean_array_fget_borrowed(v_table_288_, v___x_313_);
lean_dec(v___x_313_);
v___x_315_ = lean_nat_dec_eq(v_newNeedlePos_314_, v___x_310_);
if (v___x_315_ == 0)
{
lean_object* v___x_317_; 
lean_inc(v_newNeedlePos_314_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 3, v_newNeedlePos_314_);
v___x_317_ = v___x_292_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_needle_287_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_table_288_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_stackPos_289_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_newNeedlePos_314_);
v___x_317_ = v_reuseFailAlloc_319_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
v_a_272_ = v___x_317_;
v_b_273_ = v___x_274_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_320_; lean_object* v___x_322_; 
v_nextStackPos_320_ = l_String_Slice_posGE___redArg(v___x_270_, v_stackPos_289_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 3, v___x_310_);
lean_ctor_set(v___x_292_, 2, v_nextStackPos_320_);
v___x_322_ = v___x_292_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_needle_287_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_table_288_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_nextStackPos_320_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v___x_310_);
v___x_322_ = v_reuseFailAlloc_324_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
v_a_272_ = v___x_322_;
v_b_273_ = v___x_274_;
goto _start;
}
}
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_nextStackPos_327_; lean_object* v___x_329_; 
lean_dec(v_needlePos_290_);
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_nat_add(v_stackPos_289_, v___x_325_);
lean_dec(v_stackPos_289_);
v_nextStackPos_327_ = l_String_Slice_posGE___redArg(v___x_270_, v___x_326_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 3, v___x_310_);
lean_ctor_set(v___x_292_, 2, v_nextStackPos_327_);
v___x_329_ = v___x_292_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_needle_287_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_table_288_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_nextStackPos_327_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v___x_310_);
v___x_329_ = v_reuseFailAlloc_331_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
v_a_272_ = v___x_329_;
v_b_273_ = v___x_274_;
goto _start;
}
}
}
else
{
lean_object* v___x_332_; lean_object* v_nextStackPos_333_; lean_object* v_nextNeedlePos_334_; uint8_t v_decide_335_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v_nextStackPos_333_ = lean_nat_add(v_stackPos_289_, v___x_332_);
lean_dec(v_stackPos_289_);
v_nextNeedlePos_334_ = lean_nat_add(v_needlePos_290_, v___x_332_);
lean_dec(v_needlePos_290_);
v_decide_335_ = lean_nat_dec_eq(v_nextNeedlePos_334_, v___x_298_);
lean_dec(v___x_298_);
if (v_decide_335_ == 0)
{
lean_object* v___x_337_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 3, v_nextNeedlePos_334_);
lean_ctor_set(v___x_292_, 2, v_nextStackPos_333_);
v___x_337_ = v___x_292_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_needle_287_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_table_288_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_nextStackPos_333_);
lean_ctor_set(v_reuseFailAlloc_339_, 3, v_nextNeedlePos_334_);
v___x_337_ = v_reuseFailAlloc_339_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
v_a_272_ = v___x_337_;
goto _start;
}
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
lean_del_object(v___x_292_);
lean_dec_ref(v_table_288_);
lean_dec_ref(v_needle_287_);
v___x_340_ = lean_nat_sub(v_nextStackPos_333_, v_nextNeedlePos_334_);
lean_dec(v_nextNeedlePos_334_);
lean_dec(v_nextStackPos_333_);
v___x_341_ = l_String_Slice_pos_x21(v___x_270_, v___x_340_);
lean_dec(v___x_340_);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
}
}
}
default: 
{
lean_inc(v_b_273_);
return v_b_273_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg___boxed(lean_object* v_decoded_344_, lean_object* v___x_345_, lean_object* v___x_346_, lean_object* v_a_347_, lean_object* v_b_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(v_decoded_344_, v___x_345_, v___x_346_, v_a_347_, v_b_348_);
lean_dec(v_b_348_);
lean_dec(v___x_346_);
lean_dec_ref(v___x_345_);
lean_dec_ref(v_decoded_344_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(lean_object* v_output_354_, lean_object* v_port_355_){
_start:
{
lean_object* v_decoded_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_serverUrl_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___y_366_; lean_object* v___x_391_; uint8_t v___x_392_; 
v_decoded_356_ = l_System_Uri_unescapeUri(v_output_354_);
v___x_357_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__0));
v___x_358_ = l_Nat_reprFast(v_port_355_);
v___x_359_ = lean_string_append(v___x_357_, v___x_358_);
lean_dec_ref(v___x_358_);
v___x_360_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__1));
v_serverUrl_361_ = lean_string_append(v___x_359_, v___x_360_);
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_string_utf8_byte_size(v_decoded_356_);
lean_inc_ref(v_decoded_356_);
v___x_364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_364_, 0, v_decoded_356_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
lean_ctor_set(v___x_364_, 2, v___x_363_);
v___x_391_ = lean_string_utf8_byte_size(v_serverUrl_361_);
v___x_392_ = lean_nat_dec_eq(v___x_391_, v___x_362_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
lean_inc_ref(v_serverUrl_361_);
v___x_393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_393_, 0, v_serverUrl_361_);
lean_ctor_set(v___x_393_, 1, v___x_362_);
lean_ctor_set(v___x_393_, 2, v___x_391_);
v___x_394_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_393_);
v___x_395_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
lean_ctor_set(v___x_395_, 2, v___x_362_);
lean_ctor_set(v___x_395_, 3, v___x_362_);
v___y_366_ = v___x_395_;
goto v___jp_365_;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__2));
v___y_366_ = v___x_396_;
goto v___jp_365_;
}
v___jp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_box(0);
v___x_368_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(v_decoded_356_, v___x_364_, v___x_363_, v___y_366_, v___x_367_);
lean_dec_ref_known(v___x_364_, 3);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_dec_ref(v_serverUrl_361_);
lean_dec_ref(v_decoded_356_);
return v___x_367_;
}
else
{
lean_object* v_val_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_390_; 
v_val_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_390_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_390_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_val_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_390_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_373_ = lean_string_utf8_byte_size(v_serverUrl_361_);
v___x_374_ = lean_nat_sub(v___x_363_, v_val_369_);
v___x_375_ = lean_nat_dec_le(v___x_373_, v___x_374_);
lean_dec(v___x_374_);
if (v___x_375_ == 0)
{
lean_del_object(v___x_371_);
lean_dec(v_val_369_);
lean_dec_ref(v_serverUrl_361_);
lean_dec_ref(v_decoded_356_);
return v___x_367_;
}
else
{
uint8_t v___x_376_; 
v___x_376_ = lean_string_memcmp(v_decoded_356_, v_serverUrl_361_, v_val_369_, v___x_362_, v___x_373_);
lean_dec_ref(v_serverUrl_361_);
if (v___x_376_ == 0)
{
lean_del_object(v___x_371_);
lean_dec(v_val_369_);
lean_dec_ref(v_decoded_356_);
return v___x_367_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
lean_inc(v_val_369_);
lean_inc_ref_n(v_decoded_356_, 2);
v___x_377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_377_, 0, v_decoded_356_);
lean_ctor_set(v___x_377_, 1, v_val_369_);
lean_ctor_set(v___x_377_, 2, v___x_363_);
v___x_378_ = l_String_Slice_pos_x21(v___x_377_, v___x_373_);
lean_dec_ref_known(v___x_377_, 3);
v___x_379_ = lean_nat_add(v_val_369_, v___x_378_);
lean_dec(v___x_378_);
lean_dec(v_val_369_);
lean_inc(v___x_379_);
v___x_380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_380_, 0, v_decoded_356_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
lean_ctor_set(v___x_380_, 2, v___x_363_);
v___x_381_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1(v___x_380_, v___x_362_);
lean_dec_ref_known(v___x_380_, 3);
v___x_382_ = lean_nat_add(v___x_379_, v___x_381_);
lean_dec(v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_383_, 0, v_decoded_356_);
lean_ctor_set(v___x_383_, 1, v___x_379_);
lean_ctor_set(v___x_383_, 2, v___x_382_);
v___x_384_ = l_String_Slice_toString(v___x_383_);
lean_dec_ref_known(v___x_383_, 3);
v___x_385_ = lean_string_utf8_byte_size(v___x_384_);
v___x_386_ = lean_nat_dec_eq(v___x_385_, v___x_362_);
if (v___x_386_ == 0)
{
lean_object* v___x_388_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_384_);
v___x_388_ = v___x_371_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_384_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_dec_ref(v___x_384_);
lean_del_object(v___x_371_);
return v___x_367_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___boxed(lean_object* v_output_397_, lean_object* v_port_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(v_output_397_, v_port_398_);
lean_dec_ref(v_output_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0(lean_object* v_decoded_400_, lean_object* v___x_401_, lean_object* v___x_402_, lean_object* v_inst_403_, lean_object* v_R_404_, lean_object* v_a_405_, lean_object* v_b_406_, lean_object* v_c_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(v_decoded_400_, v___x_401_, v___x_402_, v_a_405_, v_b_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___boxed(lean_object* v_decoded_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v_inst_412_, lean_object* v_R_413_, lean_object* v_a_414_, lean_object* v_b_415_, lean_object* v_c_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0(v_decoded_409_, v___x_410_, v___x_411_, v_inst_412_, v_R_413_, v_a_414_, v_b_415_, v_c_416_);
lean_dec(v_b_415_);
lean_dec(v___x_411_);
lean_dec_ref(v___x_410_);
lean_dec_ref(v_decoded_409_);
return v_res_417_;
}
}
static lean_object* _init_l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = l_instInhabitedError;
v___x_419_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_419_, 0, lean_box(0));
lean_closure_set(v___x_419_, 1, lean_box(0));
lean_closure_set(v___x_419_, 2, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(lean_object* v_msg_420_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_1178__overap_423_; lean_object* v___x_424_; 
v___x_422_ = lean_obj_once(&l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0, &l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0_once, _init_l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0);
v___x_1178__overap_423_ = lean_panic_fn_borrowed(v___x_422_, v_msg_420_);
v___x_424_ = lean_apply_1(v___x_1178__overap_423_, lean_box(0));
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___boxed(lean_object* v_msg_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(v_msg_425_);
return v_res_427_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__2));
v___x_432_ = lean_mk_io_user_error(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(lean_object* v_val_433_, lean_object* v_timeoutMs_434_, lean_object* v_cfg_435_, lean_object* v_proc_436_, lean_object* v_logFile_437_, lean_object* v_port_438_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_440_ = lean_box(0);
v___x_441_ = lean_io_mono_ms_now();
v___x_442_ = lean_nat_sub(v___x_441_, v_val_433_);
lean_dec(v___x_441_);
v___x_443_ = lean_nat_dec_lt(v_timeoutMs_434_, v___x_442_);
lean_dec(v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
v___x_444_ = lean_io_process_child_try_wait(v_cfg_435_, v_proc_436_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
if (lean_obj_tag(v_a_445_) == 1)
{
lean_object* v_val_446_; lean_object* v___x_447_; 
lean_dec(v_port_438_);
v_val_446_ = lean_ctor_get(v_a_445_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v_a_445_, 1);
v___x_447_ = l_IO_FS_readFile(v_logFile_437_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_464_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_464_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; uint32_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_452_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__0));
v___x_453_ = lean_unbox_uint32(v_val_446_);
lean_dec(v_val_446_);
v___x_454_ = lean_uint32_to_nat(v___x_453_);
v___x_455_ = l_Nat_reprFast(v___x_454_);
v___x_456_ = lean_string_append(v___x_452_, v___x_455_);
lean_dec_ref(v___x_455_);
v___x_457_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__1));
v___x_458_ = lean_string_append(v___x_456_, v___x_457_);
v___x_459_ = lean_string_append(v___x_458_, v_a_448_);
lean_dec(v_a_448_);
v___x_460_ = lean_mk_io_user_error(v___x_459_);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 1);
lean_ctor_set(v___x_450_, 0, v___x_460_);
v___x_462_ = v___x_450_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_val_446_);
v_a_465_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_447_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_447_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v___x_473_; 
lean_dec(v_a_445_);
v___x_473_ = l_IO_FS_readFile(v_logFile_437_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_486_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_486_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_486_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_486_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; 
lean_inc(v_port_438_);
v___x_478_ = l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(v_a_474_, v_port_438_);
lean_dec(v_a_474_);
if (lean_obj_tag(v___x_478_) == 1)
{
lean_object* v___x_479_; lean_object* v___x_481_; 
lean_dec(v_port_438_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_440_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_479_);
v___x_481_ = v___x_476_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
else
{
uint32_t v___x_483_; lean_object* v___x_484_; 
lean_dec(v___x_478_);
lean_del_object(v___x_476_);
v___x_483_ = 200;
v___x_484_ = l_IO_sleep(v___x_483_);
goto _start;
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec(v_port_438_);
v_a_487_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_473_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_473_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec(v_port_438_);
v_a_495_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_444_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_444_);
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
else
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v_port_438_);
v___x_503_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___boxed(lean_object* v_val_505_, lean_object* v_timeoutMs_506_, lean_object* v_cfg_507_, lean_object* v_proc_508_, lean_object* v_logFile_509_, lean_object* v_port_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v_val_505_, v_timeoutMs_506_, v_cfg_507_, v_proc_508_, v_logFile_509_, v_port_510_);
lean_dec_ref(v_logFile_509_);
lean_dec_ref(v_proc_508_);
lean_dec_ref(v_cfg_507_);
lean_dec(v_timeoutMs_506_);
lean_dec(v_val_505_);
return v_res_512_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_516_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__2));
v___x_517_ = lean_unsigned_to_nat(2u);
v___x_518_ = lean_unsigned_to_nat(58u);
v___x_519_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__1));
v___x_520_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__0));
v___x_521_ = l_mkPanicMessageWithDecl(v___x_520_, v___x_519_, v___x_518_, v___x_517_, v___x_516_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(lean_object* v_cfg_522_, lean_object* v_logFile_523_, lean_object* v_proc_524_, lean_object* v_port_525_, lean_object* v_timeoutMs_526_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_io_mono_ms_now();
v___x_529_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v___x_528_, v_timeoutMs_526_, v_cfg_522_, v_proc_524_, v_logFile_523_, v_port_525_);
lean_dec(v___x_528_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_541_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_541_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_541_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_fst_534_; 
v_fst_534_ = lean_ctor_get(v_a_530_, 0);
lean_inc(v_fst_534_);
lean_dec(v_a_530_);
if (lean_obj_tag(v_fst_534_) == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_del_object(v___x_532_);
v___x_535_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3, &l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3);
v___x_536_ = l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(v___x_535_);
return v___x_536_;
}
else
{
lean_object* v_val_537_; lean_object* v___x_539_; 
v_val_537_ = lean_ctor_get(v_fst_534_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v_fst_534_, 1);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v_val_537_);
v___x_539_ = v___x_532_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_val_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_a_542_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_529_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_529_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___boxed(lean_object* v_cfg_550_, lean_object* v_logFile_551_, lean_object* v_proc_552_, lean_object* v_port_553_, lean_object* v_timeoutMs_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(v_cfg_550_, v_logFile_551_, v_proc_552_, v_port_553_, v_timeoutMs_554_);
lean_dec(v_timeoutMs_554_);
lean_dec_ref(v_proc_552_);
lean_dec_ref(v_logFile_551_);
lean_dec_ref(v_cfg_550_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(lean_object* v_val_557_, lean_object* v_timeoutMs_558_, lean_object* v_cfg_559_, lean_object* v_proc_560_, lean_object* v_logFile_561_, lean_object* v_port_562_, lean_object* v_inst_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v_val_557_, v_timeoutMs_558_, v_cfg_559_, v_proc_560_, v_logFile_561_, v_port_562_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___boxed(lean_object* v_val_567_, lean_object* v_timeoutMs_568_, lean_object* v_cfg_569_, lean_object* v_proc_570_, lean_object* v_logFile_571_, lean_object* v_port_572_, lean_object* v_inst_573_, lean_object* v_a_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(v_val_567_, v_timeoutMs_568_, v_cfg_569_, v_proc_570_, v_logFile_571_, v_port_572_, v_inst_573_, v_a_574_);
lean_dec_ref(v_a_574_);
lean_dec_ref(v_logFile_571_);
lean_dec_ref(v_proc_570_);
lean_dec_ref(v_cfg_569_);
lean_dec(v_timeoutMs_568_);
lean_dec(v_val_567_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(lean_object* v_j_577_, lean_object* v_k_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = l_Lean_Json_getObjValD(v_j_577_, v_k_578_);
v___x_580_ = l_Lean_Json_getStr_x3f(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0___boxed(lean_object* v_j_581_, lean_object* v_k_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_j_581_, v_k_582_);
lean_dec_ref(v_k_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(lean_object* v_e_584_){
_start:
{
if (lean_obj_tag(v_e_584_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
v_a_586_ = lean_ctor_get(v_e_584_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_e_584_);
if (v_isSharedCheck_594_ == 0)
{
v___x_588_ = v_e_584_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v_e_584_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_mk_io_user_error(v_a_586_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 1);
lean_ctor_set(v___x_588_, 0, v___x_590_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_a_595_ = lean_ctor_get(v_e_584_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v_e_584_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v_e_584_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v_e_584_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 0);
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg___boxed(lean_object* v_e_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v_e_603_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(lean_object* v_00_u03b1_606_, lean_object* v_e_607_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v_e_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___boxed(lean_object* v_00_u03b1_610_, lean_object* v_e_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(v_00_u03b1_610_, v_e_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(size_t v_sz_614_, size_t v_i_615_, lean_object* v_bs_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_615_, v_sz_614_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v_bs_616_);
return v___x_618_;
}
else
{
lean_object* v_v_619_; lean_object* v___x_620_; lean_object* v_bs_x27_621_; size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; 
v_v_619_ = lean_array_uget(v_bs_616_, v_i_615_);
v___x_620_ = lean_unsigned_to_nat(0u);
v_bs_x27_621_ = lean_array_uset(v_bs_616_, v_i_615_, v___x_620_);
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_615_, v___x_622_);
v___x_624_ = lean_array_uset(v_bs_x27_621_, v_i_615_, v_v_619_);
v_i_615_ = v___x_623_;
v_bs_616_ = v___x_624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_626_, lean_object* v_i_627_, lean_object* v_bs_628_){
_start:
{
size_t v_sz_boxed_629_; size_t v_i_boxed_630_; lean_object* v_res_631_; 
v_sz_boxed_629_ = lean_unbox_usize(v_sz_626_);
lean_dec(v_sz_626_);
v_i_boxed_630_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_res_631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(v_sz_boxed_629_, v_i_boxed_630_, v_bs_628_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 4)
{
lean_object* v_elems_634_; size_t v_sz_635_; size_t v___x_636_; lean_object* v___x_637_; 
v_elems_634_ = lean_ctor_get(v_x_633_, 0);
lean_inc_ref(v_elems_634_);
lean_dec_ref_known(v_x_633_, 1);
v_sz_635_ = lean_array_size(v_elems_634_);
v___x_636_ = ((size_t)0ULL);
v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(v_sz_635_, v___x_636_, v_elems_634_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_638_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_639_ = lean_unsigned_to_nat(80u);
v___x_640_ = l_Lean_Json_pretty(v_x_633_, v___x_639_);
v___x_641_ = lean_string_append(v___x_638_, v___x_640_);
lean_dec_ref(v___x_640_);
v___x_642_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_643_ = lean_string_append(v___x_641_, v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(lean_object* v_j_645_, lean_object* v_k_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = l_Lean_Json_getObjValD(v_j_645_, v_k_646_);
v___x_648_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3___boxed(lean_object* v_j_649_, lean_object* v_k_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_j_649_, v_k_650_);
lean_dec_ref(v_k_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(size_t v_sz_652_, size_t v_i_653_, lean_object* v_bs_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = lean_usize_dec_lt(v_i_653_, v_sz_652_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v_bs_654_);
return v___x_656_;
}
else
{
lean_object* v_v_657_; lean_object* v___x_658_; 
v_v_657_ = lean_array_uget_borrowed(v_bs_654_, v_i_653_);
lean_inc(v_v_657_);
v___x_658_ = l_Lean_Json_getNat_x3f(v_v_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec_ref(v_bs_654_);
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_668_; lean_object* v_bs_x27_669_; size_t v___x_670_; size_t v___x_671_; lean_object* v___x_672_; 
v_a_667_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_658_, 1);
v___x_668_ = lean_unsigned_to_nat(0u);
v_bs_x27_669_ = lean_array_uset(v_bs_654_, v_i_653_, v___x_668_);
v___x_670_ = ((size_t)1ULL);
v___x_671_ = lean_usize_add(v_i_653_, v___x_670_);
v___x_672_ = lean_array_uset(v_bs_x27_669_, v_i_653_, v_a_667_);
v_i_653_ = v___x_671_;
v_bs_654_ = v___x_672_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9___boxed(lean_object* v_sz_674_, lean_object* v_i_675_, lean_object* v_bs_676_){
_start:
{
size_t v_sz_boxed_677_; size_t v_i_boxed_678_; lean_object* v_res_679_; 
v_sz_boxed_677_ = lean_unbox_usize(v_sz_674_);
lean_dec(v_sz_674_);
v_i_boxed_678_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_res_679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(v_sz_boxed_677_, v_i_boxed_678_, v_bs_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7(lean_object* v_x_680_){
_start:
{
if (lean_obj_tag(v_x_680_) == 4)
{
lean_object* v_elems_681_; size_t v_sz_682_; size_t v___x_683_; lean_object* v___x_684_; 
v_elems_681_ = lean_ctor_get(v_x_680_, 0);
lean_inc_ref(v_elems_681_);
lean_dec_ref_known(v_x_680_, 1);
v_sz_682_ = lean_array_size(v_elems_681_);
v___x_683_ = ((size_t)0ULL);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(v_sz_682_, v___x_683_, v_elems_681_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_685_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_686_ = lean_unsigned_to_nat(80u);
v___x_687_ = l_Lean_Json_pretty(v_x_680_, v___x_686_);
v___x_688_ = lean_string_append(v___x_685_, v___x_687_);
lean_dec_ref(v___x_687_);
v___x_689_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_690_ = lean_string_append(v___x_688_, v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(lean_object* v_j_692_, lean_object* v_k_693_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = l_Lean_Json_getObjValD(v_j_692_, v_k_693_);
v___x_695_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7(v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5___boxed(lean_object* v_j_696_, lean_object* v_k_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_j_696_, v_k_697_);
lean_dec_ref(v_k_697_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(size_t v_sz_699_, size_t v_i_700_, lean_object* v_bs_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_lt(v_i_700_, v_sz_699_);
if (v___x_702_ == 0)
{
return v_bs_701_;
}
else
{
lean_object* v_v_703_; lean_object* v___x_704_; lean_object* v_bs_x27_705_; lean_object* v___x_706_; lean_object* v___x_707_; size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; 
v_v_703_ = lean_array_uget(v_bs_701_, v_i_700_);
v___x_704_ = lean_unsigned_to_nat(0u);
v_bs_x27_705_ = lean_array_uset(v_bs_701_, v_i_700_, v___x_704_);
v___x_706_ = l_Lean_JsonNumber_fromNat(v_v_703_);
v___x_707_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_add(v_i_700_, v___x_708_);
v___x_710_ = lean_array_uset(v_bs_x27_705_, v_i_700_, v___x_707_);
v_i_700_ = v___x_709_;
v_bs_701_ = v___x_710_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13___boxed(lean_object* v_sz_712_, lean_object* v_i_713_, lean_object* v_bs_714_){
_start:
{
size_t v_sz_boxed_715_; size_t v_i_boxed_716_; lean_object* v_res_717_; 
v_sz_boxed_715_ = lean_unbox_usize(v_sz_712_);
lean_dec(v_sz_712_);
v_i_boxed_716_ = lean_unbox_usize(v_i_713_);
lean_dec(v_i_713_);
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(v_sz_boxed_715_, v_i_boxed_716_, v_bs_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(lean_object* v_a_718_){
_start:
{
size_t v_sz_719_; size_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_sz_719_ = lean_array_size(v_a_718_);
v___x_720_ = ((size_t)0ULL);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(v_sz_719_, v___x_720_, v_a_718_);
v___x_722_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(lean_object* v_a_723_, lean_object* v_x_724_){
_start:
{
if (lean_obj_tag(v_x_724_) == 0)
{
uint8_t v___x_725_; 
v___x_725_ = 0;
return v___x_725_;
}
else
{
lean_object* v_key_726_; lean_object* v_tail_727_; uint8_t v___x_728_; 
v_key_726_ = lean_ctor_get(v_x_724_, 0);
v_tail_727_ = lean_ctor_get(v_x_724_, 2);
v___x_728_ = lean_nat_dec_eq(v_key_726_, v_a_723_);
if (v___x_728_ == 0)
{
v_x_724_ = v_tail_727_;
goto _start;
}
else
{
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg___boxed(lean_object* v_a_730_, lean_object* v_x_731_){
_start:
{
uint8_t v_res_732_; lean_object* v_r_733_; 
v_res_732_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_730_, v_x_731_);
lean_dec(v_x_731_);
lean_dec(v_a_730_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(lean_object* v_m_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_buckets_736_; lean_object* v___x_737_; uint64_t v___x_738_; uint64_t v___x_739_; uint64_t v___x_740_; uint64_t v_fold_741_; uint64_t v___x_742_; uint64_t v___x_743_; uint64_t v___x_744_; size_t v___x_745_; size_t v___x_746_; size_t v___x_747_; size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_buckets_736_ = lean_ctor_get(v_m_734_, 1);
v___x_737_ = lean_array_get_size(v_buckets_736_);
v___x_738_ = lean_uint64_of_nat(v_a_735_);
v___x_739_ = 32ULL;
v___x_740_ = lean_uint64_shift_right(v___x_738_, v___x_739_);
v_fold_741_ = lean_uint64_xor(v___x_738_, v___x_740_);
v___x_742_ = 16ULL;
v___x_743_ = lean_uint64_shift_right(v_fold_741_, v___x_742_);
v___x_744_ = lean_uint64_xor(v_fold_741_, v___x_743_);
v___x_745_ = lean_uint64_to_usize(v___x_744_);
v___x_746_ = lean_usize_of_nat(v___x_737_);
v___x_747_ = ((size_t)1ULL);
v___x_748_ = lean_usize_sub(v___x_746_, v___x_747_);
v___x_749_ = lean_usize_land(v___x_745_, v___x_748_);
v___x_750_ = lean_array_uget_borrowed(v_buckets_736_, v___x_749_);
v___x_751_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_735_, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg___boxed(lean_object* v_m_752_, lean_object* v_a_753_){
_start:
{
uint8_t v_res_754_; lean_object* v_r_755_; 
v_res_754_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_m_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_m_752_);
v_r_755_ = lean_box(v_res_754_);
return v_r_755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
if (lean_obj_tag(v_x_757_) == 0)
{
return v_x_756_;
}
else
{
lean_object* v_key_758_; lean_object* v_value_759_; lean_object* v_tail_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_783_; 
v_key_758_ = lean_ctor_get(v_x_757_, 0);
v_value_759_ = lean_ctor_get(v_x_757_, 1);
v_tail_760_ = lean_ctor_get(v_x_757_, 2);
v_isSharedCheck_783_ = !lean_is_exclusive(v_x_757_);
if (v_isSharedCheck_783_ == 0)
{
v___x_762_ = v_x_757_;
v_isShared_763_ = v_isSharedCheck_783_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_tail_760_);
lean_inc(v_value_759_);
lean_inc(v_key_758_);
lean_dec(v_x_757_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_783_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; uint64_t v___x_765_; uint64_t v___x_766_; uint64_t v___x_767_; uint64_t v_fold_768_; uint64_t v___x_769_; uint64_t v___x_770_; uint64_t v___x_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_764_ = lean_array_get_size(v_x_756_);
v___x_765_ = lean_uint64_of_nat(v_key_758_);
v___x_766_ = 32ULL;
v___x_767_ = lean_uint64_shift_right(v___x_765_, v___x_766_);
v_fold_768_ = lean_uint64_xor(v___x_765_, v___x_767_);
v___x_769_ = 16ULL;
v___x_770_ = lean_uint64_shift_right(v_fold_768_, v___x_769_);
v___x_771_ = lean_uint64_xor(v_fold_768_, v___x_770_);
v___x_772_ = lean_uint64_to_usize(v___x_771_);
v___x_773_ = lean_usize_of_nat(v___x_764_);
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_sub(v___x_773_, v___x_774_);
v___x_776_ = lean_usize_land(v___x_772_, v___x_775_);
v___x_777_ = lean_array_uget_borrowed(v_x_756_, v___x_776_);
lean_inc(v___x_777_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 2, v___x_777_);
v___x_779_ = v___x_762_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_key_758_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_value_759_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v___x_777_);
v___x_779_ = v_reuseFailAlloc_782_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; 
v___x_780_ = lean_array_uset(v_x_756_, v___x_776_, v___x_779_);
v_x_756_ = v___x_780_;
v_x_757_ = v_tail_760_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(lean_object* v_i_784_, lean_object* v_source_785_, lean_object* v_target_786_){
_start:
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = lean_array_get_size(v_source_785_);
v___x_788_ = lean_nat_dec_lt(v_i_784_, v___x_787_);
if (v___x_788_ == 0)
{
lean_dec_ref(v_source_785_);
lean_dec(v_i_784_);
return v_target_786_;
}
else
{
lean_object* v_es_789_; lean_object* v___x_790_; lean_object* v_source_791_; lean_object* v_target_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_es_789_ = lean_array_fget(v_source_785_, v_i_784_);
v___x_790_ = lean_box(0);
v_source_791_ = lean_array_fset(v_source_785_, v_i_784_, v___x_790_);
v_target_792_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(v_target_786_, v_es_789_);
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_add(v_i_784_, v___x_793_);
lean_dec(v_i_784_);
v_i_784_ = v___x_794_;
v_source_785_ = v_source_791_;
v_target_786_ = v_target_792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(lean_object* v_data_796_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_nbuckets_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_797_ = lean_array_get_size(v_data_796_);
v___x_798_ = lean_unsigned_to_nat(2u);
v_nbuckets_799_ = lean_nat_mul(v___x_797_, v___x_798_);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_box(0);
v___x_802_ = lean_mk_array(v_nbuckets_799_, v___x_801_);
v___x_803_ = lean_array_propagate_mark(v_data_796_, v___x_802_);
v___x_804_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(v___x_800_, v_data_796_, v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(lean_object* v_m_805_, lean_object* v_a_806_, lean_object* v_b_807_){
_start:
{
lean_object* v_size_808_; lean_object* v_buckets_809_; lean_object* v___x_810_; uint64_t v___x_811_; uint64_t v___x_812_; uint64_t v___x_813_; uint64_t v_fold_814_; uint64_t v___x_815_; uint64_t v___x_816_; uint64_t v___x_817_; size_t v___x_818_; size_t v___x_819_; size_t v___x_820_; size_t v___x_821_; size_t v___x_822_; lean_object* v_bkt_823_; uint8_t v___x_824_; 
v_size_808_ = lean_ctor_get(v_m_805_, 0);
v_buckets_809_ = lean_ctor_get(v_m_805_, 1);
v___x_810_ = lean_array_get_size(v_buckets_809_);
v___x_811_ = lean_uint64_of_nat(v_a_806_);
v___x_812_ = 32ULL;
v___x_813_ = lean_uint64_shift_right(v___x_811_, v___x_812_);
v_fold_814_ = lean_uint64_xor(v___x_811_, v___x_813_);
v___x_815_ = 16ULL;
v___x_816_ = lean_uint64_shift_right(v_fold_814_, v___x_815_);
v___x_817_ = lean_uint64_xor(v_fold_814_, v___x_816_);
v___x_818_ = lean_uint64_to_usize(v___x_817_);
v___x_819_ = lean_usize_of_nat(v___x_810_);
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_sub(v___x_819_, v___x_820_);
v___x_822_ = lean_usize_land(v___x_818_, v___x_821_);
v_bkt_823_ = lean_array_uget_borrowed(v_buckets_809_, v___x_822_);
v___x_824_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_806_, v_bkt_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_845_; 
lean_inc_ref(v_buckets_809_);
lean_inc(v_size_808_);
v_isSharedCheck_845_ = !lean_is_exclusive(v_m_805_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; lean_object* v_unused_847_; 
v_unused_846_ = lean_ctor_get(v_m_805_, 1);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_m_805_, 0);
lean_dec(v_unused_847_);
v___x_826_ = v_m_805_;
v_isShared_827_ = v_isSharedCheck_845_;
goto v_resetjp_825_;
}
else
{
lean_dec(v_m_805_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_845_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v_size_x27_829_; lean_object* v___x_830_; lean_object* v_buckets_x27_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_828_ = lean_unsigned_to_nat(1u);
v_size_x27_829_ = lean_nat_add(v_size_808_, v___x_828_);
lean_dec(v_size_808_);
lean_inc(v_bkt_823_);
v___x_830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_830_, 0, v_a_806_);
lean_ctor_set(v___x_830_, 1, v_b_807_);
lean_ctor_set(v___x_830_, 2, v_bkt_823_);
v_buckets_x27_831_ = lean_array_uset(v_buckets_809_, v___x_822_, v___x_830_);
v___x_832_ = lean_unsigned_to_nat(4u);
v___x_833_ = lean_nat_mul(v_size_x27_829_, v___x_832_);
v___x_834_ = lean_unsigned_to_nat(3u);
v___x_835_ = lean_nat_div(v___x_833_, v___x_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_array_get_size(v_buckets_x27_831_);
v___x_837_ = lean_nat_dec_le(v___x_835_, v___x_836_);
lean_dec(v___x_835_);
if (v___x_837_ == 0)
{
lean_object* v_val_838_; lean_object* v___x_840_; 
v_val_838_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(v_buckets_x27_831_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v_val_838_);
lean_ctor_set(v___x_826_, 0, v_size_x27_829_);
v___x_840_ = v___x_826_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_size_x27_829_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_val_838_);
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
lean_object* v___x_843_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v_buckets_x27_831_);
lean_ctor_set(v___x_826_, 0, v_size_x27_829_);
v___x_843_ = v___x_826_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_size_x27_829_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_buckets_x27_831_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
lean_dec(v_b_807_);
lean_dec(v_a_806_);
return v_m_805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_as_851_, size_t v_sz_852_, size_t v_i_853_, lean_object* v_b_854_){
_start:
{
lean_object* v_a_857_; uint8_t v___x_861_; 
v___x_861_ = lean_usize_dec_lt(v_i_853_, v_sz_852_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v_b_854_);
return v___x_862_;
}
else
{
lean_object* v_snd_863_; lean_object* v_snd_864_; lean_object* v_snd_865_; lean_object* v_fst_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_950_; 
v_snd_863_ = lean_ctor_get(v_b_854_, 1);
lean_inc(v_snd_863_);
v_snd_864_ = lean_ctor_get(v_snd_863_, 1);
lean_inc(v_snd_864_);
v_snd_865_ = lean_ctor_get(v_snd_864_, 1);
lean_inc(v_snd_865_);
v_fst_866_ = lean_ctor_get(v_b_854_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_b_854_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_b_854_, 1);
lean_dec(v_unused_951_);
v___x_868_ = v_b_854_;
v_isShared_869_ = v_isSharedCheck_950_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_fst_866_);
lean_dec(v_b_854_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_950_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_fst_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_948_; 
v_fst_870_ = lean_ctor_get(v_snd_863_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_snd_863_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_snd_863_, 1);
lean_dec(v_unused_949_);
v___x_872_ = v_snd_863_;
v_isShared_873_ = v_isSharedCheck_948_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_fst_870_);
lean_dec(v_snd_863_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_948_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_fst_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_946_; 
v_fst_874_ = lean_ctor_get(v_snd_864_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v_snd_864_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v_snd_864_, 1);
lean_dec(v_unused_947_);
v___x_876_ = v_snd_864_;
v_isShared_877_ = v_isSharedCheck_946_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_fst_874_);
lean_dec(v_snd_864_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_946_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_array_878_; lean_object* v_start_879_; lean_object* v_stop_880_; uint8_t v___x_881_; 
v_array_878_ = lean_ctor_get(v_snd_865_, 0);
v_start_879_ = lean_ctor_get(v_snd_865_, 1);
v_stop_880_ = lean_ctor_get(v_snd_865_, 2);
v___x_881_ = lean_nat_dec_lt(v_start_879_, v_stop_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_883_; 
if (v_isShared_877_ == 0)
{
v___x_883_ = v___x_876_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_fst_874_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_snd_865_);
v___x_883_ = v_reuseFailAlloc_891_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_883_);
v___x_885_ = v___x_872_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_fst_870_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_883_);
v___x_885_ = v_reuseFailAlloc_890_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_885_);
v___x_887_ = v___x_868_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_fst_866_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_889_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
}
}
}
else
{
lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_942_; 
lean_inc(v_stop_880_);
lean_inc(v_start_879_);
lean_inc_ref(v_array_878_);
v_isSharedCheck_942_ = !lean_is_exclusive(v_snd_865_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; lean_object* v_unused_945_; 
v_unused_943_ = lean_ctor_get(v_snd_865_, 2);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_snd_865_, 1);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_snd_865_, 0);
lean_dec(v_unused_945_);
v___x_893_ = v_snd_865_;
v_isShared_894_ = v_isSharedCheck_942_;
goto v_resetjp_892_;
}
else
{
lean_dec(v_snd_865_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_942_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_a_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v_a_895_ = lean_array_uget_borrowed(v_as_851_, v_i_853_);
v___x_896_ = lean_array_fget(v_array_878_, v_start_879_);
v___x_897_ = lean_unsigned_to_nat(1u);
v___x_898_ = lean_nat_add(v_start_879_, v___x_897_);
lean_dec(v_start_879_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v___x_898_);
v___x_900_ = v___x_893_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_array_878_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_stop_880_);
v___x_900_ = v_reuseFailAlloc_941_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
uint8_t v___x_911_; 
v___x_911_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_fst_866_, v_a_895_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Json_getNat_x3f(v___x_896_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_dec_ref_known(v___x_912_, 1);
goto v___jp_901_;
}
else
{
lean_object* v_a_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = lean_array_get_size(v_a_848_);
v___x_915_ = lean_nat_dec_lt(v_a_895_, v___x_914_);
if (v___x_915_ == 0)
{
lean_dec(v_a_913_);
goto v___jp_901_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_array_fget_borrowed(v_a_848_, v_a_895_);
lean_inc(v___x_916_);
v___x_917_ = l_Lean_Json_getNat_x3f(v___x_916_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_dec_ref_known(v___x_917_, 1);
lean_dec(v_a_913_);
goto v___jp_901_;
}
else
{
lean_object* v_a_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
v___x_919_ = lean_array_get_size(v_a_849_);
v___x_920_ = lean_nat_dec_lt(v_a_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_dec(v_a_918_);
lean_dec(v_a_913_);
goto v___jp_901_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_array_fget_borrowed(v_a_849_, v_a_918_);
lean_dec(v_a_918_);
lean_inc(v___x_921_);
v___x_922_ = l_Lean_Json_getNat_x3f(v___x_921_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_dec_ref_known(v___x_922_, 1);
lean_dec(v_a_913_);
goto v___jp_901_;
}
else
{
lean_object* v_a_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
v___x_924_ = lean_array_get_size(v_a_850_);
v___x_925_ = lean_nat_dec_lt(v_a_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_dec(v_a_923_);
lean_dec(v_a_913_);
goto v___jp_901_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_del_object(v___x_876_);
lean_del_object(v___x_872_);
lean_del_object(v___x_868_);
v___x_926_ = lean_box(0);
lean_inc_n(v_a_895_, 2);
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(v_fst_866_, v_a_895_, v___x_926_);
v___x_928_ = lean_unsigned_to_nat(2u);
v___x_929_ = lean_mk_empty_array_with_capacity(v___x_928_);
v___x_930_ = lean_array_push(v___x_929_, v_a_923_);
v___x_931_ = lean_array_push(v___x_930_, v_a_913_);
v___x_932_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(v___x_931_);
v___x_933_ = lean_array_push(v_fst_870_, v___x_932_);
v___x_934_ = lean_array_push(v_fst_874_, v_a_895_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_900_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_933_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_927_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v_a_857_ = v___x_937_;
goto v___jp_856_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v___x_896_);
lean_del_object(v___x_876_);
lean_del_object(v___x_872_);
lean_del_object(v___x_868_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_fst_874_);
lean_ctor_set(v___x_938_, 1, v___x_900_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_fst_870_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v_fst_866_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v_a_857_ = v___x_940_;
goto v___jp_856_;
}
v___jp_901_:
{
lean_object* v___x_903_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___x_900_);
v___x_903_ = v___x_876_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_fst_874_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v___x_900_);
v___x_903_ = v_reuseFailAlloc_910_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_905_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_903_);
v___x_905_ = v___x_872_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_fst_870_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v___x_903_);
v___x_905_ = v_reuseFailAlloc_909_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_907_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___x_905_);
v___x_907_ = v___x_868_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_fst_866_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
v_a_857_ = v___x_907_;
goto v___jp_856_;
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
v___jp_856_:
{
size_t v___x_858_; size_t v___x_859_; 
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_add(v_i_853_, v___x_858_);
v_i_853_ = v___x_859_;
v_b_854_ = v_a_857_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9___boxed(lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_as_955_, lean_object* v_sz_956_, lean_object* v_i_957_, lean_object* v_b_958_, lean_object* v___y_959_){
_start:
{
size_t v_sz_boxed_960_; size_t v_i_boxed_961_; lean_object* v_res_962_; 
v_sz_boxed_960_ = lean_unbox_usize(v_sz_956_);
lean_dec(v_sz_956_);
v_i_boxed_961_ = lean_unbox_usize(v_i_957_);
lean_dec(v_i_957_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(v_a_952_, v_a_953_, v_a_954_, v_as_955_, v_sz_boxed_960_, v_i_boxed_961_, v_b_958_);
lean_dec_ref(v_as_955_);
lean_dec_ref(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_962_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_box(0);
v___x_973_ = lean_unsigned_to_nat(16u);
v___x_974_ = lean_mk_array(v___x_973_, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8);
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(lean_object* v_a_978_, lean_object* v_as_979_, size_t v_sz_980_, size_t v_i_981_, lean_object* v_b_982_){
_start:
{
uint8_t v___x_984_; 
v___x_984_ = lean_usize_dec_lt(v_i_981_, v_sz_980_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v_b_982_);
return v___x_985_;
}
else
{
lean_object* v_fst_986_; lean_object* v_snd_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1116_; 
v_fst_986_ = lean_ctor_get(v_b_982_, 0);
v_snd_987_ = lean_ctor_get(v_b_982_, 1);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_b_982_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_989_ = v_b_982_;
v_isShared_990_ = v_isSharedCheck_1116_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_snd_987_);
lean_inc(v_fst_986_);
lean_dec(v_b_982_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1116_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__0));
v_a_993_ = lean_array_uget_borrowed(v_as_979_, v_i_981_);
v___x_994_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__1));
lean_inc(v_a_993_);
v___x_995_ = l_Lean_Json_getObjVal_x3f(v_a_993_, v___x_994_);
v___x_996_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_995_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v___x_998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2));
lean_inc(v_a_993_);
v___x_999_ = l_Lean_Json_getObjVal_x3f(v_a_993_, v___x_998_);
v___x_1000_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_999_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__3));
lean_inc(v_a_993_);
v___x_1003_ = l_Lean_Json_getObjVal_x3f(v_a_993_, v___x_1002_);
v___x_1004_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1003_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__4));
lean_inc(v_a_997_);
v___x_1007_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_a_997_, v___x_1006_);
v___x_1008_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__5));
v___x_1011_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_997_, v___x_1010_);
v___x_1012_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1011_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__6));
v___x_1015_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_1001_, v___x_1014_);
v___x_1016_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1015_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__7));
v___x_1019_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_1005_, v___x_1018_);
v___x_1020_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1019_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9);
v___x_1023_ = lean_array_get_size(v_a_1013_);
v___x_1024_ = l_Array_toSubarray___redArg(v_a_1013_, v___x_991_, v___x_1023_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v___x_1024_);
lean_ctor_set(v___x_989_, 0, v___x_992_);
v___x_1026_ = v___x_989_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; size_t v_sz_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_992_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1022_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v_sz_1029_ = lean_array_size(v_a_1009_);
v___x_1030_ = ((size_t)0ULL);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(v_a_1017_, v_a_1021_, v_a_978_, v_a_1009_, v_sz_1029_, v___x_1030_, v___x_1028_);
lean_dec(v_a_1009_);
lean_dec(v_a_1021_);
lean_dec(v_a_1017_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v_snd_1033_; lean_object* v_snd_1034_; lean_object* v_fst_1035_; lean_object* v_fst_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1049_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v_snd_1033_ = lean_ctor_get(v_a_1032_, 1);
lean_inc(v_snd_1033_);
lean_dec(v_a_1032_);
v_snd_1034_ = lean_ctor_get(v_snd_1033_, 1);
lean_inc(v_snd_1034_);
v_fst_1035_ = lean_ctor_get(v_snd_1033_, 0);
lean_inc(v_fst_1035_);
lean_dec(v_snd_1033_);
v_fst_1036_ = lean_ctor_get(v_snd_1034_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_snd_1034_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v_snd_1034_, 1);
lean_dec(v_unused_1050_);
v___x_1038_ = v_snd_1034_;
v_isShared_1039_ = v_isSharedCheck_1049_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_fst_1036_);
lean_dec(v_snd_1034_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1049_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1040_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_fst_1035_);
v___x_1041_ = lean_array_push(v_fst_986_, v___x_1040_);
v___x_1042_ = lean_array_push(v_snd_987_, v_fst_1036_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v___x_1042_);
lean_ctor_set(v___x_1038_, 0, v___x_1041_);
v___x_1044_ = v___x_1038_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
size_t v___x_1045_; size_t v___x_1046_; 
v___x_1045_ = ((size_t)1ULL);
v___x_1046_ = lean_usize_add(v_i_981_, v___x_1045_);
v_i_981_ = v___x_1046_;
v_b_982_ = v___x_1044_;
goto _start;
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
v_a_1051_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1031_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1031_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v_a_1017_);
lean_dec(v_a_1013_);
lean_dec(v_a_1009_);
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
v_a_1060_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1020_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1020_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_a_1013_);
lean_dec(v_a_1009_);
lean_dec(v_a_1005_);
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
v_a_1068_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1016_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1016_);
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
lean_dec(v_a_1009_);
lean_dec(v_a_1005_);
lean_dec(v_a_1001_);
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
v_a_1076_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1012_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1012_);
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
lean_dec(v_a_1005_);
lean_dec(v_a_1001_);
lean_dec(v_a_997_);
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
v_a_1084_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1008_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1008_);
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
lean_dec(v_a_1001_);
lean_dec(v_a_997_);
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
v_a_1092_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1004_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1004_);
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
lean_dec(v_a_997_);
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
v_a_1100_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1000_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1000_);
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
lean_del_object(v___x_989_);
lean_dec(v_snd_987_);
lean_dec(v_fst_986_);
v_a_1108_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_996_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_996_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___boxed(lean_object* v_a_1117_, lean_object* v_as_1118_, lean_object* v_sz_1119_, lean_object* v_i_1120_, lean_object* v_b_1121_, lean_object* v___y_1122_){
_start:
{
size_t v_sz_boxed_1123_; size_t v_i_boxed_1124_; lean_object* v_res_1125_; 
v_sz_boxed_1123_ = lean_unbox_usize(v_sz_1119_);
lean_dec(v_sz_1119_);
v_i_boxed_1124_ = lean_unbox_usize(v_i_1120_);
lean_dec(v_i_1120_);
v_res_1125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(v_a_1117_, v_as_1118_, v_sz_boxed_1123_, v_i_boxed_1124_, v_b_1121_);
lean_dec_ref(v_as_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(size_t v_sz_1126_, size_t v_i_1127_, lean_object* v_bs_1128_){
_start:
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_usize_dec_lt(v_i_1127_, v_sz_1126_);
if (v___x_1129_ == 0)
{
return v_bs_1128_;
}
else
{
lean_object* v_v_1130_; lean_object* v___x_1131_; lean_object* v_bs_x27_1132_; lean_object* v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; lean_object* v___x_1136_; 
v_v_1130_ = lean_array_uget(v_bs_1128_, v_i_1127_);
v___x_1131_ = lean_unsigned_to_nat(0u);
v_bs_x27_1132_ = lean_array_uset(v_bs_1128_, v_i_1127_, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_v_1130_);
v___x_1134_ = ((size_t)1ULL);
v___x_1135_ = lean_usize_add(v_i_1127_, v___x_1134_);
v___x_1136_ = lean_array_uset(v_bs_x27_1132_, v_i_1127_, v___x_1133_);
v_i_1127_ = v___x_1135_;
v_bs_1128_ = v___x_1136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2___boxed(lean_object* v_sz_1138_, lean_object* v_i_1139_, lean_object* v_bs_1140_){
_start:
{
size_t v_sz_boxed_1141_; size_t v_i_boxed_1142_; lean_object* v_res_1143_; 
v_sz_boxed_1141_ = lean_unbox_usize(v_sz_1138_);
lean_dec(v_sz_1138_);
v_i_boxed_1142_ = lean_unbox_usize(v_i_1139_);
lean_dec(v_i_1139_);
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(v_sz_boxed_1141_, v_i_boxed_1142_, v_bs_1140_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(lean_object* v_a_1144_){
_start:
{
size_t v_sz_1145_; size_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_sz_1145_ = lean_array_size(v_a_1144_);
v___x_1146_ = ((size_t)0ULL);
v___x_1147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(v_sz_1145_, v___x_1146_, v_a_1144_);
v___x_1148_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(size_t v_sz_1151_, size_t v_i_1152_, lean_object* v_bs_1153_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_lt(v_i_1152_, v_sz_1151_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_bs_1153_);
return v___x_1156_;
}
else
{
lean_object* v_v_1157_; lean_object* v___x_1158_; lean_object* v_bs_x27_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_v_1157_ = lean_array_uget(v_bs_1153_, v_i_1152_);
v___x_1158_ = lean_unsigned_to_nat(0u);
v_bs_x27_1159_ = lean_array_uset(v_bs_1153_, v_i_1152_, v___x_1158_);
v___x_1160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__0));
lean_inc(v_v_1157_);
v___x_1161_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_v_1157_, v___x_1160_);
v___x_1162_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1161_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__1));
v___x_1165_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_v_1157_, v___x_1164_);
v___x_1166_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1165_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; lean_object* v___x_1175_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v___x_1168_ = lean_unsigned_to_nat(2u);
v___x_1169_ = lean_mk_empty_array_with_capacity(v___x_1168_);
v___x_1170_ = lean_array_push(v___x_1169_, v_a_1163_);
v___x_1171_ = lean_array_push(v___x_1170_, v_a_1167_);
v___x_1172_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(v___x_1171_);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_add(v_i_1152_, v___x_1173_);
v___x_1175_ = lean_array_uset(v_bs_x27_1159_, v_i_1152_, v___x_1172_);
v_i_1152_ = v___x_1174_;
v_bs_1153_ = v___x_1175_;
goto _start;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec(v_a_1163_);
lean_dec_ref(v_bs_x27_1159_);
v_a_1177_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1166_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1166_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v_bs_x27_1159_);
lean_dec(v_v_1157_);
v_a_1185_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1162_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1162_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___boxed(lean_object* v_sz_1193_, lean_object* v_i_1194_, lean_object* v_bs_1195_, lean_object* v___y_1196_){
_start:
{
size_t v_sz_boxed_1197_; size_t v_i_boxed_1198_; lean_object* v_res_1199_; 
v_sz_boxed_1197_ = lean_unbox_usize(v_sz_1193_);
lean_dec(v_sz_1193_);
v_i_boxed_1198_ = lean_unbox_usize(v_i_1194_);
lean_dec(v_i_1194_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(v_sz_boxed_1197_, v_i_boxed_1198_, v_bs_1195_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(lean_object* v_profile_1206_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__0));
lean_inc(v_profile_1206_);
v___x_1209_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1206_, v___x_1208_);
v___x_1210_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1209_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; size_t v_sz_1212_; size_t v___x_1213_; lean_object* v___x_1214_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc_n(v_a_1211_, 2);
lean_dec_ref_known(v___x_1210_, 1);
v_sz_1212_ = lean_array_size(v_a_1211_);
v___x_1213_ = ((size_t)0ULL);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(v_sz_1212_, v___x_1213_, v_a_1211_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1));
v___x_1217_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1206_, v___x_1216_);
v___x_1218_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1217_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; size_t v_sz_1221_; lean_object* v___x_1222_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v___x_1220_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__2));
v_sz_1221_ = lean_array_size(v_a_1219_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(v_a_1211_, v_a_1219_, v_sz_1221_, v___x_1213_, v___x_1220_);
lean_dec(v_a_1219_);
lean_dec(v_a_1211_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1249_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1249_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1249_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_fst_1227_; lean_object* v_snd_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1248_; 
v_fst_1227_ = lean_ctor_get(v_a_1223_, 0);
v_snd_1228_ = lean_ctor_get(v_a_1223_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_a_1223_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1230_ = v_a_1223_;
v_isShared_1231_ = v_isSharedCheck_1248_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_snd_1228_);
lean_inc(v_fst_1227_);
lean_dec(v_a_1223_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1248_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1232_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__3));
v___x_1233_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1233_, 0, v_a_1215_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1233_);
lean_ctor_set(v___x_1230_, 0, v___x_1232_);
v___x_1235_ = v___x_1230_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1236_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4));
v___x_1237_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1237_, 0, v_fst_1227_);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1238_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1235_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_Json_mkObj(v___x_1241_);
lean_dec_ref_known(v___x_1241_, 2);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v_snd_1228_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1243_);
v___x_1245_ = v___x_1225_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_a_1215_);
v_a_1250_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1222_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1222_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_a_1215_);
lean_dec(v_a_1211_);
v_a_1258_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1218_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1218_);
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
lean_dec(v_a_1211_);
lean_dec(v_profile_1206_);
v_a_1266_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1214_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1214_);
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
lean_dec(v_profile_1206_);
v_a_1274_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1210_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1210_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___boxed(lean_object* v_profile_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(v_profile_1282_);
return v_res_1284_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(lean_object* v_00_u03b2_1285_, lean_object* v_m_1286_, lean_object* v_a_1287_){
_start:
{
uint8_t v___x_1288_; 
v___x_1288_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_m_1286_, v_a_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___boxed(lean_object* v_00_u03b2_1289_, lean_object* v_m_1290_, lean_object* v_a_1291_){
_start:
{
uint8_t v_res_1292_; lean_object* v_r_1293_; 
v_res_1292_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(v_00_u03b2_1289_, v_m_1290_, v_a_1291_);
lean_dec(v_a_1291_);
lean_dec_ref(v_m_1290_);
v_r_1293_ = lean_box(v_res_1292_);
return v_r_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7(lean_object* v_00_u03b2_1294_, lean_object* v_m_1295_, lean_object* v_a_1296_, lean_object* v_b_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(v_m_1295_, v_a_1296_, v_b_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(lean_object* v_00_u03b2_1299_, lean_object* v_a_1300_, lean_object* v_x_1301_){
_start:
{
uint8_t v___x_1302_; 
v___x_1302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_1300_, v_x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1303_, lean_object* v_a_1304_, lean_object* v_x_1305_){
_start:
{
uint8_t v_res_1306_; lean_object* v_r_1307_; 
v_res_1306_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(v_00_u03b2_1303_, v_a_1304_, v_x_1305_);
lean_dec(v_x_1305_);
lean_dec(v_a_1304_);
v_r_1307_ = lean_box(v_res_1306_);
return v_r_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11(lean_object* v_00_u03b2_1308_, lean_object* v_data_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(v_data_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14(lean_object* v_00_u03b2_1311_, lean_object* v_i_1312_, lean_object* v_source_1313_, lean_object* v_target_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(v_i_1312_, v_source_1313_, v_target_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18(lean_object* v_00_u03b2_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(v_x_1317_, v_x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(size_t v_sz_1320_, size_t v_i_1321_, lean_object* v_bs_1322_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_usize_dec_lt(v_i_1321_, v_sz_1320_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_bs_1322_);
return v___x_1324_;
}
else
{
lean_object* v_v_1325_; lean_object* v___x_1326_; 
v_v_1325_ = lean_array_uget_borrowed(v_bs_1322_, v_i_1321_);
lean_inc(v_v_1325_);
v___x_1326_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(v_v_1325_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_bs_1322_);
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1336_; lean_object* v_bs_x27_1337_; size_t v___x_1338_; size_t v___x_1339_; lean_object* v___x_1340_; 
v_a_1335_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1336_ = lean_unsigned_to_nat(0u);
v_bs_x27_1337_ = lean_array_uset(v_bs_1322_, v_i_1321_, v___x_1336_);
v___x_1338_ = ((size_t)1ULL);
v___x_1339_ = lean_usize_add(v_i_1321_, v___x_1338_);
v___x_1340_ = lean_array_uset(v_bs_x27_1337_, v_i_1321_, v_a_1335_);
v_i_1321_ = v___x_1339_;
v_bs_1322_ = v___x_1340_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1342_, lean_object* v_i_1343_, lean_object* v_bs_1344_){
_start:
{
size_t v_sz_boxed_1345_; size_t v_i_boxed_1346_; lean_object* v_res_1347_; 
v_sz_boxed_1345_ = lean_unbox_usize(v_sz_1342_);
lean_dec(v_sz_1342_);
v_i_boxed_1346_ = lean_unbox_usize(v_i_1343_);
lean_dec(v_i_1343_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(v_sz_boxed_1345_, v_i_boxed_1346_, v_bs_1344_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0(lean_object* v_x_1348_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 4)
{
lean_object* v_elems_1349_; size_t v_sz_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v_elems_1349_ = lean_ctor_get(v_x_1348_, 0);
lean_inc_ref(v_elems_1349_);
lean_dec_ref_known(v_x_1348_, 1);
v_sz_1350_ = lean_array_size(v_elems_1349_);
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(v_sz_1350_, v___x_1351_, v_elems_1349_);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1353_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_1354_ = lean_unsigned_to_nat(80u);
v___x_1355_ = l_Lean_Json_pretty(v_x_1348_, v___x_1354_);
v___x_1356_ = lean_string_append(v___x_1353_, v___x_1355_);
lean_dec_ref(v___x_1355_);
v___x_1357_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_1358_ = lean_string_append(v___x_1356_, v___x_1357_);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(lean_object* v_j_1360_, lean_object* v_k_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = l_Lean_Json_getObjValD(v_j_1360_, v_k_1361_);
v___x_1363_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0(v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0___boxed(lean_object* v_j_1364_, lean_object* v_k_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(v_j_1364_, v_k_1365_);
lean_dec_ref(v_k_1365_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(size_t v_sz_1367_, size_t v_i_1368_, lean_object* v_bs_1369_){
_start:
{
uint8_t v___x_1370_; 
v___x_1370_ = lean_usize_dec_lt(v_i_1368_, v_sz_1367_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_bs_1369_);
return v___x_1371_;
}
else
{
lean_object* v_v_1372_; lean_object* v___x_1373_; 
v_v_1372_ = lean_array_uget_borrowed(v_bs_1369_, v_i_1368_);
lean_inc(v_v_1372_);
v___x_1373_ = l_Lean_Json_getStr_x3f(v_v_1372_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec_ref(v_bs_1369_);
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1383_; lean_object* v_bs_x27_1384_; size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_1387_; 
v_a_1382_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1383_ = lean_unsigned_to_nat(0u);
v_bs_x27_1384_ = lean_array_uset(v_bs_1369_, v_i_1368_, v___x_1383_);
v___x_1385_ = ((size_t)1ULL);
v___x_1386_ = lean_usize_add(v_i_1368_, v___x_1385_);
v___x_1387_ = lean_array_uset(v_bs_x27_1384_, v_i_1368_, v_a_1382_);
v_i_1368_ = v___x_1386_;
v_bs_1369_ = v___x_1387_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_1389_, lean_object* v_i_1390_, lean_object* v_bs_1391_){
_start:
{
size_t v_sz_boxed_1392_; size_t v_i_boxed_1393_; lean_object* v_res_1394_; 
v_sz_boxed_1392_ = lean_unbox_usize(v_sz_1389_);
lean_dec(v_sz_1389_);
v_i_boxed_1393_ = lean_unbox_usize(v_i_1390_);
lean_dec(v_i_1390_);
v_res_1394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(v_sz_boxed_1392_, v_i_boxed_1393_, v_bs_1391_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2(lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1395_) == 4)
{
lean_object* v_elems_1396_; size_t v_sz_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v_elems_1396_ = lean_ctor_get(v_x_1395_, 0);
lean_inc_ref(v_elems_1396_);
lean_dec_ref_known(v_x_1395_, 1);
v_sz_1397_ = lean_array_size(v_elems_1396_);
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(v_sz_1397_, v___x_1398_, v_elems_1396_);
return v___x_1399_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1400_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_1401_ = lean_unsigned_to_nat(80u);
v___x_1402_ = l_Lean_Json_pretty(v_x_1395_, v___x_1401_);
v___x_1403_ = lean_string_append(v___x_1400_, v___x_1402_);
lean_dec_ref(v___x_1402_);
v___x_1404_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(lean_object* v_j_1407_, lean_object* v_k_1408_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = l_Lean_Json_getObjValD(v_j_1407_, v_k_1408_);
v___x_1410_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2(v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1___boxed(lean_object* v_j_1411_, lean_object* v_k_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(v_j_1411_, v_k_1412_);
lean_dec_ref(v_k_1412_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(lean_object* v_as_1415_, size_t v_sz_1416_, size_t v_i_1417_, lean_object* v_b_1418_){
_start:
{
lean_object* v_a_1421_; uint8_t v___x_1425_; 
v___x_1425_ = lean_usize_dec_lt(v_i_1417_, v_sz_1416_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_b_1418_);
return v___x_1426_;
}
else
{
lean_object* v_snd_1427_; lean_object* v_snd_1428_; lean_object* v_fst_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1489_; 
v_snd_1427_ = lean_ctor_get(v_b_1418_, 1);
lean_inc(v_snd_1427_);
v_snd_1428_ = lean_ctor_get(v_snd_1427_, 1);
lean_inc(v_snd_1428_);
v_fst_1429_ = lean_ctor_get(v_b_1418_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_b_1418_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v_b_1418_, 1);
lean_dec(v_unused_1490_);
v___x_1431_ = v_b_1418_;
v_isShared_1432_ = v_isSharedCheck_1489_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_fst_1429_);
lean_dec(v_b_1418_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1489_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_fst_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1487_; 
v_fst_1433_ = lean_ctor_get(v_snd_1427_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_snd_1427_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v_snd_1427_, 1);
lean_dec(v_unused_1488_);
v___x_1435_ = v_snd_1427_;
v_isShared_1436_ = v_isSharedCheck_1487_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_fst_1433_);
lean_dec(v_snd_1427_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1487_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_array_1437_; lean_object* v_start_1438_; lean_object* v_stop_1439_; uint8_t v___x_1440_; 
v_array_1437_ = lean_ctor_get(v_snd_1428_, 0);
v_start_1438_ = lean_ctor_get(v_snd_1428_, 1);
v_stop_1439_ = lean_ctor_get(v_snd_1428_, 2);
v___x_1440_ = lean_nat_dec_lt(v_start_1438_, v_stop_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1442_; 
if (v_isShared_1436_ == 0)
{
v___x_1442_ = v___x_1435_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_fst_1433_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_snd_1428_);
v___x_1442_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1442_);
v___x_1444_ = v___x_1431_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_fst_1429_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
}
}
else
{
lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1483_; 
lean_inc(v_stop_1439_);
lean_inc(v_start_1438_);
lean_inc_ref(v_array_1437_);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_snd_1428_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; 
v_unused_1484_ = lean_ctor_get(v_snd_1428_, 2);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_snd_1428_, 1);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_snd_1428_, 0);
lean_dec(v_unused_1486_);
v___x_1449_ = v_snd_1428_;
v_isShared_1450_ = v_isSharedCheck_1483_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v_snd_1428_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1483_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v_a_1451_ = lean_array_uget_borrowed(v_as_1415_, v_i_1417_);
v___x_1452_ = lean_array_fget(v_array_1437_, v_start_1438_);
v___x_1453_ = lean_unsigned_to_nat(1u);
v___x_1454_ = lean_nat_add(v_start_1438_, v___x_1453_);
lean_dec(v_start_1438_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 1, v___x_1454_);
v___x_1456_ = v___x_1449_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_array_1437_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_stop_1439_);
v___x_1456_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___y_1458_; lean_object* v___y_1469_; lean_object* v___x_1479_; 
lean_inc(v___x_1452_);
v___x_1479_ = l_Lean_Json_getStr_x3f(v___x_1452_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec_ref_known(v___x_1479_, 1);
v___x_1480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___closed__0));
v___x_1481_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v___x_1452_, v___x_1480_);
v___y_1469_ = v___x_1481_;
goto v___jp_1468_;
}
else
{
lean_dec(v___x_1452_);
v___y_1469_ = v___x_1479_;
goto v___jp_1468_;
}
v___jp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1459_ = lean_array_get_size(v_fst_1433_);
v___x_1460_ = lean_array_fset(v_fst_1429_, v_a_1451_, v___x_1459_);
v___x_1461_ = lean_array_push(v_fst_1433_, v___y_1458_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___x_1456_);
lean_ctor_set(v___x_1435_, 0, v___x_1461_);
v___x_1463_ = v___x_1435_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___x_1456_);
v___x_1463_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1463_);
lean_ctor_set(v___x_1431_, 0, v___x_1460_);
v___x_1465_ = v___x_1431_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
v_a_1421_ = v___x_1465_;
goto v___jp_1420_;
}
}
}
v___jp_1468_:
{
if (lean_obj_tag(v___y_1469_) == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec_ref_known(v___y_1469_, 1);
lean_del_object(v___x_1435_);
lean_del_object(v___x_1431_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_fst_1433_);
lean_ctor_set(v___x_1470_, 1, v___x_1456_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v_fst_1429_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v_a_1421_ = v___x_1471_;
goto v___jp_1420_;
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v_a_1472_ = lean_ctor_get(v___y_1469_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___y_1469_, 1);
v___x_1473_ = lean_array_get_size(v_fst_1429_);
v___x_1474_ = lean_nat_dec_lt(v_a_1451_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec(v_a_1472_);
lean_del_object(v___x_1435_);
lean_del_object(v___x_1431_);
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v_fst_1433_);
lean_ctor_set(v___x_1475_, 1, v___x_1456_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_fst_1429_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v_a_1421_ = v___x_1476_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1477_; 
lean_inc(v_a_1472_);
v___x_1477_ = l_Lean_Name_Demangle_demangleSymbol(v_a_1472_);
if (lean_obj_tag(v___x_1477_) == 0)
{
v___y_1458_ = v_a_1472_;
goto v___jp_1457_;
}
else
{
lean_object* v_val_1478_; 
lean_dec(v_a_1472_);
v_val_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_val_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___y_1458_ = v_val_1478_;
goto v___jp_1457_;
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
v___jp_1420_:
{
size_t v___x_1422_; size_t v___x_1423_; 
v___x_1422_ = ((size_t)1ULL);
v___x_1423_ = lean_usize_add(v_i_1417_, v___x_1422_);
v_i_1417_ = v___x_1423_;
v_b_1418_ = v_a_1421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___boxed(lean_object* v_as_1491_, lean_object* v_sz_1492_, lean_object* v_i_1493_, lean_object* v_b_1494_, lean_object* v___y_1495_){
_start:
{
size_t v_sz_boxed_1496_; size_t v_i_boxed_1497_; lean_object* v_res_1498_; 
v_sz_boxed_1496_ = lean_unbox_usize(v_sz_1492_);
lean_dec(v_sz_1492_);
v_i_boxed_1497_ = lean_unbox_usize(v_i_1493_);
lean_dec(v_i_1493_);
v_res_1498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(v_as_1491_, v_sz_boxed_1496_, v_i_boxed_1497_, v_b_1494_);
lean_dec_ref(v_as_1491_);
return v_res_1498_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Array_instInhabited___redArg();
return v___x_1499_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__1));
v___x_1502_ = lean_mk_io_user_error(v___x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(lean_object* v_a_1505_, lean_object* v_funcMaps_1506_, size_t v_sz_1507_, size_t v_i_1508_, lean_object* v_bs_1509_){
_start:
{
uint8_t v___x_1511_; 
v___x_1511_ = lean_usize_dec_lt(v_i_1508_, v_sz_1507_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_bs_1509_);
return v___x_1512_;
}
else
{
lean_object* v___x_1513_; lean_object* v_v_1514_; lean_object* v___x_1515_; lean_object* v_bs_x27_1516_; lean_object* v_a_1518_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1513_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0);
v_v_1514_ = lean_array_uget(v_bs_1509_, v_i_1508_);
v___x_1515_ = lean_unsigned_to_nat(0u);
v_bs_x27_1516_ = lean_array_uset(v_bs_1509_, v_i_1508_, v___x_1515_);
v___x_1523_ = lean_usize_to_nat(v_i_1508_);
v___x_1524_ = lean_array_get_borrowed(v___x_1513_, v_a_1505_, v___x_1523_);
v___x_1525_ = lean_array_get_borrowed(v___x_1513_, v_funcMaps_1506_, v___x_1523_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_array_get_size(v___x_1524_);
v___x_1527_ = lean_array_get_size(v___x_1525_);
v___x_1528_ = lean_nat_dec_eq(v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec_ref(v_bs_x27_1516_);
lean_dec(v_v_1514_);
v___x_1529_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2);
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2));
lean_inc(v_v_1514_);
v___x_1532_ = l_Lean_Json_getObjVal_x3f(v_v_1514_, v___x_1531_);
v___x_1533_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1532_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc_n(v_a_1534_, 2);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__3));
v___x_1536_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_a_1534_, v___x_1535_);
v___x_1537_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1536_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v___x_1539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__4));
lean_inc(v_v_1514_);
v___x_1540_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(v_v_1514_, v___x_1539_);
v___x_1541_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1540_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; size_t v_sz_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
lean_inc(v___x_1524_);
v___x_1543_ = l_Array_toSubarray___redArg(v___x_1524_, v___x_1515_, v___x_1526_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_a_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_a_1538_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v_sz_1546_ = lean_array_size(v___x_1525_);
v___x_1547_ = ((size_t)0ULL);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(v___x_1525_, v_sz_1546_, v___x_1547_, v___x_1545_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v_snd_1550_; lean_object* v_fst_1551_; lean_object* v_fst_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v_snd_1550_ = lean_ctor_get(v_a_1549_, 1);
lean_inc(v_snd_1550_);
v_fst_1551_ = lean_ctor_get(v_a_1549_, 0);
lean_inc(v_fst_1551_);
lean_dec(v_a_1549_);
v_fst_1552_ = lean_ctor_get(v_snd_1550_, 0);
lean_inc(v_fst_1552_);
lean_dec(v_snd_1550_);
v___x_1553_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(v_fst_1551_);
v___x_1554_ = l_Lean_Json_setObjVal_x21(v_a_1534_, v___x_1535_, v___x_1553_);
v___x_1555_ = l_Lean_Json_setObjVal_x21(v_v_1514_, v___x_1531_, v___x_1554_);
v___x_1556_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(v_fst_1552_);
v___x_1557_ = l_Lean_Json_setObjVal_x21(v___x_1555_, v___x_1539_, v___x_1556_);
v_a_1518_ = v___x_1557_;
goto v___jp_1517_;
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v_a_1534_);
lean_dec_ref(v_bs_x27_1516_);
lean_dec(v_v_1514_);
v_a_1558_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1548_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1548_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v_a_1538_);
lean_dec(v_a_1534_);
lean_dec_ref(v_bs_x27_1516_);
lean_dec(v_v_1514_);
v_a_1566_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1541_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1541_);
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
lean_dec(v_a_1534_);
lean_dec_ref(v_bs_x27_1516_);
lean_dec(v_v_1514_);
v_a_1574_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1537_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1537_);
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
lean_dec(v_v_1514_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1582_; 
v_a_1582_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1533_, 1);
v_a_1518_ = v_a_1582_;
goto v___jp_1517_;
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec_ref(v_bs_x27_1516_);
v_a_1583_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1533_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1533_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
v___jp_1517_:
{
size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = lean_usize_add(v_i_1508_, v___x_1519_);
v___x_1521_ = lean_array_uset(v_bs_x27_1516_, v_i_1508_, v_a_1518_);
v_i_1508_ = v___x_1520_;
v_bs_1509_ = v___x_1521_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___boxed(lean_object* v_a_1591_, lean_object* v_funcMaps_1592_, lean_object* v_sz_1593_, lean_object* v_i_1594_, lean_object* v_bs_1595_, lean_object* v___y_1596_){
_start:
{
size_t v_sz_boxed_1597_; size_t v_i_boxed_1598_; lean_object* v_res_1599_; 
v_sz_boxed_1597_ = lean_unbox_usize(v_sz_1593_);
lean_dec(v_sz_1593_);
v_i_boxed_1598_ = lean_unbox_usize(v_i_1594_);
lean_dec(v_i_1594_);
v_res_1599_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1591_, v_funcMaps_1592_, v_sz_boxed_1597_, v_i_boxed_1598_, v_bs_1595_);
lean_dec_ref(v_funcMaps_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1599_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__1));
v___x_1603_ = lean_mk_io_user_error(v___x_1602_);
return v___x_1603_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__3));
v___x_1606_ = lean_mk_io_user_error(v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(lean_object* v_profile_1609_, lean_object* v_response_1610_, lean_object* v_funcMaps_1611_){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__0));
v___x_1614_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_response_1610_, v___x_1613_);
v___x_1615_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1614_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1695_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1695_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1695_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_array_get_size(v_a_1616_);
v___x_1622_ = lean_nat_dec_lt(v___x_1620_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
lean_dec(v_a_1616_);
lean_dec(v_profile_1609_);
v___x_1623_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2, &l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2);
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 1);
lean_ctor_set(v___x_1618_, 0, v___x_1623_);
v___x_1625_ = v___x_1618_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_del_object(v___x_1618_);
v___x_1627_ = lean_array_fget(v_a_1616_, v___x_1620_);
lean_dec(v_a_1616_);
v___x_1628_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4));
v___x_1629_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(v___x_1627_, v___x_1628_);
v___x_1630_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1629_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v___x_1632_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1));
lean_inc(v_profile_1609_);
v___x_1633_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1609_, v___x_1632_);
v___x_1634_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1633_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1678_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1678_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1678_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1644_ = lean_array_get_size(v_a_1631_);
v___x_1645_ = lean_array_get_size(v_a_1635_);
v___x_1646_ = lean_nat_dec_eq(v___x_1644_, v___x_1645_);
if (v___x_1646_ == 0)
{
lean_dec(v_a_1635_);
lean_dec(v_a_1631_);
lean_dec(v_profile_1609_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = lean_array_get_size(v_funcMaps_1611_);
v___x_1648_ = lean_nat_dec_eq(v___x_1647_, v___x_1645_);
if (v___x_1648_ == 0)
{
lean_dec(v_a_1635_);
lean_dec(v_a_1631_);
lean_dec(v_profile_1609_);
goto v___jp_1639_;
}
else
{
size_t v_sz_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
lean_del_object(v___x_1637_);
v_sz_1649_ = lean_array_size(v_a_1635_);
v___x_1650_ = ((size_t)0ULL);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1631_, v_funcMaps_1611_, v_sz_1649_, v___x_1650_, v_a_1635_);
lean_dec(v_a_1631_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1653_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__5));
lean_inc(v_profile_1609_);
v___x_1654_ = l_Lean_Json_getObjVal_x3f(v_profile_1609_, v___x_1653_);
v___x_1655_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1654_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1669_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1669_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1669_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1660_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_a_1652_);
v___x_1661_ = l_Lean_Json_setObjVal_x21(v_profile_1609_, v___x_1632_, v___x_1660_);
v___x_1662_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__6));
v___x_1663_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1663_, 0, v___x_1648_);
v___x_1664_ = l_Lean_Json_setObjVal_x21(v_a_1656_, v___x_1662_, v___x_1663_);
v___x_1665_ = l_Lean_Json_setObjVal_x21(v___x_1661_, v___x_1653_, v___x_1664_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1665_);
v___x_1667_ = v___x_1658_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
lean_dec(v_a_1652_);
lean_dec(v_profile_1609_);
return v___x_1655_;
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_profile_1609_);
v_a_1670_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1651_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1651_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
v___jp_1639_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4, &l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4);
if (v_isShared_1638_ == 0)
{
lean_ctor_set_tag(v___x_1637_, 1);
lean_ctor_set(v___x_1637_, 0, v___x_1640_);
v___x_1642_ = v___x_1637_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec(v_a_1631_);
lean_dec(v_profile_1609_);
v_a_1679_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1634_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1634_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_profile_1609_);
v_a_1687_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1630_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1630_);
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
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_profile_1609_);
v_a_1696_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1615_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1615_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___boxed(lean_object* v_profile_1704_, lean_object* v_response_1705_, lean_object* v_funcMaps_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(v_profile_1704_, v_response_1705_, v_funcMaps_1706_);
lean_dec_ref(v_funcMaps_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(lean_object* v_a_1709_, lean_object* v_funcMaps_1710_, lean_object* v_as_1711_, size_t v_sz_1712_, size_t v_i_1713_, lean_object* v_bs_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1709_, v_funcMaps_1710_, v_sz_1712_, v_i_1713_, v_bs_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___boxed(lean_object* v_a_1717_, lean_object* v_funcMaps_1718_, lean_object* v_as_1719_, lean_object* v_sz_1720_, lean_object* v_i_1721_, lean_object* v_bs_1722_, lean_object* v___y_1723_){
_start:
{
size_t v_sz_boxed_1724_; size_t v_i_boxed_1725_; lean_object* v_res_1726_; 
v_sz_boxed_1724_ = lean_unbox_usize(v_sz_1720_);
lean_dec(v_sz_1720_);
v_i_boxed_1725_ = lean_unbox_usize(v_i_1721_);
lean_dec(v_i_1721_);
v_res_1726_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(v_a_1717_, v_funcMaps_1718_, v_as_1719_, v_sz_boxed_1724_, v_i_boxed_1725_, v_bs_1722_);
lean_dec_ref(v_as_1719_);
lean_dec_ref(v_funcMaps_1718_);
lean_dec_ref(v_a_1717_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(lean_object* v_cfg_1727_, lean_object* v_proc_1728_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_io_process_child_kill(v_cfg_1727_, v_proc_1728_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v___x_1734_; 
lean_dec_ref_known(v___x_1733_, 1);
v___x_1734_ = lean_io_process_child_wait(v_cfg_1727_, v_proc_1728_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1742_; 
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1742_ == 0)
{
lean_object* v_unused_1743_; 
v_unused_1743_ = lean_ctor_get(v___x_1734_, 0);
lean_dec(v_unused_1743_);
v___x_1736_ = v___x_1734_;
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v___x_1734_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = lean_box(0);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
else
{
lean_dec_ref_known(v___x_1734_, 1);
goto v___jp_1730_;
}
}
else
{
if (lean_obj_tag(v___x_1733_) == 0)
{
return v___x_1733_;
}
else
{
lean_dec_ref_known(v___x_1733_, 1);
goto v___jp_1730_;
}
}
v___jp_1730_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe___boxed(lean_object* v_cfg_1744_, lean_object* v_proc_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v_cfg_1744_, v_proc_1745_);
lean_dec_ref(v_proc_1745_);
lean_dec_ref(v_cfg_1744_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(lean_object* v_as_1749_, lean_object* v_j_1750_){
_start:
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = lean_array_get_size(v_as_1749_);
v___x_1752_ = lean_nat_dec_lt(v_j_1750_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; 
lean_dec(v_j_1750_);
v___x_1753_ = lean_box(0);
return v___x_1753_;
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1754_ = lean_array_fget_borrowed(v_as_1749_, v_j_1750_);
v___x_1755_ = ((lean_object*)(l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0));
v___x_1756_ = lean_string_dec_eq(v___x_1754_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_unsigned_to_nat(1u);
v___x_1758_ = lean_nat_add(v_j_1750_, v___x_1757_);
lean_dec(v_j_1750_);
v_j_1750_ = v___x_1758_;
goto _start;
}
else
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_j_1750_);
return v___x_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___boxed(lean_object* v_as_1761_, lean_object* v_j_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(v_as_1761_, v_j_1762_);
lean_dec_ref(v_as_1761_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash(lean_object* v_args_1766_){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(v_args_1766_, v___x_1767_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash___closed__0));
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v_args_1766_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
return v___x_1770_;
}
else
{
lean_object* v_val_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_val_1771_ = lean_ctor_get(v___x_1768_, 0);
lean_inc_n(v_val_1771_, 2);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1772_ = l_Array_extract___redArg(v_args_1766_, v___x_1767_, v_val_1771_);
v___x_1773_ = lean_unsigned_to_nat(1u);
v___x_1774_ = lean_nat_add(v_val_1771_, v___x_1773_);
lean_dec(v_val_1771_);
v___x_1775_ = lean_array_get_size(v_args_1766_);
v___x_1776_ = l_Array_extract___redArg(v_args_1766_, v___x_1774_, v___x_1775_);
lean_dec_ref(v_args_1766_);
v___x_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1772_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(lean_object* v_f_1778_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_io_create_tempdir();
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v_r_1782_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc_n(v_a_1781_, 2);
lean_dec_ref_known(v___x_1780_, 1);
v_r_1782_ = lean_apply_2(v_f_1778_, v_a_1781_, lean_box(0));
if (lean_obj_tag(v_r_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v_r_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v_r_1782_, 1);
v___x_1784_ = l_IO_FS_removeDirAll(v_a_1781_);
lean_dec(v_a_1781_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v___x_1784_, 0);
lean_dec(v_unused_1792_);
v___x_1786_ = v___x_1784_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_dec(v___x_1784_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v_a_1783_);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1783_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_a_1783_);
v_a_1793_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1784_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1784_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1802_; 
v_a_1801_ = lean_ctor_get(v_r_1782_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v_r_1782_, 1);
v___x_1802_ = l_IO_FS_removeDirAll(v_a_1781_);
lean_dec(v_a_1781_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v___x_1802_, 0);
lean_dec(v_unused_1810_);
v___x_1804_ = v___x_1802_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_dec(v___x_1802_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set_tag(v___x_1804_, 1);
lean_ctor_set(v___x_1804_, 0, v_a_1801_);
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1801_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_a_1801_);
v_a_1811_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1802_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1802_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v_f_1778_);
v_a_1819_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1780_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1780_);
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
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg___boxed(lean_object* v_f_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v_f_1827_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(lean_object* v_00_u03b1_1830_, lean_object* v_f_1831_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v_f_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___boxed(lean_object* v_00_u03b1_1834_, lean_object* v_f_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(v_00_u03b1_1834_, v_f_1835_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__0(lean_object* v___y_1838_, lean_object* v_____r_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v___y_1838_);
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__0___boxed(lean_object* v___y_1843_, lean_object* v_____r_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lake_Samply_run___lam__0(v___y_1843_, v_____r_1844_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(lean_object* v_s_1847_){
_start:
{
lean_object* v___x_1849_; lean_object* v_putStr_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_get_stderr();
v_putStr_1850_ = lean_ctor_get(v___x_1849_, 4);
lean_inc_ref(v_putStr_1850_);
lean_dec_ref(v___x_1849_);
v___x_1851_ = lean_apply_2(v_putStr_1850_, v_s_1847_, lean_box(0));
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0___boxed(lean_object* v_s_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(v_s_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0(lean_object* v_s_1855_){
_start:
{
uint32_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = 10;
v___x_1858_ = lean_string_push(v_s_1855_, v___x_1857_);
v___x_1859_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0___boxed(lean_object* v_s_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v_s_1860_);
return v_res_1862_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1868_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__2));
v___x_1869_ = lean_unsigned_to_nat(4u);
v___x_1870_ = lean_mk_empty_array_with_capacity(v___x_1869_);
v___x_1871_ = lean_array_push(v___x_1870_, v___x_1868_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__3));
v___x_1873_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__5, &l_Lake_Samply_run___lam__1___closed__5_once, _init_l_Lake_Samply_run___lam__1___closed__5);
v___x_1874_ = lean_array_push(v___x_1873_, v___x_1872_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__4));
v___x_1876_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__6, &l_Lake_Samply_run___lam__1___closed__6_once, _init_l_Lake_Samply_run___lam__1___closed__6);
v___x_1877_ = lean_array_push(v___x_1876_, v___x_1875_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1878_ = ((lean_object*)(l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0));
v___x_1879_ = lean_unsigned_to_nat(2u);
v___x_1880_ = lean_mk_empty_array_with_capacity(v___x_1879_);
v___x_1881_ = lean_array_push(v___x_1880_, v___x_1878_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__20(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1894_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__19));
v___x_1895_ = lean_unsigned_to_nat(2u);
v___x_1896_ = lean_mk_empty_array_with_capacity(v___x_1895_);
v___x_1897_ = lean_array_push(v___x_1896_, v___x_1894_);
return v___x_1897_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__31(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1908_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__22));
v___x_1909_ = lean_unsigned_to_nat(9u);
v___x_1910_ = lean_mk_empty_array_with_capacity(v___x_1909_);
v___x_1911_ = lean_array_push(v___x_1910_, v___x_1908_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__32(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__23));
v___x_1913_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__31, &l_Lake_Samply_run___lam__1___closed__31_once, _init_l_Lake_Samply_run___lam__1___closed__31);
v___x_1914_ = lean_array_push(v___x_1913_, v___x_1912_);
return v___x_1914_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__33(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__24));
v___x_1916_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__32, &l_Lake_Samply_run___lam__1___closed__32_once, _init_l_Lake_Samply_run___lam__1___closed__32);
v___x_1917_ = lean_array_push(v___x_1916_, v___x_1915_);
return v___x_1917_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__34(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__25));
v___x_1919_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__33, &l_Lake_Samply_run___lam__1___closed__33_once, _init_l_Lake_Samply_run___lam__1___closed__33);
v___x_1920_ = lean_array_push(v___x_1919_, v___x_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__1(lean_object* v_passthrough_1933_, lean_object* v_binary_1934_, lean_object* v___x_1935_, lean_object* v_env_1936_, uint8_t v_raw_1937_, lean_object* v_port_1938_, lean_object* v___x_1939_, uint8_t v_serve_1940_, lean_object* v_outputPath_1941_, lean_object* v_tmpDir_1942_){
_start:
{
lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v_a_1947_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___y_1991_; 
v___x_1988_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__0));
lean_inc_ref(v_tmpDir_1942_);
v___x_1989_ = l_System_FilePath_join(v_tmpDir_1942_, v___x_1988_);
if (lean_obj_tag(v_outputPath_1941_) == 0)
{
if (v_raw_1937_ == 0)
{
lean_object* v___x_2247_; 
v___x_2247_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__45));
v___y_1991_ = v___x_2247_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2248_; 
v___x_2248_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__46));
v___y_1991_ = v___x_2248_;
goto v___jp_1990_;
}
}
else
{
lean_object* v_val_2249_; 
v_val_2249_ = lean_ctor_get(v_outputPath_1941_, 0);
lean_inc(v_val_2249_);
lean_dec_ref_known(v_outputPath_1941_, 1);
v___y_1991_ = v_val_2249_;
goto v___jp_1990_;
}
v___jp_1944_:
{
lean_object* v___x_1948_; 
v___x_1948_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v___y_1946_, v___y_1945_);
lean_dec_ref(v___y_1945_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1955_ == 0)
{
lean_object* v_unused_1956_; 
v_unused_1956_ = lean_ctor_get(v___x_1948_, 0);
lean_dec(v_unused_1956_);
v___x_1950_ = v___x_1948_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_dec(v___x_1948_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
lean_ctor_set_tag(v___x_1950_, 1);
lean_ctor_set(v___x_1950_, 0, v_a_1947_);
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1947_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v_a_1947_);
v_a_1957_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1948_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1948_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
v___jp_1965_:
{
lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___y_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___y_1968_);
v___x_1970_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v___y_1967_, v___y_1966_);
lean_dec_ref(v___y_1966_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1978_; 
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v___x_1970_, 0);
lean_dec(v_unused_1979_);
v___x_1972_ = v___x_1970_;
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
else
{
lean_dec(v___x_1970_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1978_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_a_1974_; lean_object* v___x_1976_; 
v_a_1974_ = lean_ctor_get(v_a_1969_, 0);
lean_inc(v_a_1974_);
lean_dec(v_a_1969_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_a_1974_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_a_1969_);
v_a_1980_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1970_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1970_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
v___jp_1990_:
{
lean_object* v___x_1992_; lean_object* v_fst_1993_; lean_object* v_snd_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1992_ = l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash(v_passthrough_1933_);
v_fst_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_fst_1993_);
v_snd_1994_ = lean_ctor_get(v___x_1992_, 1);
lean_inc(v_snd_1994_);
lean_dec_ref(v___x_1992_);
v___x_1995_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__1));
v___x_1996_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_1995_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec_ref_known(v___x_1996_, 1);
v___x_1997_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__0));
v___x_1998_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__7, &l_Lake_Samply_run___lam__1___closed__7_once, _init_l_Lake_Samply_run___lam__1___closed__7);
lean_inc_ref(v___x_1989_);
v___x_1999_ = lean_array_push(v___x_1998_, v___x_1989_);
v___x_2000_ = l_Array_append___redArg(v___x_1999_, v_fst_1993_);
lean_dec(v_fst_1993_);
v___x_2001_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__8, &l_Lake_Samply_run___lam__1___closed__8_once, _init_l_Lake_Samply_run___lam__1___closed__8);
v___x_2002_ = lean_array_push(v___x_2001_, v_binary_1934_);
v___x_2003_ = l_Array_append___redArg(v___x_2000_, v___x_2002_);
lean_dec_ref(v___x_2002_);
v___x_2004_ = l_Array_append___redArg(v___x_2003_, v_snd_1994_);
lean_dec(v_snd_1994_);
v___x_2005_ = lean_box(0);
v___x_2006_ = 1;
v___x_2007_ = 0;
v___x_2008_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2008_, 0, v___x_1997_);
lean_ctor_set(v___x_2008_, 1, v___x_1935_);
lean_ctor_set(v___x_2008_, 2, v___x_2004_);
lean_ctor_set(v___x_2008_, 3, v___x_2005_);
lean_ctor_set(v___x_2008_, 4, v_env_1936_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*5, v___x_2006_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*5 + 1, v___x_2007_);
v___x_2009_ = lean_io_process_spawn(v___x_2008_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2011_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = lean_io_process_child_wait(v___x_1997_, v_a_2010_);
lean_dec(v_a_2010_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2222_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2222_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2222_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
uint32_t v___x_2016_; uint32_t v___x_2017_; uint8_t v___x_2018_; 
v___x_2016_ = 0;
v___x_2017_ = lean_unbox_uint32(v_a_2012_);
v___x_2018_ = lean_uint32_dec_eq(v___x_2017_, v___x_2016_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; uint32_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
lean_dec(v_port_1938_);
v___x_2019_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__9));
v___x_2020_ = lean_unbox_uint32(v_a_2012_);
lean_dec(v_a_2012_);
v___x_2021_ = lean_uint32_to_nat(v___x_2020_);
v___x_2022_ = l_Nat_reprFast(v___x_2021_);
v___x_2023_ = lean_string_append(v___x_2019_, v___x_2022_);
lean_dec_ref(v___x_2022_);
v___x_2024_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__10));
v___x_2025_ = lean_string_append(v___x_2023_, v___x_2024_);
v___x_2026_ = lean_mk_io_user_error(v___x_2025_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 1);
lean_ctor_set(v___x_2014_, 0, v___x_2026_);
v___x_2028_ = v___x_2014_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
else
{
lean_del_object(v___x_2014_);
lean_dec(v_a_2012_);
if (v_raw_1937_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__11));
v___x_2031_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2030_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec_ref_known(v___x_2031_, 1);
v___x_2032_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__12));
lean_inc_ref(v_tmpDir_1942_);
v___x_2033_ = l_System_FilePath_join(v_tmpDir_1942_, v___x_2032_);
v___x_2034_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__0));
v___x_2035_ = l_IO_FS_writeFile(v___x_2033_, v___x_2034_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec_ref_known(v___x_2035_, 1);
v___x_2036_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__13));
v___x_2037_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__1));
v___x_2038_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__14));
lean_inc(v_port_1938_);
v___x_2039_ = l_Nat_reprFast(v_port_1938_);
v___x_2040_ = lean_string_append(v___x_2038_, v___x_2039_);
v___x_2041_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__15));
v___x_2042_ = lean_string_append(v___x_2040_, v___x_2041_);
lean_inc_ref(v___x_1989_);
v___x_2043_ = l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(v___x_1989_);
v___x_2044_ = lean_string_append(v___x_2042_, v___x_2043_);
lean_dec_ref(v___x_2043_);
v___x_2045_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__16));
v___x_2046_ = lean_string_append(v___x_2044_, v___x_2045_);
lean_inc_ref(v___x_2033_);
v___x_2047_ = l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(v___x_2033_);
v___x_2048_ = lean_string_append(v___x_2046_, v___x_2047_);
lean_dec_ref(v___x_2047_);
v___x_2049_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__17));
v___x_2050_ = lean_string_append(v___x_2048_, v___x_2049_);
v___x_2051_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4, &l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4);
v___x_2052_ = lean_array_push(v___x_2051_, v___x_2050_);
v___x_2053_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__5));
v___x_2054_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2054_, 0, v___x_2036_);
lean_ctor_set(v___x_2054_, 1, v___x_2037_);
lean_ctor_set(v___x_2054_, 2, v___x_2052_);
lean_ctor_set(v___x_2054_, 3, v___x_2005_);
lean_ctor_set(v___x_2054_, 4, v___x_2053_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*5, v___x_2006_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*5 + 1, v___x_2007_);
v___x_2055_ = lean_io_process_spawn(v___x_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2057_ = lean_unsigned_to_nat(30000u);
v___x_2058_ = l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(v___x_2036_, v___x_2033_, v_a_2056_, v_port_1938_, v___x_2057_);
lean_dec_ref(v___x_2033_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__0));
v___x_2061_ = lean_string_append(v___x_2060_, v___x_2039_);
lean_dec_ref(v___x_2039_);
v___x_2062_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__1));
v___x_2063_ = lean_string_append(v___x_2061_, v___x_2062_);
v___x_2064_ = lean_string_append(v___x_2063_, v_a_2059_);
lean_dec(v_a_2059_);
v___x_2065_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__18));
v___x_2066_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2065_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_dec_ref_known(v___x_2066_, 1);
v___x_2067_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__20, &l_Lake_Samply_run___lam__1___closed__20_once, _init_l_Lake_Samply_run___lam__1___closed__20);
lean_inc_ref(v___x_1989_);
v___x_2068_ = lean_array_push(v___x_2067_, v___x_1989_);
lean_inc_ref(v___x_1939_);
v___x_2069_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2069_, 0, v___x_1997_);
lean_ctor_set(v___x_2069_, 1, v___x_1939_);
lean_ctor_set(v___x_2069_, 2, v___x_2068_);
lean_ctor_set(v___x_2069_, 3, v___x_2005_);
lean_ctor_set(v___x_2069_, 4, v___x_2053_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*5, v___x_2006_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*5 + 1, v___x_2007_);
v___x_2070_ = l_IO_Process_run(v___x_2069_, v___x_2005_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v___x_2072_ = l_Lean_Json_parse(v_a_2071_);
v___x_2073_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_2072_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2075_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc_n(v_a_2074_, 2);
lean_dec_ref_known(v___x_2073_, 1);
v___x_2075_ = l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(v_a_2074_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2164_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2164_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2164_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_fst_2080_; lean_object* v_snd_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v_fst_2080_ = lean_ctor_get(v_a_2076_, 0);
lean_inc(v_fst_2080_);
v_snd_2081_ = lean_ctor_get(v_a_2076_, 1);
lean_inc(v_snd_2081_);
lean_dec(v_a_2076_);
v___x_2082_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__21));
v___x_2083_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__26));
lean_inc_ref(v___x_2064_);
v___x_2084_ = lean_string_append(v___x_2064_, v___x_2083_);
v___x_2085_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__27));
v___x_2086_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__28));
v___x_2087_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__29));
v___x_2088_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__30));
v___x_2089_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__34, &l_Lake_Samply_run___lam__1___closed__34_once, _init_l_Lake_Samply_run___lam__1___closed__34);
v___x_2090_ = lean_array_push(v___x_2089_, v___x_2084_);
v___x_2091_ = lean_array_push(v___x_2090_, v___x_2085_);
v___x_2092_ = lean_array_push(v___x_2091_, v___x_2086_);
v___x_2093_ = lean_array_push(v___x_2092_, v___x_2087_);
v___x_2094_ = lean_array_push(v___x_2093_, v___x_2088_);
v___x_2095_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2095_, 0, v___x_1997_);
lean_ctor_set(v___x_2095_, 1, v___x_2082_);
lean_ctor_set(v___x_2095_, 2, v___x_2094_);
lean_ctor_set(v___x_2095_, 3, v___x_2005_);
lean_ctor_set(v___x_2095_, 4, v___x_2053_);
lean_ctor_set_uint8(v___x_2095_, sizeof(void*)*5, v___x_2006_);
lean_ctor_set_uint8(v___x_2095_, sizeof(void*)*5 + 1, v___x_2007_);
v___x_2096_ = l_Lean_Json_compress(v_fst_2080_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 1);
lean_ctor_set(v___x_2078_, 0, v___x_2096_);
v___x_2098_ = v___x_2078_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_IO_Process_run(v___x_2095_, v___x_2098_);
lean_dec_ref(v___x_2098_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = l_Lean_Json_parse(v_a_2100_);
v___x_2102_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_2101_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2104_ = l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(v_a_2074_, v_a_2103_, v_snd_2081_);
lean_dec(v_snd_2081_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__35));
lean_inc_ref(v_tmpDir_1942_);
v___x_2107_ = l_System_FilePath_join(v_tmpDir_1942_, v___x_2106_);
v___x_2108_ = l_Lean_Json_compress(v_a_2105_);
v___x_2109_ = l_IO_FS_writeFile(v___x_2107_, v___x_2108_);
lean_dec_ref(v___x_2108_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_dec_ref_known(v___x_2109_, 1);
v___x_2110_ = lean_unsigned_to_nat(1u);
v___x_2111_ = lean_mk_empty_array_with_capacity(v___x_2110_);
v___x_2112_ = lean_array_push(v___x_2111_, v___x_2107_);
v___x_2113_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2113_, 0, v___x_1997_);
lean_ctor_set(v___x_2113_, 1, v___x_1939_);
lean_ctor_set(v___x_2113_, 2, v___x_2112_);
lean_ctor_set(v___x_2113_, 3, v___x_2005_);
lean_ctor_set(v___x_2113_, 4, v___x_2053_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*5, v___x_2006_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*5 + 1, v___x_2007_);
v___x_2114_ = l_IO_Process_run(v___x_2113_, v___x_2005_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec_ref_known(v___x_2114_, 1);
v___x_2115_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__36));
v___x_2116_ = l_System_FilePath_join(v_tmpDir_1942_, v___x_2115_);
v___x_2117_ = lean_io_rename(v___x_2116_, v___x_1989_);
lean_dec_ref(v___x_2116_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; 
lean_dec_ref_known(v___x_2117_, 1);
v___x_2118_ = l_Lake_copyFile(v___x_1989_, v___y_1991_);
lean_dec_ref(v___x_1989_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec_ref_known(v___x_2118_, 1);
v___x_2119_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__37));
v___x_2120_ = lean_string_append(v___x_2119_, v___y_1991_);
v___x_2121_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2120_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_dec_ref_known(v___x_2121_, 1);
if (v_serve_1940_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_dec_ref(v___x_2064_);
v___x_2122_ = lean_box(0);
v___x_2123_ = l_Lake_Samply_run___lam__0(v___y_1991_, v___x_2122_);
v___y_1966_ = v_a_2056_;
v___y_1967_ = v___x_2036_;
v___y_1968_ = v___x_2123_;
goto v___jp_1965_;
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2124_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__38));
v___x_2125_ = lean_string_append(v___x_2124_, v___x_2064_);
v___x_2126_ = lean_string_append(v___x_2125_, v___x_2062_);
v___x_2127_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2126_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec_ref_known(v___x_2127_, 1);
v___x_2128_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__39));
v___x_2129_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2128_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
lean_dec_ref_known(v___x_2129_, 1);
v___x_2130_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__40));
v___x_2131_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__41));
v___x_2132_ = lean_string_append(v___x_2064_, v___x_2131_);
v___x_2133_ = l_Lake_uriEncode(v___x_2132_, v___x_2034_);
lean_dec_ref(v___x_2132_);
v___x_2134_ = lean_string_append(v___x_2130_, v___x_2133_);
lean_dec_ref(v___x_2133_);
v___x_2135_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2134_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_dec_ref_known(v___x_2135_, 1);
v___x_2136_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__42));
v___x_2137_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2136_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2138_; 
lean_dec_ref_known(v___x_2137_, 1);
v___x_2138_ = lean_io_process_child_wait(v___x_2036_, v_a_2056_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; uint32_t v___x_2140_; uint8_t v___x_2141_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = lean_unbox_uint32(v_a_2139_);
v___x_2141_ = lean_uint32_dec_eq(v___x_2140_, v___x_2016_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; uint32_t v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec_ref(v___y_1991_);
v___x_2142_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__43));
v___x_2143_ = lean_unbox_uint32(v_a_2139_);
lean_dec(v_a_2139_);
v___x_2144_ = lean_uint32_to_nat(v___x_2143_);
v___x_2145_ = l_Nat_reprFast(v___x_2144_);
v___x_2146_ = lean_string_append(v___x_2142_, v___x_2145_);
lean_dec_ref(v___x_2145_);
v___x_2147_ = lean_mk_io_user_error(v___x_2146_);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v___x_2147_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec(v_a_2139_);
v___x_2148_ = lean_box(0);
v___x_2149_ = l_Lake_Samply_run___lam__0(v___y_1991_, v___x_2148_);
v___y_1966_ = v_a_2056_;
v___y_1967_ = v___x_2036_;
v___y_1968_ = v___x_2149_;
goto v___jp_1965_;
}
}
else
{
lean_object* v_a_2150_; 
lean_dec_ref(v___y_1991_);
v_a_2150_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2138_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2150_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2151_; 
lean_dec_ref(v___y_1991_);
v_a_2151_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2137_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2151_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2152_; 
lean_dec_ref(v___y_1991_);
v_a_2152_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2135_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2152_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2153_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
v_a_2153_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2129_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2153_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2154_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
v_a_2154_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2127_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2154_;
goto v___jp_1944_;
}
}
}
else
{
lean_object* v_a_2155_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
v_a_2155_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2121_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2155_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2156_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
v_a_2156_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2118_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2156_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2157_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
v_a_2157_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2117_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2157_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2158_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
v_a_2158_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2114_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2158_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2159_; 
lean_dec_ref(v___x_2107_);
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
v_a_2159_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2109_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2159_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2160_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
v_a_2160_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2104_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2160_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2161_; 
lean_dec(v_snd_2081_);
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
v_a_2161_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2102_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2161_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2162_; 
lean_dec(v_snd_2081_);
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
v_a_2162_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2099_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2162_;
goto v___jp_1944_;
}
}
}
}
else
{
lean_object* v_a_2165_; 
lean_dec(v_a_2074_);
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
v_a_2165_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2075_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2165_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2166_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
v_a_2166_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2073_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2166_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2167_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
v_a_2167_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2070_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2167_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2168_; 
lean_dec_ref(v___x_2064_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
v_a_2168_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2066_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2168_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2169_; 
lean_dec_ref(v___x_2039_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
v_a_2169_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2058_, 1);
v___y_1945_ = v_a_2056_;
v___y_1946_ = v___x_2036_;
v_a_1947_ = v_a_2169_;
goto v___jp_1944_;
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v___x_2039_);
lean_dec_ref(v___x_2033_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
lean_dec(v_port_1938_);
v_a_2170_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2055_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2055_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec_ref(v___x_2033_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
lean_dec(v_port_1938_);
v_a_2178_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2035_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2035_);
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
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
lean_dec(v_port_1938_);
v_a_2186_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2031_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2031_);
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
lean_object* v___x_2194_; 
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
lean_dec(v_port_1938_);
v___x_2194_ = l_Lake_copyFile(v___x_1989_, v___y_1991_);
lean_dec_ref(v___x_1989_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec_ref_known(v___x_2194_, 1);
v___x_2195_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__44));
v___x_2196_ = lean_string_append(v___x_2195_, v___y_1991_);
v___x_2197_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2196_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; 
v_unused_2205_ = lean_ctor_get(v___x_2197_, 0);
lean_dec(v_unused_2205_);
v___x_2199_ = v___x_2197_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_dec(v___x_2197_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___y_1991_);
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___y_1991_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec_ref(v___y_1991_);
v_a_2206_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2197_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2197_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref(v___y_1991_);
v_a_2214_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2194_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2194_);
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
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
lean_dec(v_port_1938_);
v_a_2223_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2011_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2011_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
lean_dec(v_port_1938_);
v_a_2231_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2009_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2009_);
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
lean_dec(v_snd_1994_);
lean_dec(v_fst_1993_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_tmpDir_1942_);
lean_dec_ref(v___x_1939_);
lean_dec(v_port_1938_);
lean_dec_ref(v_env_1936_);
lean_dec_ref(v___x_1935_);
lean_dec_ref(v_binary_1934_);
v_a_2239_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_1996_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_1996_);
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
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__1___boxed(lean_object* v_passthrough_2250_, lean_object* v_binary_2251_, lean_object* v___x_2252_, lean_object* v_env_2253_, lean_object* v_raw_2254_, lean_object* v_port_2255_, lean_object* v___x_2256_, lean_object* v_serve_2257_, lean_object* v_outputPath_2258_, lean_object* v_tmpDir_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v_raw_boxed_2261_; uint8_t v_serve_boxed_2262_; lean_object* v_res_2263_; 
v_raw_boxed_2261_ = lean_unbox(v_raw_2254_);
v_serve_boxed_2262_ = lean_unbox(v_serve_2257_);
v_res_2263_ = l_Lake_Samply_run___lam__1(v_passthrough_2250_, v_binary_2251_, v___x_2252_, v_env_2253_, v_raw_boxed_2261_, v_port_2255_, v___x_2256_, v_serve_boxed_2262_, v_outputPath_2258_, v_tmpDir_2259_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run(lean_object* v_binary_2269_, lean_object* v_passthrough_2270_, lean_object* v_outputPath_2271_, lean_object* v_port_2272_, uint8_t v_raw_2273_, uint8_t v_serve_2274_, lean_object* v_env_2275_){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = ((lean_object*)(l_Lake_Samply_run___closed__0));
v___x_2278_ = ((lean_object*)(l_Lake_Samply_run___closed__1));
v___x_2279_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2277_, v___x_2278_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___f_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec_ref_known(v___x_2279_, 1);
v___x_2280_ = ((lean_object*)(l_Lake_Samply_run___closed__2));
v___x_2281_ = lean_box(v_raw_2273_);
v___x_2282_ = lean_box(v_serve_2274_);
v___f_2283_ = lean_alloc_closure((void*)(l_Lake_Samply_run___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2283_, 0, v_passthrough_2270_);
lean_closure_set(v___f_2283_, 1, v_binary_2269_);
lean_closure_set(v___f_2283_, 2, v___x_2277_);
lean_closure_set(v___f_2283_, 3, v_env_2275_);
lean_closure_set(v___f_2283_, 4, v___x_2281_);
lean_closure_set(v___f_2283_, 5, v_port_2272_);
lean_closure_set(v___f_2283_, 6, v___x_2280_);
lean_closure_set(v___f_2283_, 7, v___x_2282_);
lean_closure_set(v___f_2283_, 8, v_outputPath_2271_);
v___x_2284_ = ((lean_object*)(l_Lake_Samply_run___closed__3));
v___x_2285_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2280_, v___x_2284_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_dec_ref_known(v___x_2285_, 1);
if (v_raw_2273_ == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__21));
v___x_2287_ = ((lean_object*)(l_Lake_Samply_run___closed__4));
v___x_2288_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2286_, v___x_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v___x_2289_; 
lean_dec_ref_known(v___x_2288_, 1);
v___x_2289_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v___f_2283_);
return v___x_2289_;
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref(v___f_2283_);
v_a_2290_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2288_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2288_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
else
{
lean_object* v___x_2298_; 
v___x_2298_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v___f_2283_);
return v___x_2298_;
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec_ref(v___f_2283_);
v_a_2299_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2285_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2285_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v_env_2275_);
lean_dec(v_port_2272_);
lean_dec(v_outputPath_2271_);
lean_dec_ref(v_passthrough_2270_);
lean_dec_ref(v_binary_2269_);
v_a_2307_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2279_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2279_);
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
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___boxed(lean_object* v_binary_2315_, lean_object* v_passthrough_2316_, lean_object* v_outputPath_2317_, lean_object* v_port_2318_, lean_object* v_raw_2319_, lean_object* v_serve_2320_, lean_object* v_env_2321_, lean_object* v_a_2322_){
_start:
{
uint8_t v_raw_boxed_2323_; uint8_t v_serve_boxed_2324_; lean_object* v_res_2325_; 
v_raw_boxed_2323_ = lean_unbox(v_raw_2319_);
v_serve_boxed_2324_ = lean_unbox(v_serve_2320_);
v_res_2325_ = l_Lake_Samply_run(v_binary_2315_, v_passthrough_2316_, v_outputPath_2317_, v_port_2318_, v_raw_boxed_2323_, v_serve_boxed_2324_, v_env_2321_);
return v_res_2325_;
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
