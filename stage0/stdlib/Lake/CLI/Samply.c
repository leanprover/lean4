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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___boxed(lean_object* v_output_396_, lean_object* v_port_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(v_output_396_, v_port_397_);
lean_dec_ref(v_output_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0(lean_object* v_decoded_399_, lean_object* v___x_400_, lean_object* v___x_401_, lean_object* v_inst_402_, lean_object* v_R_403_, lean_object* v_a_404_, lean_object* v_b_405_, lean_object* v_c_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___redArg(v_decoded_399_, v___x_400_, v___x_401_, v_a_404_, v_b_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0___boxed(lean_object* v_decoded_408_, lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v_inst_411_, lean_object* v_R_412_, lean_object* v_a_413_, lean_object* v_b_414_, lean_object* v_c_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__0(v_decoded_408_, v___x_409_, v___x_410_, v_inst_411_, v_R_412_, v_a_413_, v_b_414_, v_c_415_);
lean_dec(v_b_414_);
lean_dec(v___x_410_);
lean_dec_ref(v___x_409_);
lean_dec_ref(v_decoded_408_);
return v_res_416_;
}
}
static lean_object* _init_l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = l_instInhabitedError;
v___x_418_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_418_, 0, lean_box(0));
lean_closure_set(v___x_418_, 1, lean_box(0));
lean_closure_set(v___x_418_, 2, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(lean_object* v_msg_419_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_1178__overap_422_; lean_object* v___x_423_; 
v___x_421_ = lean_obj_once(&l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0, &l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0_once, _init_l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0);
v___x_1178__overap_422_ = lean_panic_fn_borrowed(v___x_421_, v_msg_419_);
v___x_423_ = lean_apply_1(v___x_1178__overap_422_, lean_box(0));
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___boxed(lean_object* v_msg_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(v_msg_424_);
return v_res_426_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__2));
v___x_431_ = lean_mk_io_user_error(v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(lean_object* v_val_432_, lean_object* v_timeoutMs_433_, lean_object* v_cfg_434_, lean_object* v_proc_435_, lean_object* v_logFile_436_, lean_object* v_port_437_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_439_ = lean_box(0);
v___x_440_ = lean_io_mono_ms_now();
v___x_441_ = lean_nat_sub(v___x_440_, v_val_432_);
lean_dec(v___x_440_);
v___x_442_ = lean_nat_dec_lt(v_timeoutMs_433_, v___x_441_);
lean_dec(v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_io_process_child_try_wait(v_cfg_434_, v_proc_435_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
if (lean_obj_tag(v_a_444_) == 1)
{
lean_object* v_val_445_; lean_object* v___x_446_; 
lean_dec(v_port_437_);
v_val_445_ = lean_ctor_get(v_a_444_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v_a_444_, 1);
v___x_446_ = l_IO_FS_readFile(v_logFile_436_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_463_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_463_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_463_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_463_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; uint32_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_451_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__0));
v___x_452_ = lean_unbox_uint32(v_val_445_);
lean_dec(v_val_445_);
v___x_453_ = lean_uint32_to_nat(v___x_452_);
v___x_454_ = l_Nat_reprFast(v___x_453_);
v___x_455_ = lean_string_append(v___x_451_, v___x_454_);
lean_dec_ref(v___x_454_);
v___x_456_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__1));
v___x_457_ = lean_string_append(v___x_455_, v___x_456_);
v___x_458_ = lean_string_append(v___x_457_, v_a_447_);
lean_dec(v_a_447_);
v___x_459_ = lean_mk_io_user_error(v___x_458_);
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 1);
lean_ctor_set(v___x_449_, 0, v___x_459_);
v___x_461_ = v___x_449_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_val_445_);
v_a_464_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_446_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_446_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v___x_472_; 
lean_dec(v_a_444_);
v___x_472_ = l_IO_FS_readFile(v_logFile_436_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_485_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_485_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_485_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; 
lean_inc(v_port_437_);
v___x_477_ = l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(v_a_473_, v_port_437_);
lean_dec(v_a_473_);
if (lean_obj_tag(v___x_477_) == 1)
{
lean_object* v___x_478_; lean_object* v___x_480_; 
lean_dec(v_port_437_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___x_439_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_478_);
v___x_480_ = v___x_475_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
else
{
uint32_t v___x_482_; lean_object* v___x_483_; 
lean_dec(v___x_477_);
lean_del_object(v___x_475_);
v___x_482_ = 200;
v___x_483_ = l_IO_sleep(v___x_482_);
goto _start;
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v_port_437_);
v_a_486_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_472_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_472_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_port_437_);
v_a_494_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_443_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_443_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v_port_437_);
v___x_502_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3);
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___boxed(lean_object* v_val_504_, lean_object* v_timeoutMs_505_, lean_object* v_cfg_506_, lean_object* v_proc_507_, lean_object* v_logFile_508_, lean_object* v_port_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v_val_504_, v_timeoutMs_505_, v_cfg_506_, v_proc_507_, v_logFile_508_, v_port_509_);
lean_dec_ref(v_logFile_508_);
lean_dec_ref(v_proc_507_);
lean_dec_ref(v_cfg_506_);
lean_dec(v_timeoutMs_505_);
lean_dec(v_val_504_);
return v_res_511_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_515_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__2));
v___x_516_ = lean_unsigned_to_nat(2u);
v___x_517_ = lean_unsigned_to_nat(58u);
v___x_518_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__1));
v___x_519_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__0));
v___x_520_ = l_mkPanicMessageWithDecl(v___x_519_, v___x_518_, v___x_517_, v___x_516_, v___x_515_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(lean_object* v_cfg_521_, lean_object* v_logFile_522_, lean_object* v_proc_523_, lean_object* v_port_524_, lean_object* v_timeoutMs_525_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_io_mono_ms_now();
v___x_528_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v___x_527_, v_timeoutMs_525_, v_cfg_521_, v_proc_523_, v_logFile_522_, v_port_524_);
lean_dec(v___x_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_540_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_540_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_540_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_540_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_fst_533_; 
v_fst_533_ = lean_ctor_get(v_a_529_, 0);
lean_inc(v_fst_533_);
lean_dec(v_a_529_);
if (lean_obj_tag(v_fst_533_) == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_del_object(v___x_531_);
v___x_534_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3, &l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3);
v___x_535_ = l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(v___x_534_);
return v___x_535_;
}
else
{
lean_object* v_val_536_; lean_object* v___x_538_; 
v_val_536_ = lean_ctor_get(v_fst_533_, 0);
lean_inc(v_val_536_);
lean_dec_ref_known(v_fst_533_, 1);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v_val_536_);
v___x_538_ = v___x_531_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_val_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_a_541_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_528_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_528_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___boxed(lean_object* v_cfg_549_, lean_object* v_logFile_550_, lean_object* v_proc_551_, lean_object* v_port_552_, lean_object* v_timeoutMs_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(v_cfg_549_, v_logFile_550_, v_proc_551_, v_port_552_, v_timeoutMs_553_);
lean_dec(v_timeoutMs_553_);
lean_dec_ref(v_proc_551_);
lean_dec_ref(v_logFile_550_);
lean_dec_ref(v_cfg_549_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(lean_object* v_val_556_, lean_object* v_timeoutMs_557_, lean_object* v_cfg_558_, lean_object* v_proc_559_, lean_object* v_logFile_560_, lean_object* v_port_561_, lean_object* v_inst_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v_val_556_, v_timeoutMs_557_, v_cfg_558_, v_proc_559_, v_logFile_560_, v_port_561_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___boxed(lean_object* v_val_566_, lean_object* v_timeoutMs_567_, lean_object* v_cfg_568_, lean_object* v_proc_569_, lean_object* v_logFile_570_, lean_object* v_port_571_, lean_object* v_inst_572_, lean_object* v_a_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(v_val_566_, v_timeoutMs_567_, v_cfg_568_, v_proc_569_, v_logFile_570_, v_port_571_, v_inst_572_, v_a_573_);
lean_dec_ref(v_a_573_);
lean_dec_ref(v_logFile_570_);
lean_dec_ref(v_proc_569_);
lean_dec_ref(v_cfg_568_);
lean_dec(v_timeoutMs_567_);
lean_dec(v_val_566_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(lean_object* v_j_576_, lean_object* v_k_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = l_Lean_Json_getObjValD(v_j_576_, v_k_577_);
v___x_579_ = l_Lean_Json_getStr_x3f(v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0___boxed(lean_object* v_j_580_, lean_object* v_k_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_j_580_, v_k_581_);
lean_dec_ref(v_k_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(lean_object* v_e_583_){
_start:
{
if (lean_obj_tag(v_e_583_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_593_; 
v_a_585_ = lean_ctor_get(v_e_583_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v_e_583_);
if (v_isSharedCheck_593_ == 0)
{
v___x_587_ = v_e_583_;
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v_e_583_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_589_ = lean_mk_io_user_error(v_a_585_);
if (v_isShared_588_ == 0)
{
lean_ctor_set_tag(v___x_587_, 1);
lean_ctor_set(v___x_587_, 0, v___x_589_);
v___x_591_ = v___x_587_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_594_ = lean_ctor_get(v_e_583_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_e_583_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v_e_583_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v_e_583_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set_tag(v___x_596_, 0);
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg___boxed(lean_object* v_e_602_, lean_object* v_a_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v_e_602_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(lean_object* v_00_u03b1_605_, lean_object* v_e_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v_e_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___boxed(lean_object* v_00_u03b1_609_, lean_object* v_e_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(v_00_u03b1_609_, v_e_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(size_t v_sz_613_, size_t v_i_614_, lean_object* v_bs_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_lt(v_i_614_, v_sz_613_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_bs_615_);
return v___x_617_;
}
else
{
lean_object* v_v_618_; lean_object* v___x_619_; lean_object* v_bs_x27_620_; size_t v___x_621_; size_t v___x_622_; lean_object* v___x_623_; 
v_v_618_ = lean_array_uget(v_bs_615_, v_i_614_);
v___x_619_ = lean_unsigned_to_nat(0u);
v_bs_x27_620_ = lean_array_uset(v_bs_615_, v_i_614_, v___x_619_);
v___x_621_ = ((size_t)1ULL);
v___x_622_ = lean_usize_add(v_i_614_, v___x_621_);
v___x_623_ = lean_array_uset(v_bs_x27_620_, v_i_614_, v_v_618_);
v_i_614_ = v___x_622_;
v_bs_615_ = v___x_623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_625_, lean_object* v_i_626_, lean_object* v_bs_627_){
_start:
{
size_t v_sz_boxed_628_; size_t v_i_boxed_629_; lean_object* v_res_630_; 
v_sz_boxed_628_ = lean_unbox_usize(v_sz_625_);
lean_dec(v_sz_625_);
v_i_boxed_629_ = lean_unbox_usize(v_i_626_);
lean_dec(v_i_626_);
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(v_sz_boxed_628_, v_i_boxed_629_, v_bs_627_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 4)
{
lean_object* v_elems_633_; size_t v_sz_634_; size_t v___x_635_; lean_object* v___x_636_; 
v_elems_633_ = lean_ctor_get(v_x_632_, 0);
lean_inc_ref(v_elems_633_);
lean_dec_ref_known(v_x_632_, 1);
v_sz_634_ = lean_array_size(v_elems_633_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(v_sz_634_, v___x_635_, v_elems_633_);
return v___x_636_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_637_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_638_ = lean_unsigned_to_nat(80u);
v___x_639_ = l_Lean_Json_pretty(v_x_632_, v___x_638_);
v___x_640_ = lean_string_append(v___x_637_, v___x_639_);
lean_dec_ref(v___x_639_);
v___x_641_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_642_ = lean_string_append(v___x_640_, v___x_641_);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(lean_object* v_j_644_, lean_object* v_k_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = l_Lean_Json_getObjValD(v_j_644_, v_k_645_);
v___x_647_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3___boxed(lean_object* v_j_648_, lean_object* v_k_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_j_648_, v_k_649_);
lean_dec_ref(v_k_649_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(size_t v_sz_651_, size_t v_i_652_, lean_object* v_bs_653_){
_start:
{
uint8_t v___x_654_; 
v___x_654_ = lean_usize_dec_lt(v_i_652_, v_sz_651_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v_bs_653_);
return v___x_655_;
}
else
{
lean_object* v_v_656_; lean_object* v___x_657_; 
v_v_656_ = lean_array_uget_borrowed(v_bs_653_, v_i_652_);
lean_inc(v_v_656_);
v___x_657_ = l_Lean_Json_getNat_x3f(v_v_656_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_bs_653_);
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_667_; lean_object* v_bs_x27_668_; size_t v___x_669_; size_t v___x_670_; lean_object* v___x_671_; 
v_a_666_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_657_, 1);
v___x_667_ = lean_unsigned_to_nat(0u);
v_bs_x27_668_ = lean_array_uset(v_bs_653_, v_i_652_, v___x_667_);
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_add(v_i_652_, v___x_669_);
v___x_671_ = lean_array_uset(v_bs_x27_668_, v_i_652_, v_a_666_);
v_i_652_ = v___x_670_;
v_bs_653_ = v___x_671_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9___boxed(lean_object* v_sz_673_, lean_object* v_i_674_, lean_object* v_bs_675_){
_start:
{
size_t v_sz_boxed_676_; size_t v_i_boxed_677_; lean_object* v_res_678_; 
v_sz_boxed_676_ = lean_unbox_usize(v_sz_673_);
lean_dec(v_sz_673_);
v_i_boxed_677_ = lean_unbox_usize(v_i_674_);
lean_dec(v_i_674_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(v_sz_boxed_676_, v_i_boxed_677_, v_bs_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7(lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_679_) == 4)
{
lean_object* v_elems_680_; size_t v_sz_681_; size_t v___x_682_; lean_object* v___x_683_; 
v_elems_680_ = lean_ctor_get(v_x_679_, 0);
lean_inc_ref(v_elems_680_);
lean_dec_ref_known(v_x_679_, 1);
v_sz_681_ = lean_array_size(v_elems_680_);
v___x_682_ = ((size_t)0ULL);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(v_sz_681_, v___x_682_, v_elems_680_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_684_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_685_ = lean_unsigned_to_nat(80u);
v___x_686_ = l_Lean_Json_pretty(v_x_679_, v___x_685_);
v___x_687_ = lean_string_append(v___x_684_, v___x_686_);
lean_dec_ref(v___x_686_);
v___x_688_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_689_ = lean_string_append(v___x_687_, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(lean_object* v_j_691_, lean_object* v_k_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l_Lean_Json_getObjValD(v_j_691_, v_k_692_);
v___x_694_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5___boxed(lean_object* v_j_695_, lean_object* v_k_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_j_695_, v_k_696_);
lean_dec_ref(v_k_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(size_t v_sz_698_, size_t v_i_699_, lean_object* v_bs_700_){
_start:
{
uint8_t v___x_701_; 
v___x_701_ = lean_usize_dec_lt(v_i_699_, v_sz_698_);
if (v___x_701_ == 0)
{
return v_bs_700_;
}
else
{
lean_object* v_v_702_; lean_object* v___x_703_; lean_object* v_bs_x27_704_; lean_object* v___x_705_; lean_object* v___x_706_; size_t v___x_707_; size_t v___x_708_; lean_object* v___x_709_; 
v_v_702_ = lean_array_uget(v_bs_700_, v_i_699_);
v___x_703_ = lean_unsigned_to_nat(0u);
v_bs_x27_704_ = lean_array_uset(v_bs_700_, v_i_699_, v___x_703_);
v___x_705_ = l_Lean_JsonNumber_fromNat(v_v_702_);
v___x_706_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_add(v_i_699_, v___x_707_);
v___x_709_ = lean_array_uset(v_bs_x27_704_, v_i_699_, v___x_706_);
v_i_699_ = v___x_708_;
v_bs_700_ = v___x_709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13___boxed(lean_object* v_sz_711_, lean_object* v_i_712_, lean_object* v_bs_713_){
_start:
{
size_t v_sz_boxed_714_; size_t v_i_boxed_715_; lean_object* v_res_716_; 
v_sz_boxed_714_ = lean_unbox_usize(v_sz_711_);
lean_dec(v_sz_711_);
v_i_boxed_715_ = lean_unbox_usize(v_i_712_);
lean_dec(v_i_712_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(v_sz_boxed_714_, v_i_boxed_715_, v_bs_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(lean_object* v_a_717_){
_start:
{
size_t v_sz_718_; size_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_sz_718_ = lean_array_size(v_a_717_);
v___x_719_ = ((size_t)0ULL);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(v_sz_718_, v___x_719_, v_a_717_);
v___x_721_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(lean_object* v_a_722_, lean_object* v_x_723_){
_start:
{
if (lean_obj_tag(v_x_723_) == 0)
{
uint8_t v___x_724_; 
v___x_724_ = 0;
return v___x_724_;
}
else
{
lean_object* v_key_725_; lean_object* v_tail_726_; uint8_t v___x_727_; 
v_key_725_ = lean_ctor_get(v_x_723_, 0);
v_tail_726_ = lean_ctor_get(v_x_723_, 2);
v___x_727_ = lean_nat_dec_eq(v_key_725_, v_a_722_);
if (v___x_727_ == 0)
{
v_x_723_ = v_tail_726_;
goto _start;
}
else
{
return v___x_727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg___boxed(lean_object* v_a_729_, lean_object* v_x_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_729_, v_x_730_);
lean_dec(v_x_730_);
lean_dec(v_a_729_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(lean_object* v_m_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_buckets_735_; lean_object* v___x_736_; uint64_t v___x_737_; uint64_t v___x_738_; uint64_t v___x_739_; uint64_t v_fold_740_; uint64_t v___x_741_; uint64_t v___x_742_; uint64_t v___x_743_; size_t v___x_744_; size_t v___x_745_; size_t v___x_746_; size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_buckets_735_ = lean_ctor_get(v_m_733_, 1);
v___x_736_ = lean_array_get_size(v_buckets_735_);
v___x_737_ = lean_uint64_of_nat(v_a_734_);
v___x_738_ = 32ULL;
v___x_739_ = lean_uint64_shift_right(v___x_737_, v___x_738_);
v_fold_740_ = lean_uint64_xor(v___x_737_, v___x_739_);
v___x_741_ = 16ULL;
v___x_742_ = lean_uint64_shift_right(v_fold_740_, v___x_741_);
v___x_743_ = lean_uint64_xor(v_fold_740_, v___x_742_);
v___x_744_ = lean_uint64_to_usize(v___x_743_);
v___x_745_ = lean_usize_of_nat(v___x_736_);
v___x_746_ = ((size_t)1ULL);
v___x_747_ = lean_usize_sub(v___x_745_, v___x_746_);
v___x_748_ = lean_usize_land(v___x_744_, v___x_747_);
v___x_749_ = lean_array_uget_borrowed(v_buckets_735_, v___x_748_);
v___x_750_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_734_, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg___boxed(lean_object* v_m_751_, lean_object* v_a_752_){
_start:
{
uint8_t v_res_753_; lean_object* v_r_754_; 
v_res_753_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_m_751_, v_a_752_);
lean_dec(v_a_752_);
lean_dec_ref(v_m_751_);
v_r_754_ = lean_box(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
if (lean_obj_tag(v_x_756_) == 0)
{
return v_x_755_;
}
else
{
lean_object* v_key_757_; lean_object* v_value_758_; lean_object* v_tail_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_782_; 
v_key_757_ = lean_ctor_get(v_x_756_, 0);
v_value_758_ = lean_ctor_get(v_x_756_, 1);
v_tail_759_ = lean_ctor_get(v_x_756_, 2);
v_isSharedCheck_782_ = !lean_is_exclusive(v_x_756_);
if (v_isSharedCheck_782_ == 0)
{
v___x_761_ = v_x_756_;
v_isShared_762_ = v_isSharedCheck_782_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_tail_759_);
lean_inc(v_value_758_);
lean_inc(v_key_757_);
lean_dec(v_x_756_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_782_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; uint64_t v___x_764_; uint64_t v___x_765_; uint64_t v___x_766_; uint64_t v_fold_767_; uint64_t v___x_768_; uint64_t v___x_769_; uint64_t v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_763_ = lean_array_get_size(v_x_755_);
v___x_764_ = lean_uint64_of_nat(v_key_757_);
v___x_765_ = 32ULL;
v___x_766_ = lean_uint64_shift_right(v___x_764_, v___x_765_);
v_fold_767_ = lean_uint64_xor(v___x_764_, v___x_766_);
v___x_768_ = 16ULL;
v___x_769_ = lean_uint64_shift_right(v_fold_767_, v___x_768_);
v___x_770_ = lean_uint64_xor(v_fold_767_, v___x_769_);
v___x_771_ = lean_uint64_to_usize(v___x_770_);
v___x_772_ = lean_usize_of_nat(v___x_763_);
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_sub(v___x_772_, v___x_773_);
v___x_775_ = lean_usize_land(v___x_771_, v___x_774_);
v___x_776_ = lean_array_uget_borrowed(v_x_755_, v___x_775_);
lean_inc(v___x_776_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 2, v___x_776_);
v___x_778_ = v___x_761_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_key_757_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_value_758_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v___x_776_);
v___x_778_ = v_reuseFailAlloc_781_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; 
v___x_779_ = lean_array_uset(v_x_755_, v___x_775_, v___x_778_);
v_x_755_ = v___x_779_;
v_x_756_ = v_tail_759_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(lean_object* v_i_783_, lean_object* v_source_784_, lean_object* v_target_785_){
_start:
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = lean_array_get_size(v_source_784_);
v___x_787_ = lean_nat_dec_lt(v_i_783_, v___x_786_);
if (v___x_787_ == 0)
{
lean_dec_ref(v_source_784_);
lean_dec(v_i_783_);
return v_target_785_;
}
else
{
lean_object* v_es_788_; lean_object* v___x_789_; lean_object* v_source_790_; lean_object* v_target_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_es_788_ = lean_array_fget(v_source_784_, v_i_783_);
v___x_789_ = lean_box(0);
v_source_790_ = lean_array_fset(v_source_784_, v_i_783_, v___x_789_);
v_target_791_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(v_target_785_, v_es_788_);
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v_i_783_, v___x_792_);
lean_dec(v_i_783_);
v_i_783_ = v___x_793_;
v_source_784_ = v_source_790_;
v_target_785_ = v_target_791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(lean_object* v_data_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_nbuckets_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_796_ = lean_array_get_size(v_data_795_);
v___x_797_ = lean_unsigned_to_nat(2u);
v_nbuckets_798_ = lean_nat_mul(v___x_796_, v___x_797_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_box(0);
v___x_801_ = lean_mk_array(v_nbuckets_798_, v___x_800_);
v___x_802_ = lean_array_propagate_mark(v_data_795_, v___x_801_);
v___x_803_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(v___x_799_, v_data_795_, v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(lean_object* v_m_804_, lean_object* v_a_805_, lean_object* v_b_806_){
_start:
{
lean_object* v_size_807_; lean_object* v_buckets_808_; lean_object* v___x_809_; uint64_t v___x_810_; uint64_t v___x_811_; uint64_t v___x_812_; uint64_t v_fold_813_; uint64_t v___x_814_; uint64_t v___x_815_; uint64_t v___x_816_; size_t v___x_817_; size_t v___x_818_; size_t v___x_819_; size_t v___x_820_; size_t v___x_821_; lean_object* v_bkt_822_; uint8_t v___x_823_; 
v_size_807_ = lean_ctor_get(v_m_804_, 0);
v_buckets_808_ = lean_ctor_get(v_m_804_, 1);
v___x_809_ = lean_array_get_size(v_buckets_808_);
v___x_810_ = lean_uint64_of_nat(v_a_805_);
v___x_811_ = 32ULL;
v___x_812_ = lean_uint64_shift_right(v___x_810_, v___x_811_);
v_fold_813_ = lean_uint64_xor(v___x_810_, v___x_812_);
v___x_814_ = 16ULL;
v___x_815_ = lean_uint64_shift_right(v_fold_813_, v___x_814_);
v___x_816_ = lean_uint64_xor(v_fold_813_, v___x_815_);
v___x_817_ = lean_uint64_to_usize(v___x_816_);
v___x_818_ = lean_usize_of_nat(v___x_809_);
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_sub(v___x_818_, v___x_819_);
v___x_821_ = lean_usize_land(v___x_817_, v___x_820_);
v_bkt_822_ = lean_array_uget_borrowed(v_buckets_808_, v___x_821_);
v___x_823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_805_, v_bkt_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_844_; 
lean_inc_ref(v_buckets_808_);
lean_inc(v_size_807_);
v_isSharedCheck_844_ = !lean_is_exclusive(v_m_804_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; lean_object* v_unused_846_; 
v_unused_845_ = lean_ctor_get(v_m_804_, 1);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_m_804_, 0);
lean_dec(v_unused_846_);
v___x_825_ = v_m_804_;
v_isShared_826_ = v_isSharedCheck_844_;
goto v_resetjp_824_;
}
else
{
lean_dec(v_m_804_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_844_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v_size_x27_828_; lean_object* v___x_829_; lean_object* v_buckets_x27_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_827_ = lean_unsigned_to_nat(1u);
v_size_x27_828_ = lean_nat_add(v_size_807_, v___x_827_);
lean_dec(v_size_807_);
lean_inc(v_bkt_822_);
v___x_829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_829_, 0, v_a_805_);
lean_ctor_set(v___x_829_, 1, v_b_806_);
lean_ctor_set(v___x_829_, 2, v_bkt_822_);
v_buckets_x27_830_ = lean_array_uset(v_buckets_808_, v___x_821_, v___x_829_);
v___x_831_ = lean_unsigned_to_nat(4u);
v___x_832_ = lean_nat_mul(v_size_x27_828_, v___x_831_);
v___x_833_ = lean_unsigned_to_nat(3u);
v___x_834_ = lean_nat_div(v___x_832_, v___x_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_array_get_size(v_buckets_x27_830_);
v___x_836_ = lean_nat_dec_le(v___x_834_, v___x_835_);
lean_dec(v___x_834_);
if (v___x_836_ == 0)
{
lean_object* v_val_837_; lean_object* v___x_839_; 
v_val_837_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(v_buckets_x27_830_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v_val_837_);
lean_ctor_set(v___x_825_, 0, v_size_x27_828_);
v___x_839_ = v___x_825_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_size_x27_828_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_val_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
lean_object* v___x_842_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v_buckets_x27_830_);
lean_ctor_set(v___x_825_, 0, v_size_x27_828_);
v___x_842_ = v___x_825_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_size_x27_828_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_buckets_x27_830_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_dec(v_b_806_);
lean_dec(v_a_805_);
return v_m_804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_as_850_, size_t v_sz_851_, size_t v_i_852_, lean_object* v_b_853_){
_start:
{
lean_object* v_a_856_; uint8_t v___x_860_; 
v___x_860_ = lean_usize_dec_lt(v_i_852_, v_sz_851_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v_b_853_);
return v___x_861_;
}
else
{
lean_object* v_snd_862_; lean_object* v_snd_863_; lean_object* v_snd_864_; lean_object* v_fst_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_949_; 
v_snd_862_ = lean_ctor_get(v_b_853_, 1);
lean_inc(v_snd_862_);
v_snd_863_ = lean_ctor_get(v_snd_862_, 1);
lean_inc(v_snd_863_);
v_snd_864_ = lean_ctor_get(v_snd_863_, 1);
lean_inc(v_snd_864_);
v_fst_865_ = lean_ctor_get(v_b_853_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_b_853_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v_b_853_, 1);
lean_dec(v_unused_950_);
v___x_867_ = v_b_853_;
v_isShared_868_ = v_isSharedCheck_949_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_fst_865_);
lean_dec(v_b_853_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_949_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_fst_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_947_; 
v_fst_869_ = lean_ctor_get(v_snd_862_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v_snd_862_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v_snd_862_, 1);
lean_dec(v_unused_948_);
v___x_871_ = v_snd_862_;
v_isShared_872_ = v_isSharedCheck_947_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_fst_869_);
lean_dec(v_snd_862_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_947_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_fst_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_945_; 
v_fst_873_ = lean_ctor_get(v_snd_863_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_snd_863_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v_snd_863_, 1);
lean_dec(v_unused_946_);
v___x_875_ = v_snd_863_;
v_isShared_876_ = v_isSharedCheck_945_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_fst_873_);
lean_dec(v_snd_863_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_945_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_array_877_; lean_object* v_start_878_; lean_object* v_stop_879_; uint8_t v___x_880_; 
v_array_877_ = lean_ctor_get(v_snd_864_, 0);
v_start_878_ = lean_ctor_get(v_snd_864_, 1);
v_stop_879_ = lean_ctor_get(v_snd_864_, 2);
v___x_880_ = lean_nat_dec_lt(v_start_878_, v_stop_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_882_; 
if (v_isShared_876_ == 0)
{
v___x_882_ = v___x_875_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_fst_873_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_snd_864_);
v___x_882_ = v_reuseFailAlloc_890_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v___x_882_);
v___x_884_ = v___x_871_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_fst_869_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_889_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_884_);
v___x_886_ = v___x_867_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_fst_865_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_888_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
}
}
}
else
{
lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_941_; 
lean_inc(v_stop_879_);
lean_inc(v_start_878_);
lean_inc_ref(v_array_877_);
v_isSharedCheck_941_ = !lean_is_exclusive(v_snd_864_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; lean_object* v_unused_943_; lean_object* v_unused_944_; 
v_unused_942_ = lean_ctor_get(v_snd_864_, 2);
lean_dec(v_unused_942_);
v_unused_943_ = lean_ctor_get(v_snd_864_, 1);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_snd_864_, 0);
lean_dec(v_unused_944_);
v___x_892_ = v_snd_864_;
v_isShared_893_ = v_isSharedCheck_941_;
goto v_resetjp_891_;
}
else
{
lean_dec(v_snd_864_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_941_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_a_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v_a_894_ = lean_array_uget_borrowed(v_as_850_, v_i_852_);
v___x_895_ = lean_array_fget(v_array_877_, v_start_878_);
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_nat_add(v_start_878_, v___x_896_);
lean_dec(v_start_878_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v___x_897_);
v___x_899_ = v___x_892_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_array_877_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_stop_879_);
v___x_899_ = v_reuseFailAlloc_940_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
uint8_t v___x_910_; 
v___x_910_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_fst_865_, v_a_894_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Json_getNat_x3f(v___x_895_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_dec_ref_known(v___x_911_, 1);
goto v___jp_900_;
}
else
{
lean_object* v_a_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = lean_array_get_size(v_a_847_);
v___x_914_ = lean_nat_dec_lt(v_a_894_, v___x_913_);
if (v___x_914_ == 0)
{
lean_dec(v_a_912_);
goto v___jp_900_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_array_fget_borrowed(v_a_847_, v_a_894_);
lean_inc(v___x_915_);
v___x_916_ = l_Lean_Json_getNat_x3f(v___x_915_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_dec_ref_known(v___x_916_, 1);
lean_dec(v_a_912_);
goto v___jp_900_;
}
else
{
lean_object* v_a_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = lean_array_get_size(v_a_848_);
v___x_919_ = lean_nat_dec_lt(v_a_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_dec(v_a_917_);
lean_dec(v_a_912_);
goto v___jp_900_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_array_fget_borrowed(v_a_848_, v_a_917_);
lean_dec(v_a_917_);
lean_inc(v___x_920_);
v___x_921_ = l_Lean_Json_getNat_x3f(v___x_920_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_dec_ref_known(v___x_921_, 1);
lean_dec(v_a_912_);
goto v___jp_900_;
}
else
{
lean_object* v_a_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v___x_923_ = lean_array_get_size(v_a_849_);
v___x_924_ = lean_nat_dec_lt(v_a_922_, v___x_923_);
if (v___x_924_ == 0)
{
lean_dec(v_a_922_);
lean_dec(v_a_912_);
goto v___jp_900_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_del_object(v___x_875_);
lean_del_object(v___x_871_);
lean_del_object(v___x_867_);
v___x_925_ = lean_box(0);
lean_inc_n(v_a_894_, 2);
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(v_fst_865_, v_a_894_, v___x_925_);
v___x_927_ = lean_unsigned_to_nat(2u);
v___x_928_ = lean_mk_empty_array_with_capacity(v___x_927_);
v___x_929_ = lean_array_push(v___x_928_, v_a_922_);
v___x_930_ = lean_array_push(v___x_929_, v_a_912_);
v___x_931_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(v___x_930_);
v___x_932_ = lean_array_push(v_fst_869_, v___x_931_);
v___x_933_ = lean_array_push(v_fst_873_, v_a_894_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_899_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_932_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_926_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v_a_856_ = v___x_936_;
goto v___jp_855_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec(v___x_895_);
lean_del_object(v___x_875_);
lean_del_object(v___x_871_);
lean_del_object(v___x_867_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_fst_873_);
lean_ctor_set(v___x_937_, 1, v___x_899_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_fst_869_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_fst_865_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v_a_856_ = v___x_939_;
goto v___jp_855_;
}
v___jp_900_:
{
lean_object* v___x_902_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v___x_899_);
v___x_902_ = v___x_875_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_fst_873_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v___x_899_);
v___x_902_ = v_reuseFailAlloc_909_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v___x_902_);
v___x_904_ = v___x_871_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_fst_869_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v___x_902_);
v___x_904_ = v_reuseFailAlloc_908_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_906_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_904_);
v___x_906_ = v___x_867_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_fst_865_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
v_a_856_ = v___x_906_;
goto v___jp_855_;
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
v___jp_855_:
{
size_t v___x_857_; size_t v___x_858_; 
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_add(v_i_852_, v___x_857_);
v_i_852_ = v___x_858_;
v_b_853_ = v_a_856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9___boxed(lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_as_954_, lean_object* v_sz_955_, lean_object* v_i_956_, lean_object* v_b_957_, lean_object* v___y_958_){
_start:
{
size_t v_sz_boxed_959_; size_t v_i_boxed_960_; lean_object* v_res_961_; 
v_sz_boxed_959_ = lean_unbox_usize(v_sz_955_);
lean_dec(v_sz_955_);
v_i_boxed_960_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(v_a_951_, v_a_952_, v_a_953_, v_as_954_, v_sz_boxed_959_, v_i_boxed_960_, v_b_957_);
lean_dec_ref(v_as_954_);
lean_dec_ref(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec_ref(v_a_951_);
return v_res_961_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = lean_box(0);
v___x_972_ = lean_unsigned_to_nat(16u);
v___x_973_ = lean_mk_array(v___x_972_, v___x_971_);
return v___x_973_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8);
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(lean_object* v_a_977_, lean_object* v_as_978_, size_t v_sz_979_, size_t v_i_980_, lean_object* v_b_981_){
_start:
{
uint8_t v___x_983_; 
v___x_983_ = lean_usize_dec_lt(v_i_980_, v_sz_979_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v_b_981_);
return v___x_984_;
}
else
{
lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1115_; 
v_fst_985_ = lean_ctor_get(v_b_981_, 0);
v_snd_986_ = lean_ctor_get(v_b_981_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_b_981_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_988_ = v_b_981_;
v_isShared_989_ = v_isSharedCheck_1115_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snd_986_);
lean_inc(v_fst_985_);
lean_dec(v_b_981_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1115_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__0));
v_a_992_ = lean_array_uget_borrowed(v_as_978_, v_i_980_);
v___x_993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__1));
lean_inc(v_a_992_);
v___x_994_ = l_Lean_Json_getObjVal_x3f(v_a_992_, v___x_993_);
v___x_995_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_994_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v___x_997_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2));
lean_inc(v_a_992_);
v___x_998_ = l_Lean_Json_getObjVal_x3f(v_a_992_, v___x_997_);
v___x_999_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__3));
lean_inc(v_a_992_);
v___x_1002_ = l_Lean_Json_getObjVal_x3f(v_a_992_, v___x_1001_);
v___x_1003_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__4));
lean_inc(v_a_996_);
v___x_1006_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_a_996_, v___x_1005_);
v___x_1007_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__5));
v___x_1010_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_996_, v___x_1009_);
v___x_1011_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__6));
v___x_1014_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_1000_, v___x_1013_);
v___x_1015_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1014_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__7));
v___x_1018_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_1004_, v___x_1017_);
v___x_1019_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1018_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___x_1021_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9);
v___x_1022_ = lean_array_get_size(v_a_1012_);
v___x_1023_ = l_Array_toSubarray___redArg(v_a_1012_, v___x_990_, v___x_1022_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v___x_1023_);
lean_ctor_set(v___x_988_, 0, v___x_991_);
v___x_1025_ = v___x_988_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; size_t v_sz_1028_; size_t v___x_1029_; lean_object* v___x_1030_; 
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_991_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1021_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v_sz_1028_ = lean_array_size(v_a_1008_);
v___x_1029_ = ((size_t)0ULL);
v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(v_a_1016_, v_a_1020_, v_a_977_, v_a_1008_, v_sz_1028_, v___x_1029_, v___x_1027_);
lean_dec(v_a_1008_);
lean_dec(v_a_1020_);
lean_dec(v_a_1016_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v_snd_1032_; lean_object* v_snd_1033_; lean_object* v_fst_1034_; lean_object* v_fst_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1048_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v___x_1030_, 1);
v_snd_1032_ = lean_ctor_get(v_a_1031_, 1);
lean_inc(v_snd_1032_);
lean_dec(v_a_1031_);
v_snd_1033_ = lean_ctor_get(v_snd_1032_, 1);
lean_inc(v_snd_1033_);
v_fst_1034_ = lean_ctor_get(v_snd_1032_, 0);
lean_inc(v_fst_1034_);
lean_dec(v_snd_1032_);
v_fst_1035_ = lean_ctor_get(v_snd_1033_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_snd_1033_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v_snd_1033_, 1);
lean_dec(v_unused_1049_);
v___x_1037_ = v_snd_1033_;
v_isShared_1038_ = v_isSharedCheck_1048_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_fst_1035_);
lean_dec(v_snd_1033_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1048_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1039_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1039_, 0, v_fst_1034_);
v___x_1040_ = lean_array_push(v_fst_985_, v___x_1039_);
v___x_1041_ = lean_array_push(v_snd_986_, v_fst_1035_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___x_1041_);
lean_ctor_set(v___x_1037_, 0, v___x_1040_);
v___x_1043_ = v___x_1037_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
size_t v___x_1044_; size_t v___x_1045_; 
v___x_1044_ = ((size_t)1ULL);
v___x_1045_ = lean_usize_add(v_i_980_, v___x_1044_);
v_i_980_ = v___x_1045_;
v_b_981_ = v___x_1043_;
goto _start;
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
v_a_1050_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1030_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1030_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v_a_1016_);
lean_dec(v_a_1012_);
lean_dec(v_a_1008_);
lean_del_object(v___x_988_);
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
v_a_1059_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1019_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1019_);
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
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec(v_a_1012_);
lean_dec(v_a_1008_);
lean_dec(v_a_1004_);
lean_del_object(v___x_988_);
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
v_a_1067_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1015_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1015_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_a_1008_);
lean_dec(v_a_1004_);
lean_dec(v_a_1000_);
lean_del_object(v___x_988_);
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
v_a_1075_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1011_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1011_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec(v_a_1004_);
lean_dec(v_a_1000_);
lean_dec(v_a_996_);
lean_del_object(v___x_988_);
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
v_a_1083_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1007_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1007_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_a_1000_);
lean_dec(v_a_996_);
lean_del_object(v___x_988_);
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
v_a_1091_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1003_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1003_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_a_996_);
lean_del_object(v___x_988_);
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
v_a_1099_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_999_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_999_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_del_object(v___x_988_);
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
v_a_1107_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_995_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_995_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___boxed(lean_object* v_a_1116_, lean_object* v_as_1117_, lean_object* v_sz_1118_, lean_object* v_i_1119_, lean_object* v_b_1120_, lean_object* v___y_1121_){
_start:
{
size_t v_sz_boxed_1122_; size_t v_i_boxed_1123_; lean_object* v_res_1124_; 
v_sz_boxed_1122_ = lean_unbox_usize(v_sz_1118_);
lean_dec(v_sz_1118_);
v_i_boxed_1123_ = lean_unbox_usize(v_i_1119_);
lean_dec(v_i_1119_);
v_res_1124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(v_a_1116_, v_as_1117_, v_sz_boxed_1122_, v_i_boxed_1123_, v_b_1120_);
lean_dec_ref(v_as_1117_);
lean_dec_ref(v_a_1116_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(size_t v_sz_1125_, size_t v_i_1126_, lean_object* v_bs_1127_){
_start:
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_usize_dec_lt(v_i_1126_, v_sz_1125_);
if (v___x_1128_ == 0)
{
return v_bs_1127_;
}
else
{
lean_object* v_v_1129_; lean_object* v___x_1130_; lean_object* v_bs_x27_1131_; lean_object* v___x_1132_; size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
v_v_1129_ = lean_array_uget(v_bs_1127_, v_i_1126_);
v___x_1130_ = lean_unsigned_to_nat(0u);
v_bs_x27_1131_ = lean_array_uset(v_bs_1127_, v_i_1126_, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_v_1129_);
v___x_1133_ = ((size_t)1ULL);
v___x_1134_ = lean_usize_add(v_i_1126_, v___x_1133_);
v___x_1135_ = lean_array_uset(v_bs_x27_1131_, v_i_1126_, v___x_1132_);
v_i_1126_ = v___x_1134_;
v_bs_1127_ = v___x_1135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2___boxed(lean_object* v_sz_1137_, lean_object* v_i_1138_, lean_object* v_bs_1139_){
_start:
{
size_t v_sz_boxed_1140_; size_t v_i_boxed_1141_; lean_object* v_res_1142_; 
v_sz_boxed_1140_ = lean_unbox_usize(v_sz_1137_);
lean_dec(v_sz_1137_);
v_i_boxed_1141_ = lean_unbox_usize(v_i_1138_);
lean_dec(v_i_1138_);
v_res_1142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(v_sz_boxed_1140_, v_i_boxed_1141_, v_bs_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(lean_object* v_a_1143_){
_start:
{
size_t v_sz_1144_; size_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_sz_1144_ = lean_array_size(v_a_1143_);
v___x_1145_ = ((size_t)0ULL);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(v_sz_1144_, v___x_1145_, v_a_1143_);
v___x_1147_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(size_t v_sz_1150_, size_t v_i_1151_, lean_object* v_bs_1152_){
_start:
{
uint8_t v___x_1154_; 
v___x_1154_ = lean_usize_dec_lt(v_i_1151_, v_sz_1150_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_bs_1152_);
return v___x_1155_;
}
else
{
lean_object* v_v_1156_; lean_object* v___x_1157_; lean_object* v_bs_x27_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_v_1156_ = lean_array_uget(v_bs_1152_, v_i_1151_);
v___x_1157_ = lean_unsigned_to_nat(0u);
v_bs_x27_1158_ = lean_array_uset(v_bs_1152_, v_i_1151_, v___x_1157_);
v___x_1159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__0));
lean_inc(v_v_1156_);
v___x_1160_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_v_1156_, v___x_1159_);
v___x_1161_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1160_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__1));
v___x_1164_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_v_1156_, v___x_1163_);
v___x_1165_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1164_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; lean_object* v___x_1174_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = lean_unsigned_to_nat(2u);
v___x_1168_ = lean_mk_empty_array_with_capacity(v___x_1167_);
v___x_1169_ = lean_array_push(v___x_1168_, v_a_1162_);
v___x_1170_ = lean_array_push(v___x_1169_, v_a_1166_);
v___x_1171_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(v___x_1170_);
v___x_1172_ = ((size_t)1ULL);
v___x_1173_ = lean_usize_add(v_i_1151_, v___x_1172_);
v___x_1174_ = lean_array_uset(v_bs_x27_1158_, v_i_1151_, v___x_1171_);
v_i_1151_ = v___x_1173_;
v_bs_1152_ = v___x_1174_;
goto _start;
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_a_1162_);
lean_dec_ref(v_bs_x27_1158_);
v_a_1176_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1165_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1165_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v_bs_x27_1158_);
lean_dec(v_v_1156_);
v_a_1184_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1161_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1161_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___boxed(lean_object* v_sz_1192_, lean_object* v_i_1193_, lean_object* v_bs_1194_, lean_object* v___y_1195_){
_start:
{
size_t v_sz_boxed_1196_; size_t v_i_boxed_1197_; lean_object* v_res_1198_; 
v_sz_boxed_1196_ = lean_unbox_usize(v_sz_1192_);
lean_dec(v_sz_1192_);
v_i_boxed_1197_ = lean_unbox_usize(v_i_1193_);
lean_dec(v_i_1193_);
v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(v_sz_boxed_1196_, v_i_boxed_1197_, v_bs_1194_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(lean_object* v_profile_1205_){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__0));
lean_inc(v_profile_1205_);
v___x_1208_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1205_, v___x_1207_);
v___x_1209_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1208_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; size_t v_sz_1211_; size_t v___x_1212_; lean_object* v___x_1213_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc_n(v_a_1210_, 2);
lean_dec_ref_known(v___x_1209_, 1);
v_sz_1211_ = lean_array_size(v_a_1210_);
v___x_1212_ = ((size_t)0ULL);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(v_sz_1211_, v___x_1212_, v_a_1210_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v___x_1215_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1));
v___x_1216_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1205_, v___x_1215_);
v___x_1217_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; size_t v_sz_1220_; lean_object* v___x_1221_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v___x_1219_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__2));
v_sz_1220_ = lean_array_size(v_a_1218_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(v_a_1210_, v_a_1218_, v_sz_1220_, v___x_1212_, v___x_1219_);
lean_dec(v_a_1218_);
lean_dec(v_a_1210_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1248_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1248_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1248_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_fst_1226_; lean_object* v_snd_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1247_; 
v_fst_1226_ = lean_ctor_get(v_a_1222_, 0);
v_snd_1227_ = lean_ctor_get(v_a_1222_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_a_1222_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1229_ = v_a_1222_;
v_isShared_1230_ = v_isSharedCheck_1247_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_snd_1227_);
lean_inc(v_fst_1226_);
lean_dec(v_a_1222_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1247_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1231_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__3));
v___x_1232_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_a_1214_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v___x_1232_);
lean_ctor_set(v___x_1229_, 0, v___x_1231_);
v___x_1234_ = v___x_1229_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1235_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4));
v___x_1236_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_fst_1226_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = lean_box(0);
v___x_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1234_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = l_Lean_Json_mkObj(v___x_1240_);
lean_dec_ref_known(v___x_1240_, 2);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v_snd_1227_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1242_);
v___x_1244_ = v___x_1224_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_a_1214_);
v_a_1249_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1221_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1221_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_a_1214_);
lean_dec(v_a_1210_);
v_a_1257_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1217_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1217_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_a_1210_);
lean_dec(v_profile_1205_);
v_a_1265_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1213_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1213_);
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
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_profile_1205_);
v_a_1273_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1209_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1209_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___boxed(lean_object* v_profile_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(v_profile_1281_);
return v_res_1283_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(lean_object* v_00_u03b2_1284_, lean_object* v_m_1285_, lean_object* v_a_1286_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_m_1285_, v_a_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___boxed(lean_object* v_00_u03b2_1288_, lean_object* v_m_1289_, lean_object* v_a_1290_){
_start:
{
uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_res_1291_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(v_00_u03b2_1288_, v_m_1289_, v_a_1290_);
lean_dec(v_a_1290_);
lean_dec_ref(v_m_1289_);
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7(lean_object* v_00_u03b2_1293_, lean_object* v_m_1294_, lean_object* v_a_1295_, lean_object* v_b_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(v_m_1294_, v_a_1295_, v_b_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(lean_object* v_00_u03b2_1298_, lean_object* v_a_1299_, lean_object* v_x_1300_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_1299_, v_x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1302_, lean_object* v_a_1303_, lean_object* v_x_1304_){
_start:
{
uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_res_1305_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(v_00_u03b2_1302_, v_a_1303_, v_x_1304_);
lean_dec(v_x_1304_);
lean_dec(v_a_1303_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11(lean_object* v_00_u03b2_1307_, lean_object* v_data_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(v_data_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14(lean_object* v_00_u03b2_1310_, lean_object* v_i_1311_, lean_object* v_source_1312_, lean_object* v_target_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(v_i_1311_, v_source_1312_, v_target_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18(lean_object* v_00_u03b2_1315_, lean_object* v_x_1316_, lean_object* v_x_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(v_x_1316_, v_x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(size_t v_sz_1319_, size_t v_i_1320_, lean_object* v_bs_1321_){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_usize_dec_lt(v_i_1320_, v_sz_1319_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_bs_1321_);
return v___x_1323_;
}
else
{
lean_object* v_v_1324_; lean_object* v___x_1325_; 
v_v_1324_ = lean_array_uget_borrowed(v_bs_1321_, v_i_1320_);
lean_inc(v_v_1324_);
v___x_1325_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(v_v_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v_bs_1321_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1335_; lean_object* v_bs_x27_1336_; size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; 
v_a_1334_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1335_ = lean_unsigned_to_nat(0u);
v_bs_x27_1336_ = lean_array_uset(v_bs_1321_, v_i_1320_, v___x_1335_);
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_add(v_i_1320_, v___x_1337_);
v___x_1339_ = lean_array_uset(v_bs_x27_1336_, v_i_1320_, v_a_1334_);
v_i_1320_ = v___x_1338_;
v_bs_1321_ = v___x_1339_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1341_, lean_object* v_i_1342_, lean_object* v_bs_1343_){
_start:
{
size_t v_sz_boxed_1344_; size_t v_i_boxed_1345_; lean_object* v_res_1346_; 
v_sz_boxed_1344_ = lean_unbox_usize(v_sz_1341_);
lean_dec(v_sz_1341_);
v_i_boxed_1345_ = lean_unbox_usize(v_i_1342_);
lean_dec(v_i_1342_);
v_res_1346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(v_sz_boxed_1344_, v_i_boxed_1345_, v_bs_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0(lean_object* v_x_1347_){
_start:
{
if (lean_obj_tag(v_x_1347_) == 4)
{
lean_object* v_elems_1348_; size_t v_sz_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v_elems_1348_ = lean_ctor_get(v_x_1347_, 0);
lean_inc_ref(v_elems_1348_);
lean_dec_ref_known(v_x_1347_, 1);
v_sz_1349_ = lean_array_size(v_elems_1348_);
v___x_1350_ = ((size_t)0ULL);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(v_sz_1349_, v___x_1350_, v_elems_1348_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1352_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_1353_ = lean_unsigned_to_nat(80u);
v___x_1354_ = l_Lean_Json_pretty(v_x_1347_, v___x_1353_);
v___x_1355_ = lean_string_append(v___x_1352_, v___x_1354_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_1357_ = lean_string_append(v___x_1355_, v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(lean_object* v_j_1359_, lean_object* v_k_1360_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = l_Lean_Json_getObjValD(v_j_1359_, v_k_1360_);
v___x_1362_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0(v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0___boxed(lean_object* v_j_1363_, lean_object* v_k_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(v_j_1363_, v_k_1364_);
lean_dec_ref(v_k_1364_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(size_t v_sz_1366_, size_t v_i_1367_, lean_object* v_bs_1368_){
_start:
{
uint8_t v___x_1369_; 
v___x_1369_ = lean_usize_dec_lt(v_i_1367_, v_sz_1366_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v_bs_1368_);
return v___x_1370_;
}
else
{
lean_object* v_v_1371_; lean_object* v___x_1372_; 
v_v_1371_ = lean_array_uget_borrowed(v_bs_1368_, v_i_1367_);
lean_inc(v_v_1371_);
v___x_1372_ = l_Lean_Json_getStr_x3f(v_v_1371_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v_bs_1368_);
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1382_; lean_object* v_bs_x27_1383_; size_t v___x_1384_; size_t v___x_1385_; lean_object* v___x_1386_; 
v_a_1381_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1382_ = lean_unsigned_to_nat(0u);
v_bs_x27_1383_ = lean_array_uset(v_bs_1368_, v_i_1367_, v___x_1382_);
v___x_1384_ = ((size_t)1ULL);
v___x_1385_ = lean_usize_add(v_i_1367_, v___x_1384_);
v___x_1386_ = lean_array_uset(v_bs_x27_1383_, v_i_1367_, v_a_1381_);
v_i_1367_ = v___x_1385_;
v_bs_1368_ = v___x_1386_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_1388_, lean_object* v_i_1389_, lean_object* v_bs_1390_){
_start:
{
size_t v_sz_boxed_1391_; size_t v_i_boxed_1392_; lean_object* v_res_1393_; 
v_sz_boxed_1391_ = lean_unbox_usize(v_sz_1388_);
lean_dec(v_sz_1388_);
v_i_boxed_1392_ = lean_unbox_usize(v_i_1389_);
lean_dec(v_i_1389_);
v_res_1393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(v_sz_boxed_1391_, v_i_boxed_1392_, v_bs_1390_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2(lean_object* v_x_1394_){
_start:
{
if (lean_obj_tag(v_x_1394_) == 4)
{
lean_object* v_elems_1395_; size_t v_sz_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
v_elems_1395_ = lean_ctor_get(v_x_1394_, 0);
lean_inc_ref(v_elems_1395_);
lean_dec_ref_known(v_x_1394_, 1);
v_sz_1396_ = lean_array_size(v_elems_1395_);
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(v_sz_1396_, v___x_1397_, v_elems_1395_);
return v___x_1398_;
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1399_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_1400_ = lean_unsigned_to_nat(80u);
v___x_1401_ = l_Lean_Json_pretty(v_x_1394_, v___x_1400_);
v___x_1402_ = lean_string_append(v___x_1399_, v___x_1401_);
lean_dec_ref(v___x_1401_);
v___x_1403_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_1404_ = lean_string_append(v___x_1402_, v___x_1403_);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(lean_object* v_j_1406_, lean_object* v_k_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = l_Lean_Json_getObjValD(v_j_1406_, v_k_1407_);
v___x_1409_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2(v___x_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1___boxed(lean_object* v_j_1410_, lean_object* v_k_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(v_j_1410_, v_k_1411_);
lean_dec_ref(v_k_1411_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(lean_object* v_as_1414_, size_t v_sz_1415_, size_t v_i_1416_, lean_object* v_b_1417_){
_start:
{
lean_object* v_a_1420_; uint8_t v___x_1424_; 
v___x_1424_ = lean_usize_dec_lt(v_i_1416_, v_sz_1415_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_b_1417_);
return v___x_1425_;
}
else
{
lean_object* v_snd_1426_; lean_object* v_snd_1427_; lean_object* v_fst_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1488_; 
v_snd_1426_ = lean_ctor_get(v_b_1417_, 1);
lean_inc(v_snd_1426_);
v_snd_1427_ = lean_ctor_get(v_snd_1426_, 1);
lean_inc(v_snd_1427_);
v_fst_1428_ = lean_ctor_get(v_b_1417_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_b_1417_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_b_1417_, 1);
lean_dec(v_unused_1489_);
v___x_1430_ = v_b_1417_;
v_isShared_1431_ = v_isSharedCheck_1488_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_fst_1428_);
lean_dec(v_b_1417_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1488_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_fst_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1486_; 
v_fst_1432_ = lean_ctor_get(v_snd_1426_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_snd_1426_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v_snd_1426_, 1);
lean_dec(v_unused_1487_);
v___x_1434_ = v_snd_1426_;
v_isShared_1435_ = v_isSharedCheck_1486_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_fst_1432_);
lean_dec(v_snd_1426_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1486_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_array_1436_; lean_object* v_start_1437_; lean_object* v_stop_1438_; uint8_t v___x_1439_; 
v_array_1436_ = lean_ctor_get(v_snd_1427_, 0);
v_start_1437_ = lean_ctor_get(v_snd_1427_, 1);
v_stop_1438_ = lean_ctor_get(v_snd_1427_, 2);
v___x_1439_ = lean_nat_dec_lt(v_start_1437_, v_stop_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1441_; 
if (v_isShared_1435_ == 0)
{
v___x_1441_ = v___x_1434_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_fst_1432_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_snd_1427_);
v___x_1441_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 1, v___x_1441_);
v___x_1443_ = v___x_1430_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_fst_1428_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
}
}
else
{
lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1482_; 
lean_inc(v_stop_1438_);
lean_inc(v_start_1437_);
lean_inc_ref(v_array_1436_);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_snd_1427_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; 
v_unused_1483_ = lean_ctor_get(v_snd_1427_, 2);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_snd_1427_, 1);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_snd_1427_, 0);
lean_dec(v_unused_1485_);
v___x_1448_ = v_snd_1427_;
v_isShared_1449_ = v_isSharedCheck_1482_;
goto v_resetjp_1447_;
}
else
{
lean_dec(v_snd_1427_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1482_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v_a_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v_a_1450_ = lean_array_uget_borrowed(v_as_1414_, v_i_1416_);
v___x_1451_ = lean_array_fget(v_array_1436_, v_start_1437_);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v_start_1437_, v___x_1452_);
lean_dec(v_start_1437_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 1, v___x_1453_);
v___x_1455_ = v___x_1448_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_array_1436_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_stop_1438_);
v___x_1455_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___y_1457_; lean_object* v___y_1468_; lean_object* v___x_1478_; 
lean_inc(v___x_1451_);
v___x_1478_ = l_Lean_Json_getStr_x3f(v___x_1451_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec_ref_known(v___x_1478_, 1);
v___x_1479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___closed__0));
v___x_1480_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v___x_1451_, v___x_1479_);
v___y_1468_ = v___x_1480_;
goto v___jp_1467_;
}
else
{
lean_dec(v___x_1451_);
v___y_1468_ = v___x_1478_;
goto v___jp_1467_;
}
v___jp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1458_ = lean_array_get_size(v_fst_1432_);
v___x_1459_ = lean_array_fset(v_fst_1428_, v_a_1450_, v___x_1458_);
v___x_1460_ = lean_array_push(v_fst_1432_, v___y_1457_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v___x_1455_);
lean_ctor_set(v___x_1434_, 0, v___x_1460_);
v___x_1462_ = v___x_1434_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___x_1455_);
v___x_1462_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 1, v___x_1462_);
lean_ctor_set(v___x_1430_, 0, v___x_1459_);
v___x_1464_ = v___x_1430_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
v_a_1420_ = v___x_1464_;
goto v___jp_1419_;
}
}
}
v___jp_1467_:
{
if (lean_obj_tag(v___y_1468_) == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec_ref_known(v___y_1468_, 1);
lean_del_object(v___x_1434_);
lean_del_object(v___x_1430_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_fst_1432_);
lean_ctor_set(v___x_1469_, 1, v___x_1455_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_fst_1428_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v_a_1420_ = v___x_1470_;
goto v___jp_1419_;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_a_1471_ = lean_ctor_get(v___y_1468_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___y_1468_, 1);
v___x_1472_ = lean_array_get_size(v_fst_1428_);
v___x_1473_ = lean_nat_dec_lt(v_a_1450_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v_a_1471_);
lean_del_object(v___x_1434_);
lean_del_object(v___x_1430_);
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v_fst_1432_);
lean_ctor_set(v___x_1474_, 1, v___x_1455_);
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v_fst_1428_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v_a_1420_ = v___x_1475_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1476_; 
lean_inc(v_a_1471_);
v___x_1476_ = l_Lean_Name_Demangle_demangleSymbol(v_a_1471_);
if (lean_obj_tag(v___x_1476_) == 0)
{
v___y_1457_ = v_a_1471_;
goto v___jp_1456_;
}
else
{
lean_object* v_val_1477_; 
lean_dec(v_a_1471_);
v_val_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_val_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v___y_1457_ = v_val_1477_;
goto v___jp_1456_;
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
v___jp_1419_:
{
size_t v___x_1421_; size_t v___x_1422_; 
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_add(v_i_1416_, v___x_1421_);
v_i_1416_ = v___x_1422_;
v_b_1417_ = v_a_1420_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___boxed(lean_object* v_as_1490_, lean_object* v_sz_1491_, lean_object* v_i_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_){
_start:
{
size_t v_sz_boxed_1495_; size_t v_i_boxed_1496_; lean_object* v_res_1497_; 
v_sz_boxed_1495_ = lean_unbox_usize(v_sz_1491_);
lean_dec(v_sz_1491_);
v_i_boxed_1496_ = lean_unbox_usize(v_i_1492_);
lean_dec(v_i_1492_);
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(v_as_1490_, v_sz_boxed_1495_, v_i_boxed_1496_, v_b_1493_);
lean_dec_ref(v_as_1490_);
return v_res_1497_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Array_instInhabited___redArg();
return v___x_1498_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__1));
v___x_1501_ = lean_mk_io_user_error(v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(lean_object* v_a_1504_, lean_object* v_funcMaps_1505_, size_t v_sz_1506_, size_t v_i_1507_, lean_object* v_bs_1508_){
_start:
{
uint8_t v___x_1510_; 
v___x_1510_ = lean_usize_dec_lt(v_i_1507_, v_sz_1506_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_bs_1508_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; lean_object* v_v_1513_; lean_object* v___x_1514_; lean_object* v_bs_x27_1515_; lean_object* v_a_1517_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1512_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0);
v_v_1513_ = lean_array_uget(v_bs_1508_, v_i_1507_);
v___x_1514_ = lean_unsigned_to_nat(0u);
v_bs_x27_1515_ = lean_array_uset(v_bs_1508_, v_i_1507_, v___x_1514_);
v___x_1522_ = lean_usize_to_nat(v_i_1507_);
v___x_1523_ = lean_array_get_borrowed(v___x_1512_, v_a_1504_, v___x_1522_);
v___x_1524_ = lean_array_get_borrowed(v___x_1512_, v_funcMaps_1505_, v___x_1522_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_array_get_size(v___x_1523_);
v___x_1526_ = lean_array_get_size(v___x_1524_);
v___x_1527_ = lean_nat_dec_eq(v___x_1525_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec_ref(v_bs_x27_1515_);
lean_dec(v_v_1513_);
v___x_1528_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2));
lean_inc(v_v_1513_);
v___x_1531_ = l_Lean_Json_getObjVal_x3f(v_v_1513_, v___x_1530_);
v___x_1532_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1531_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc_n(v_a_1533_, 2);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__3));
v___x_1535_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_a_1533_, v___x_1534_);
v___x_1536_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1535_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__4));
lean_inc(v_v_1513_);
v___x_1539_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(v_v_1513_, v___x_1538_);
v___x_1540_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1539_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; size_t v_sz_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
lean_inc(v___x_1523_);
v___x_1542_ = l_Array_toSubarray___redArg(v___x_1523_, v___x_1514_, v___x_1525_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_a_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_a_1537_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v_sz_1545_ = lean_array_size(v___x_1524_);
v___x_1546_ = ((size_t)0ULL);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(v___x_1524_, v_sz_1545_, v___x_1546_, v___x_1544_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v_snd_1549_; lean_object* v_fst_1550_; lean_object* v_fst_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v_snd_1549_ = lean_ctor_get(v_a_1548_, 1);
lean_inc(v_snd_1549_);
v_fst_1550_ = lean_ctor_get(v_a_1548_, 0);
lean_inc(v_fst_1550_);
lean_dec(v_a_1548_);
v_fst_1551_ = lean_ctor_get(v_snd_1549_, 0);
lean_inc(v_fst_1551_);
lean_dec(v_snd_1549_);
v___x_1552_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(v_fst_1550_);
v___x_1553_ = l_Lean_Json_setObjVal_x21(v_a_1533_, v___x_1534_, v___x_1552_);
v___x_1554_ = l_Lean_Json_setObjVal_x21(v_v_1513_, v___x_1530_, v___x_1553_);
v___x_1555_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(v_fst_1551_);
v___x_1556_ = l_Lean_Json_setObjVal_x21(v___x_1554_, v___x_1538_, v___x_1555_);
v_a_1517_ = v___x_1556_;
goto v___jp_1516_;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_a_1533_);
lean_dec_ref(v_bs_x27_1515_);
lean_dec(v_v_1513_);
v_a_1557_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1547_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1547_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_a_1537_);
lean_dec(v_a_1533_);
lean_dec_ref(v_bs_x27_1515_);
lean_dec(v_v_1513_);
v_a_1565_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1540_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1540_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v_a_1533_);
lean_dec_ref(v_bs_x27_1515_);
lean_dec(v_v_1513_);
v_a_1573_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1536_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1536_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_dec(v_v_1513_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1581_; 
v_a_1581_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1532_, 1);
v_a_1517_ = v_a_1581_;
goto v___jp_1516_;
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v_bs_x27_1515_);
v_a_1582_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1532_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1532_);
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
}
v___jp_1516_:
{
size_t v___x_1518_; size_t v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_add(v_i_1507_, v___x_1518_);
v___x_1520_ = lean_array_uset(v_bs_x27_1515_, v_i_1507_, v_a_1517_);
v_i_1507_ = v___x_1519_;
v_bs_1508_ = v___x_1520_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___boxed(lean_object* v_a_1590_, lean_object* v_funcMaps_1591_, lean_object* v_sz_1592_, lean_object* v_i_1593_, lean_object* v_bs_1594_, lean_object* v___y_1595_){
_start:
{
size_t v_sz_boxed_1596_; size_t v_i_boxed_1597_; lean_object* v_res_1598_; 
v_sz_boxed_1596_ = lean_unbox_usize(v_sz_1592_);
lean_dec(v_sz_1592_);
v_i_boxed_1597_ = lean_unbox_usize(v_i_1593_);
lean_dec(v_i_1593_);
v_res_1598_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1590_, v_funcMaps_1591_, v_sz_boxed_1596_, v_i_boxed_1597_, v_bs_1594_);
lean_dec_ref(v_funcMaps_1591_);
lean_dec_ref(v_a_1590_);
return v_res_1598_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__1));
v___x_1602_ = lean_mk_io_user_error(v___x_1601_);
return v___x_1602_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__3));
v___x_1605_ = lean_mk_io_user_error(v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(lean_object* v_profile_1608_, lean_object* v_response_1609_, lean_object* v_funcMaps_1610_){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__0));
v___x_1613_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_response_1609_, v___x_1612_);
v___x_1614_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1613_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1694_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1694_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1694_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1619_ = lean_unsigned_to_nat(0u);
v___x_1620_ = lean_array_get_size(v_a_1615_);
v___x_1621_ = lean_nat_dec_lt(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1624_; 
lean_dec(v_a_1615_);
lean_dec(v_profile_1608_);
v___x_1622_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2, &l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2);
if (v_isShared_1618_ == 0)
{
lean_ctor_set_tag(v___x_1617_, 1);
lean_ctor_set(v___x_1617_, 0, v___x_1622_);
v___x_1624_ = v___x_1617_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_del_object(v___x_1617_);
v___x_1626_ = lean_array_fget(v_a_1615_, v___x_1619_);
lean_dec(v_a_1615_);
v___x_1627_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4));
v___x_1628_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(v___x_1626_, v___x_1627_);
v___x_1629_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1628_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1));
lean_inc(v_profile_1608_);
v___x_1632_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1608_, v___x_1631_);
v___x_1633_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1632_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1677_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1677_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1677_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1643_ = lean_array_get_size(v_a_1630_);
v___x_1644_ = lean_array_get_size(v_a_1634_);
v___x_1645_ = lean_nat_dec_eq(v___x_1643_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_dec(v_a_1634_);
lean_dec(v_a_1630_);
lean_dec(v_profile_1608_);
goto v___jp_1638_;
}
else
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = lean_array_get_size(v_funcMaps_1610_);
v___x_1647_ = lean_nat_dec_eq(v___x_1646_, v___x_1644_);
if (v___x_1647_ == 0)
{
lean_dec(v_a_1634_);
lean_dec(v_a_1630_);
lean_dec(v_profile_1608_);
goto v___jp_1638_;
}
else
{
size_t v_sz_1648_; size_t v___x_1649_; lean_object* v___x_1650_; 
lean_del_object(v___x_1636_);
v_sz_1648_ = lean_array_size(v_a_1634_);
v___x_1649_ = ((size_t)0ULL);
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1630_, v_funcMaps_1610_, v_sz_1648_, v___x_1649_, v_a_1634_);
lean_dec(v_a_1630_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__5));
lean_inc(v_profile_1608_);
v___x_1653_ = l_Lean_Json_getObjVal_x3f(v_profile_1608_, v___x_1652_);
v___x_1654_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1653_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1668_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1668_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1668_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1666_; 
v___x_1659_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_a_1651_);
v___x_1660_ = l_Lean_Json_setObjVal_x21(v_profile_1608_, v___x_1631_, v___x_1659_);
v___x_1661_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__6));
v___x_1662_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1662_, 0, v___x_1647_);
v___x_1663_ = l_Lean_Json_setObjVal_x21(v_a_1655_, v___x_1661_, v___x_1662_);
v___x_1664_ = l_Lean_Json_setObjVal_x21(v___x_1660_, v___x_1652_, v___x_1663_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1664_);
v___x_1666_ = v___x_1657_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
else
{
lean_dec(v_a_1651_);
lean_dec(v_profile_1608_);
return v___x_1654_;
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v_profile_1608_);
v_a_1669_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1650_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1650_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
v___jp_1638_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4, &l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4);
if (v_isShared_1637_ == 0)
{
lean_ctor_set_tag(v___x_1636_, 1);
lean_ctor_set(v___x_1636_, 0, v___x_1639_);
v___x_1641_ = v___x_1636_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_a_1630_);
lean_dec(v_profile_1608_);
v_a_1678_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1633_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1633_);
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
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec(v_profile_1608_);
v_a_1686_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1629_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1629_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v_profile_1608_);
v_a_1695_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1614_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1614_);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___boxed(lean_object* v_profile_1703_, lean_object* v_response_1704_, lean_object* v_funcMaps_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(v_profile_1703_, v_response_1704_, v_funcMaps_1705_);
lean_dec_ref(v_funcMaps_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(lean_object* v_a_1708_, lean_object* v_funcMaps_1709_, lean_object* v_as_1710_, size_t v_sz_1711_, size_t v_i_1712_, lean_object* v_bs_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1708_, v_funcMaps_1709_, v_sz_1711_, v_i_1712_, v_bs_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___boxed(lean_object* v_a_1716_, lean_object* v_funcMaps_1717_, lean_object* v_as_1718_, lean_object* v_sz_1719_, lean_object* v_i_1720_, lean_object* v_bs_1721_, lean_object* v___y_1722_){
_start:
{
size_t v_sz_boxed_1723_; size_t v_i_boxed_1724_; lean_object* v_res_1725_; 
v_sz_boxed_1723_ = lean_unbox_usize(v_sz_1719_);
lean_dec(v_sz_1719_);
v_i_boxed_1724_ = lean_unbox_usize(v_i_1720_);
lean_dec(v_i_1720_);
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(v_a_1716_, v_funcMaps_1717_, v_as_1718_, v_sz_boxed_1723_, v_i_boxed_1724_, v_bs_1721_);
lean_dec_ref(v_as_1718_);
lean_dec_ref(v_funcMaps_1717_);
lean_dec_ref(v_a_1716_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(lean_object* v_cfg_1726_, lean_object* v_proc_1727_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_io_process_child_kill(v_cfg_1726_, v_proc_1727_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; 
lean_dec_ref_known(v___x_1732_, 1);
v___x_1733_ = lean_io_process_child_wait(v_cfg_1726_, v_proc_1727_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1741_; 
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v___x_1733_, 0);
lean_dec(v_unused_1742_);
v___x_1735_ = v___x_1733_;
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
else
{
lean_dec(v___x_1733_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1737_ = lean_box(0);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1737_);
v___x_1739_ = v___x_1735_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
else
{
lean_dec_ref_known(v___x_1733_, 1);
goto v___jp_1729_;
}
}
else
{
if (lean_obj_tag(v___x_1732_) == 0)
{
return v___x_1732_;
}
else
{
lean_dec_ref_known(v___x_1732_, 1);
goto v___jp_1729_;
}
}
v___jp_1729_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe___boxed(lean_object* v_cfg_1743_, lean_object* v_proc_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v_cfg_1743_, v_proc_1744_);
lean_dec_ref(v_proc_1744_);
lean_dec_ref(v_cfg_1743_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(lean_object* v_as_1748_, lean_object* v_j_1749_){
_start:
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = lean_array_get_size(v_as_1748_);
v___x_1751_ = lean_nat_dec_lt(v_j_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
lean_dec(v_j_1749_);
v___x_1752_ = lean_box(0);
return v___x_1752_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1753_ = lean_array_fget_borrowed(v_as_1748_, v_j_1749_);
v___x_1754_ = ((lean_object*)(l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0));
v___x_1755_ = lean_string_dec_eq(v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = lean_unsigned_to_nat(1u);
v___x_1757_ = lean_nat_add(v_j_1749_, v___x_1756_);
lean_dec(v_j_1749_);
v_j_1749_ = v___x_1757_;
goto _start;
}
else
{
lean_object* v___x_1759_; 
v___x_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1759_, 0, v_j_1749_);
return v___x_1759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___boxed(lean_object* v_as_1760_, lean_object* v_j_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(v_as_1760_, v_j_1761_);
lean_dec_ref(v_as_1760_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash(lean_object* v_args_1765_){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_unsigned_to_nat(0u);
v___x_1767_ = l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(v_args_1765_, v___x_1766_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash___closed__0));
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v_args_1765_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
return v___x_1769_;
}
else
{
lean_object* v_val_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_val_1770_ = lean_ctor_get(v___x_1767_, 0);
lean_inc_n(v_val_1770_, 2);
lean_dec_ref_known(v___x_1767_, 1);
v___x_1771_ = l_Array_extract___redArg(v_args_1765_, v___x_1766_, v_val_1770_);
v___x_1772_ = lean_unsigned_to_nat(1u);
v___x_1773_ = lean_nat_add(v_val_1770_, v___x_1772_);
lean_dec(v_val_1770_);
v___x_1774_ = lean_array_get_size(v_args_1765_);
v___x_1775_ = l_Array_extract___redArg(v_args_1765_, v___x_1773_, v___x_1774_);
lean_dec_ref(v_args_1765_);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1771_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
return v___x_1776_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(lean_object* v_f_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_io_create_tempdir();
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v_r_1781_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc_n(v_a_1780_, 2);
lean_dec_ref_known(v___x_1779_, 1);
v_r_1781_ = lean_apply_2(v_f_1777_, v_a_1780_, lean_box(0));
if (lean_obj_tag(v_r_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1783_; 
v_a_1782_ = lean_ctor_get(v_r_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v_r_1781_, 1);
v___x_1783_ = l_IO_FS_removeDirAll(v_a_1780_);
lean_dec(v_a_1780_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v___x_1783_, 0);
lean_dec(v_unused_1791_);
v___x_1785_ = v___x_1783_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_dec(v___x_1783_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v_a_1782_);
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1782_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_a_1782_);
v_a_1792_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1783_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1783_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1801_; 
v_a_1800_ = lean_ctor_get(v_r_1781_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v_r_1781_, 1);
v___x_1801_ = l_IO_FS_removeDirAll(v_a_1780_);
lean_dec(v_a_1780_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v___x_1801_, 0);
lean_dec(v_unused_1809_);
v___x_1803_ = v___x_1801_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_dec(v___x_1801_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 1);
lean_ctor_set(v___x_1803_, 0, v_a_1800_);
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1800_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec(v_a_1800_);
v_a_1810_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1801_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1801_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec_ref(v_f_1777_);
v_a_1818_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1779_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1779_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg___boxed(lean_object* v_f_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v_f_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(lean_object* v_00_u03b1_1829_, lean_object* v_f_1830_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v_f_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___boxed(lean_object* v_00_u03b1_1833_, lean_object* v_f_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(v_00_u03b1_1833_, v_f_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__0(lean_object* v___y_1837_, lean_object* v_____r_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___y_1837_);
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__0___boxed(lean_object* v___y_1842_, lean_object* v_____r_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lake_Samply_run___lam__0(v___y_1842_, v_____r_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(lean_object* v_s_1846_){
_start:
{
lean_object* v___x_1848_; lean_object* v_putStr_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_get_stderr();
v_putStr_1849_ = lean_ctor_get(v___x_1848_, 4);
lean_inc_ref(v_putStr_1849_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = lean_apply_2(v_putStr_1849_, v_s_1846_, lean_box(0));
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0___boxed(lean_object* v_s_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(v_s_1851_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0(lean_object* v_s_1854_){
_start:
{
uint32_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = 10;
v___x_1857_ = lean_string_push(v_s_1854_, v___x_1856_);
v___x_1858_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0___boxed(lean_object* v_s_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v_s_1859_);
return v_res_1861_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1867_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__2));
v___x_1868_ = lean_unsigned_to_nat(4u);
v___x_1869_ = lean_mk_empty_array_with_capacity(v___x_1868_);
v___x_1870_ = lean_array_push(v___x_1869_, v___x_1867_);
return v___x_1870_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__3));
v___x_1872_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__5, &l_Lake_Samply_run___lam__1___closed__5_once, _init_l_Lake_Samply_run___lam__1___closed__5);
v___x_1873_ = lean_array_push(v___x_1872_, v___x_1871_);
return v___x_1873_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__4));
v___x_1875_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__6, &l_Lake_Samply_run___lam__1___closed__6_once, _init_l_Lake_Samply_run___lam__1___closed__6);
v___x_1876_ = lean_array_push(v___x_1875_, v___x_1874_);
return v___x_1876_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1877_ = ((lean_object*)(l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0));
v___x_1878_ = lean_unsigned_to_nat(2u);
v___x_1879_ = lean_mk_empty_array_with_capacity(v___x_1878_);
v___x_1880_ = lean_array_push(v___x_1879_, v___x_1877_);
return v___x_1880_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__20(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1893_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__19));
v___x_1894_ = lean_unsigned_to_nat(2u);
v___x_1895_ = lean_mk_empty_array_with_capacity(v___x_1894_);
v___x_1896_ = lean_array_push(v___x_1895_, v___x_1893_);
return v___x_1896_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__31(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1907_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__22));
v___x_1908_ = lean_unsigned_to_nat(9u);
v___x_1909_ = lean_mk_empty_array_with_capacity(v___x_1908_);
v___x_1910_ = lean_array_push(v___x_1909_, v___x_1907_);
return v___x_1910_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__32(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__23));
v___x_1912_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__31, &l_Lake_Samply_run___lam__1___closed__31_once, _init_l_Lake_Samply_run___lam__1___closed__31);
v___x_1913_ = lean_array_push(v___x_1912_, v___x_1911_);
return v___x_1913_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__33(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__24));
v___x_1915_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__32, &l_Lake_Samply_run___lam__1___closed__32_once, _init_l_Lake_Samply_run___lam__1___closed__32);
v___x_1916_ = lean_array_push(v___x_1915_, v___x_1914_);
return v___x_1916_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__34(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__25));
v___x_1918_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__33, &l_Lake_Samply_run___lam__1___closed__33_once, _init_l_Lake_Samply_run___lam__1___closed__33);
v___x_1919_ = lean_array_push(v___x_1918_, v___x_1917_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__1(lean_object* v_passthrough_1932_, lean_object* v_binary_1933_, lean_object* v___x_1934_, lean_object* v_env_1935_, uint8_t v_raw_1936_, lean_object* v_port_1937_, lean_object* v___x_1938_, uint8_t v_serve_1939_, lean_object* v_outputPath_1940_, lean_object* v_tmpDir_1941_){
_start:
{
lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v_a_1946_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___y_1990_; 
v___x_1987_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__0));
lean_inc_ref(v_tmpDir_1941_);
v___x_1988_ = l_System_FilePath_join(v_tmpDir_1941_, v___x_1987_);
if (lean_obj_tag(v_outputPath_1940_) == 0)
{
if (v_raw_1936_ == 0)
{
lean_object* v___x_2246_; 
v___x_2246_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__45));
v___y_1990_ = v___x_2246_;
goto v___jp_1989_;
}
else
{
lean_object* v___x_2247_; 
v___x_2247_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__46));
v___y_1990_ = v___x_2247_;
goto v___jp_1989_;
}
}
else
{
lean_object* v_val_2248_; 
v_val_2248_ = lean_ctor_get(v_outputPath_1940_, 0);
lean_inc(v_val_2248_);
lean_dec_ref_known(v_outputPath_1940_, 1);
v___y_1990_ = v_val_2248_;
goto v___jp_1989_;
}
v___jp_1943_:
{
lean_object* v___x_1947_; 
v___x_1947_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v___y_1945_, v___y_1944_);
lean_dec_ref(v___y_1944_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v___x_1947_, 0);
lean_dec(v_unused_1955_);
v___x_1949_ = v___x_1947_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_dec(v___x_1947_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set_tag(v___x_1949_, 1);
lean_ctor_set(v___x_1949_, 0, v_a_1946_);
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1946_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v_a_1946_);
v_a_1956_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1947_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1947_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
v___jp_1964_:
{
lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___y_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___y_1967_);
v___x_1969_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v___y_1966_, v___y_1965_);
lean_dec_ref(v___y_1965_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1977_; 
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; 
v_unused_1978_ = lean_ctor_get(v___x_1969_, 0);
lean_dec(v_unused_1978_);
v___x_1971_ = v___x_1969_;
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
else
{
lean_dec(v___x_1969_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1977_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_a_1973_; lean_object* v___x_1975_; 
v_a_1973_ = lean_ctor_get(v_a_1968_, 0);
lean_inc(v_a_1973_);
lean_dec(v_a_1968_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v_a_1973_);
v___x_1975_ = v___x_1971_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v_a_1968_);
v_a_1979_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1969_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1969_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
v___jp_1989_:
{
lean_object* v___x_1991_; lean_object* v_fst_1992_; lean_object* v_snd_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1991_ = l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash(v_passthrough_1932_);
v_fst_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_fst_1992_);
v_snd_1993_ = lean_ctor_get(v___x_1991_, 1);
lean_inc(v_snd_1993_);
lean_dec_ref(v___x_1991_);
v___x_1994_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__1));
v___x_1995_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_1994_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec_ref_known(v___x_1995_, 1);
v___x_1996_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__0));
v___x_1997_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__7, &l_Lake_Samply_run___lam__1___closed__7_once, _init_l_Lake_Samply_run___lam__1___closed__7);
lean_inc_ref(v___x_1988_);
v___x_1998_ = lean_array_push(v___x_1997_, v___x_1988_);
v___x_1999_ = l_Array_append___redArg(v___x_1998_, v_fst_1992_);
lean_dec(v_fst_1992_);
v___x_2000_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__8, &l_Lake_Samply_run___lam__1___closed__8_once, _init_l_Lake_Samply_run___lam__1___closed__8);
v___x_2001_ = lean_array_push(v___x_2000_, v_binary_1933_);
v___x_2002_ = l_Array_append___redArg(v___x_1999_, v___x_2001_);
lean_dec_ref(v___x_2001_);
v___x_2003_ = l_Array_append___redArg(v___x_2002_, v_snd_1993_);
lean_dec(v_snd_1993_);
v___x_2004_ = lean_box(0);
v___x_2005_ = 1;
v___x_2006_ = 0;
v___x_2007_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2007_, 0, v___x_1996_);
lean_ctor_set(v___x_2007_, 1, v___x_1934_);
lean_ctor_set(v___x_2007_, 2, v___x_2003_);
lean_ctor_set(v___x_2007_, 3, v___x_2004_);
lean_ctor_set(v___x_2007_, 4, v_env_1935_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*5, v___x_2005_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*5 + 1, v___x_2006_);
v___x_2008_ = lean_io_process_spawn(v___x_2007_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v___x_2010_ = lean_io_process_child_wait(v___x_1996_, v_a_2009_);
lean_dec(v_a_2009_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2221_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2221_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2221_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
uint32_t v___x_2015_; uint32_t v___x_2016_; uint8_t v___x_2017_; 
v___x_2015_ = 0;
v___x_2016_ = lean_unbox_uint32(v_a_2011_);
v___x_2017_ = lean_uint32_dec_eq(v___x_2016_, v___x_2015_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; uint32_t v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
lean_dec(v_port_1937_);
v___x_2018_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__9));
v___x_2019_ = lean_unbox_uint32(v_a_2011_);
lean_dec(v_a_2011_);
v___x_2020_ = lean_uint32_to_nat(v___x_2019_);
v___x_2021_ = l_Nat_reprFast(v___x_2020_);
v___x_2022_ = lean_string_append(v___x_2018_, v___x_2021_);
lean_dec_ref(v___x_2021_);
v___x_2023_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__10));
v___x_2024_ = lean_string_append(v___x_2022_, v___x_2023_);
v___x_2025_ = lean_mk_io_user_error(v___x_2024_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 1);
lean_ctor_set(v___x_2013_, 0, v___x_2025_);
v___x_2027_ = v___x_2013_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
else
{
lean_del_object(v___x_2013_);
lean_dec(v_a_2011_);
if (v_raw_1936_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__11));
v___x_2030_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2029_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec_ref_known(v___x_2030_, 1);
v___x_2031_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__12));
lean_inc_ref(v_tmpDir_1941_);
v___x_2032_ = l_System_FilePath_join(v_tmpDir_1941_, v___x_2031_);
v___x_2033_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__0));
v___x_2034_ = l_IO_FS_writeFile(v___x_2032_, v___x_2033_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_dec_ref_known(v___x_2034_, 1);
v___x_2035_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__13));
v___x_2036_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__1));
v___x_2037_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__14));
lean_inc(v_port_1937_);
v___x_2038_ = l_Nat_reprFast(v_port_1937_);
v___x_2039_ = lean_string_append(v___x_2037_, v___x_2038_);
v___x_2040_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__15));
v___x_2041_ = lean_string_append(v___x_2039_, v___x_2040_);
lean_inc_ref(v___x_1988_);
v___x_2042_ = l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(v___x_1988_);
v___x_2043_ = lean_string_append(v___x_2041_, v___x_2042_);
lean_dec_ref(v___x_2042_);
v___x_2044_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__16));
v___x_2045_ = lean_string_append(v___x_2043_, v___x_2044_);
lean_inc_ref(v___x_2032_);
v___x_2046_ = l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(v___x_2032_);
v___x_2047_ = lean_string_append(v___x_2045_, v___x_2046_);
lean_dec_ref(v___x_2046_);
v___x_2048_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__17));
v___x_2049_ = lean_string_append(v___x_2047_, v___x_2048_);
v___x_2050_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4, &l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4);
v___x_2051_ = lean_array_push(v___x_2050_, v___x_2049_);
v___x_2052_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__5));
v___x_2053_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2053_, 0, v___x_2035_);
lean_ctor_set(v___x_2053_, 1, v___x_2036_);
lean_ctor_set(v___x_2053_, 2, v___x_2051_);
lean_ctor_set(v___x_2053_, 3, v___x_2004_);
lean_ctor_set(v___x_2053_, 4, v___x_2052_);
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*5, v___x_2005_);
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*5 + 1, v___x_2006_);
v___x_2054_ = lean_io_process_spawn(v___x_2053_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v___x_2056_ = lean_unsigned_to_nat(30000u);
v___x_2057_ = l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(v___x_2035_, v___x_2032_, v_a_2055_, v_port_1937_, v___x_2056_);
lean_dec_ref(v___x_2032_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2059_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__0));
v___x_2060_ = lean_string_append(v___x_2059_, v___x_2038_);
lean_dec_ref(v___x_2038_);
v___x_2061_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__1));
v___x_2062_ = lean_string_append(v___x_2060_, v___x_2061_);
v___x_2063_ = lean_string_append(v___x_2062_, v_a_2058_);
lean_dec(v_a_2058_);
v___x_2064_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__18));
v___x_2065_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2064_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec_ref_known(v___x_2065_, 1);
v___x_2066_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__20, &l_Lake_Samply_run___lam__1___closed__20_once, _init_l_Lake_Samply_run___lam__1___closed__20);
lean_inc_ref(v___x_1988_);
v___x_2067_ = lean_array_push(v___x_2066_, v___x_1988_);
lean_inc_ref(v___x_1938_);
v___x_2068_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2068_, 0, v___x_1996_);
lean_ctor_set(v___x_2068_, 1, v___x_1938_);
lean_ctor_set(v___x_2068_, 2, v___x_2067_);
lean_ctor_set(v___x_2068_, 3, v___x_2004_);
lean_ctor_set(v___x_2068_, 4, v___x_2052_);
lean_ctor_set_uint8(v___x_2068_, sizeof(void*)*5, v___x_2005_);
lean_ctor_set_uint8(v___x_2068_, sizeof(void*)*5 + 1, v___x_2006_);
v___x_2069_ = l_IO_Process_run(v___x_2068_, v___x_2004_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2071_ = l_Lean_Json_parse(v_a_2070_);
v___x_2072_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_2071_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2074_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc_n(v_a_2073_, 2);
lean_dec_ref_known(v___x_2072_, 1);
v___x_2074_ = l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(v_a_2073_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2163_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2163_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2163_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_fst_2079_; lean_object* v_snd_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v_fst_2079_ = lean_ctor_get(v_a_2075_, 0);
lean_inc(v_fst_2079_);
v_snd_2080_ = lean_ctor_get(v_a_2075_, 1);
lean_inc(v_snd_2080_);
lean_dec(v_a_2075_);
v___x_2081_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__21));
v___x_2082_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__26));
lean_inc_ref(v___x_2063_);
v___x_2083_ = lean_string_append(v___x_2063_, v___x_2082_);
v___x_2084_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__27));
v___x_2085_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__28));
v___x_2086_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__29));
v___x_2087_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__30));
v___x_2088_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__34, &l_Lake_Samply_run___lam__1___closed__34_once, _init_l_Lake_Samply_run___lam__1___closed__34);
v___x_2089_ = lean_array_push(v___x_2088_, v___x_2083_);
v___x_2090_ = lean_array_push(v___x_2089_, v___x_2084_);
v___x_2091_ = lean_array_push(v___x_2090_, v___x_2085_);
v___x_2092_ = lean_array_push(v___x_2091_, v___x_2086_);
v___x_2093_ = lean_array_push(v___x_2092_, v___x_2087_);
v___x_2094_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2094_, 0, v___x_1996_);
lean_ctor_set(v___x_2094_, 1, v___x_2081_);
lean_ctor_set(v___x_2094_, 2, v___x_2093_);
lean_ctor_set(v___x_2094_, 3, v___x_2004_);
lean_ctor_set(v___x_2094_, 4, v___x_2052_);
lean_ctor_set_uint8(v___x_2094_, sizeof(void*)*5, v___x_2005_);
lean_ctor_set_uint8(v___x_2094_, sizeof(void*)*5 + 1, v___x_2006_);
v___x_2095_ = l_Lean_Json_compress(v_fst_2079_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set_tag(v___x_2077_, 1);
lean_ctor_set(v___x_2077_, 0, v___x_2095_);
v___x_2097_ = v___x_2077_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_IO_Process_run(v___x_2094_, v___x_2097_);
lean_dec_ref(v___x_2097_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v___x_2100_ = l_Lean_Json_parse(v_a_2099_);
v___x_2101_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_2100_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(v_a_2073_, v_a_2102_, v_snd_2080_);
lean_dec(v_snd_2080_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
v___x_2105_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__35));
lean_inc_ref(v_tmpDir_1941_);
v___x_2106_ = l_System_FilePath_join(v_tmpDir_1941_, v___x_2105_);
v___x_2107_ = l_Lean_Json_compress(v_a_2104_);
v___x_2108_ = l_IO_FS_writeFile(v___x_2106_, v___x_2107_);
lean_dec_ref(v___x_2107_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec_ref_known(v___x_2108_, 1);
v___x_2109_ = lean_unsigned_to_nat(1u);
v___x_2110_ = lean_mk_empty_array_with_capacity(v___x_2109_);
v___x_2111_ = lean_array_push(v___x_2110_, v___x_2106_);
v___x_2112_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2112_, 0, v___x_1996_);
lean_ctor_set(v___x_2112_, 1, v___x_1938_);
lean_ctor_set(v___x_2112_, 2, v___x_2111_);
lean_ctor_set(v___x_2112_, 3, v___x_2004_);
lean_ctor_set(v___x_2112_, 4, v___x_2052_);
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*5, v___x_2005_);
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*5 + 1, v___x_2006_);
v___x_2113_ = l_IO_Process_run(v___x_2112_, v___x_2004_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref_known(v___x_2113_, 1);
v___x_2114_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__36));
v___x_2115_ = l_System_FilePath_join(v_tmpDir_1941_, v___x_2114_);
v___x_2116_ = lean_io_rename(v___x_2115_, v___x_1988_);
lean_dec_ref(v___x_2115_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; 
lean_dec_ref_known(v___x_2116_, 1);
v___x_2117_ = l_Lake_copyFile(v___x_1988_, v___y_1990_);
lean_dec_ref(v___x_1988_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_dec_ref_known(v___x_2117_, 1);
v___x_2118_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__37));
v___x_2119_ = lean_string_append(v___x_2118_, v___y_1990_);
v___x_2120_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2119_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_dec_ref_known(v___x_2120_, 1);
if (v_serve_1939_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec_ref(v___x_2063_);
v___x_2121_ = lean_box(0);
v___x_2122_ = l_Lake_Samply_run___lam__0(v___y_1990_, v___x_2121_);
v___y_1965_ = v_a_2055_;
v___y_1966_ = v___x_2035_;
v___y_1967_ = v___x_2122_;
goto v___jp_1964_;
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2123_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__38));
v___x_2124_ = lean_string_append(v___x_2123_, v___x_2063_);
v___x_2125_ = lean_string_append(v___x_2124_, v___x_2061_);
v___x_2126_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2125_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec_ref_known(v___x_2126_, 1);
v___x_2127_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__39));
v___x_2128_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2127_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_dec_ref_known(v___x_2128_, 1);
v___x_2129_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__40));
v___x_2130_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__41));
v___x_2131_ = lean_string_append(v___x_2063_, v___x_2130_);
v___x_2132_ = l_Lake_uriEncode(v___x_2131_, v___x_2033_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = lean_string_append(v___x_2129_, v___x_2132_);
lean_dec_ref(v___x_2132_);
v___x_2134_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2133_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec_ref_known(v___x_2134_, 1);
v___x_2135_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__42));
v___x_2136_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2135_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v___x_2137_; 
lean_dec_ref_known(v___x_2136_, 1);
v___x_2137_ = lean_io_process_child_wait(v___x_2035_, v_a_2055_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; uint32_t v___x_2139_; uint8_t v___x_2140_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = lean_unbox_uint32(v_a_2138_);
v___x_2140_ = lean_uint32_dec_eq(v___x_2139_, v___x_2015_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; uint32_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_dec_ref(v___y_1990_);
v___x_2141_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__43));
v___x_2142_ = lean_unbox_uint32(v_a_2138_);
lean_dec(v_a_2138_);
v___x_2143_ = lean_uint32_to_nat(v___x_2142_);
v___x_2144_ = l_Nat_reprFast(v___x_2143_);
v___x_2145_ = lean_string_append(v___x_2141_, v___x_2144_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = lean_mk_io_user_error(v___x_2145_);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v___x_2146_;
goto v___jp_1943_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec(v_a_2138_);
v___x_2147_ = lean_box(0);
v___x_2148_ = l_Lake_Samply_run___lam__0(v___y_1990_, v___x_2147_);
v___y_1965_ = v_a_2055_;
v___y_1966_ = v___x_2035_;
v___y_1967_ = v___x_2148_;
goto v___jp_1964_;
}
}
else
{
lean_object* v_a_2149_; 
lean_dec_ref(v___y_1990_);
v_a_2149_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2137_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2149_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2150_; 
lean_dec_ref(v___y_1990_);
v_a_2150_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2136_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2150_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2151_; 
lean_dec_ref(v___y_1990_);
v_a_2151_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2134_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2151_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2152_; 
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
v_a_2152_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2128_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2152_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2153_; 
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
v_a_2153_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2126_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2153_;
goto v___jp_1943_;
}
}
}
else
{
lean_object* v_a_2154_; 
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
v_a_2154_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2120_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2154_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2155_; 
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
v_a_2155_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2117_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2155_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2156_; 
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
v_a_2156_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2116_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2156_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2157_; 
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
v_a_2157_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2113_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2157_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2158_; 
lean_dec_ref(v___x_2106_);
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
v_a_2158_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2108_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2158_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2159_; 
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
v_a_2159_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2103_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2159_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2160_; 
lean_dec(v_snd_2080_);
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
v_a_2160_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2101_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2160_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2161_; 
lean_dec(v_snd_2080_);
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
v_a_2161_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2098_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2161_;
goto v___jp_1943_;
}
}
}
}
else
{
lean_object* v_a_2164_; 
lean_dec(v_a_2073_);
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
v_a_2164_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2074_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2164_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2165_; 
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
v_a_2165_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2072_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2165_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2166_; 
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
v_a_2166_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2069_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2166_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2167_; 
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
v_a_2167_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2065_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2167_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2168_; 
lean_dec_ref(v___x_2038_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
v_a_2168_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2057_, 1);
v___y_1944_ = v_a_2055_;
v___y_1945_ = v___x_2035_;
v_a_1946_ = v_a_2168_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec_ref(v___x_2038_);
lean_dec_ref(v___x_2032_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
lean_dec(v_port_1937_);
v_a_2169_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2054_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2054_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec_ref(v___x_2032_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
lean_dec(v_port_1937_);
v_a_2177_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2034_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2034_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
lean_dec(v_port_1937_);
v_a_2185_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2030_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2030_);
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
lean_object* v___x_2193_; 
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
lean_dec(v_port_1937_);
v___x_2193_ = l_Lake_copyFile(v___x_1988_, v___y_1990_);
lean_dec_ref(v___x_1988_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_dec_ref_known(v___x_2193_, 1);
v___x_2194_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__44));
v___x_2195_ = lean_string_append(v___x_2194_, v___y_1990_);
v___x_2196_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2195_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; 
v_unused_2204_ = lean_ctor_get(v___x_2196_, 0);
lean_dec(v_unused_2204_);
v___x_2198_ = v___x_2196_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_dec(v___x_2196_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___y_1990_);
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___y_1990_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec_ref(v___y_1990_);
v_a_2205_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2196_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2196_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref(v___y_1990_);
v_a_2213_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2193_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2193_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
lean_dec(v_port_1937_);
v_a_2222_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2010_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2010_);
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
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
lean_dec(v_port_1937_);
v_a_2230_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2008_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2008_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v_snd_1993_);
lean_dec(v_fst_1992_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___x_1988_);
lean_dec_ref(v_tmpDir_1941_);
lean_dec_ref(v___x_1938_);
lean_dec(v_port_1937_);
lean_dec_ref(v_env_1935_);
lean_dec_ref(v___x_1934_);
lean_dec_ref(v_binary_1933_);
v_a_2238_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_1995_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_1995_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__1___boxed(lean_object* v_passthrough_2249_, lean_object* v_binary_2250_, lean_object* v___x_2251_, lean_object* v_env_2252_, lean_object* v_raw_2253_, lean_object* v_port_2254_, lean_object* v___x_2255_, lean_object* v_serve_2256_, lean_object* v_outputPath_2257_, lean_object* v_tmpDir_2258_, lean_object* v___y_2259_){
_start:
{
uint8_t v_raw_boxed_2260_; uint8_t v_serve_boxed_2261_; lean_object* v_res_2262_; 
v_raw_boxed_2260_ = lean_unbox(v_raw_2253_);
v_serve_boxed_2261_ = lean_unbox(v_serve_2256_);
v_res_2262_ = l_Lake_Samply_run___lam__1(v_passthrough_2249_, v_binary_2250_, v___x_2251_, v_env_2252_, v_raw_boxed_2260_, v_port_2254_, v___x_2255_, v_serve_boxed_2261_, v_outputPath_2257_, v_tmpDir_2258_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run(lean_object* v_binary_2268_, lean_object* v_passthrough_2269_, lean_object* v_outputPath_2270_, lean_object* v_port_2271_, uint8_t v_raw_2272_, uint8_t v_serve_2273_, lean_object* v_env_2274_){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = ((lean_object*)(l_Lake_Samply_run___closed__0));
v___x_2277_ = ((lean_object*)(l_Lake_Samply_run___closed__1));
v___x_2278_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2276_, v___x_2277_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___f_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
lean_dec_ref_known(v___x_2278_, 1);
v___x_2279_ = ((lean_object*)(l_Lake_Samply_run___closed__2));
v___x_2280_ = lean_box(v_raw_2272_);
v___x_2281_ = lean_box(v_serve_2273_);
v___f_2282_ = lean_alloc_closure((void*)(l_Lake_Samply_run___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2282_, 0, v_passthrough_2269_);
lean_closure_set(v___f_2282_, 1, v_binary_2268_);
lean_closure_set(v___f_2282_, 2, v___x_2276_);
lean_closure_set(v___f_2282_, 3, v_env_2274_);
lean_closure_set(v___f_2282_, 4, v___x_2280_);
lean_closure_set(v___f_2282_, 5, v_port_2271_);
lean_closure_set(v___f_2282_, 6, v___x_2279_);
lean_closure_set(v___f_2282_, 7, v___x_2281_);
lean_closure_set(v___f_2282_, 8, v_outputPath_2270_);
v___x_2283_ = ((lean_object*)(l_Lake_Samply_run___closed__3));
v___x_2284_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2279_, v___x_2283_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_dec_ref_known(v___x_2284_, 1);
if (v_raw_2272_ == 0)
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__21));
v___x_2286_ = ((lean_object*)(l_Lake_Samply_run___closed__4));
v___x_2287_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2285_, v___x_2286_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v___x_2288_; 
lean_dec_ref_known(v___x_2287_, 1);
v___x_2288_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v___f_2282_);
return v___x_2288_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec_ref(v___f_2282_);
v_a_2289_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2287_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2287_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v___x_2297_; 
v___x_2297_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v___f_2282_);
return v___x_2297_;
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v___f_2282_);
v_a_2298_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2284_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2284_);
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
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v_env_2274_);
lean_dec(v_port_2271_);
lean_dec(v_outputPath_2270_);
lean_dec_ref(v_passthrough_2269_);
lean_dec_ref(v_binary_2268_);
v_a_2306_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2278_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2278_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___boxed(lean_object* v_binary_2314_, lean_object* v_passthrough_2315_, lean_object* v_outputPath_2316_, lean_object* v_port_2317_, lean_object* v_raw_2318_, lean_object* v_serve_2319_, lean_object* v_env_2320_, lean_object* v_a_2321_){
_start:
{
uint8_t v_raw_boxed_2322_; uint8_t v_serve_boxed_2323_; lean_object* v_res_2324_; 
v_raw_boxed_2322_ = lean_unbox(v_raw_2318_);
v_serve_boxed_2323_ = lean_unbox(v_serve_2319_);
v_res_2324_ = l_Lake_Samply_run(v_binary_2314_, v_passthrough_2315_, v_outputPath_2316_, v_port_2317_, v_raw_boxed_2322_, v_serve_boxed_2323_, v_env_2320_);
return v_res_2324_;
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
