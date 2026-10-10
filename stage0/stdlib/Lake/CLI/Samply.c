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
lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(lean_object* v_cmd_14_, lean_object* v_installHint_15_){
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
LEAN_EXPORT void l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmd_14_ = stack[0].m_obj;
lean_object* v_installHint_15_ = stack[1].m_obj;
lean_object* v_res_58_;
v_res_58_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v_cmd_14_, v_installHint_15_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___boxed(lean_object* v_cmd_59_, lean_object* v_installHint_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v_cmd_59_, v_installHint_60_);
lean_dec_ref(v_installHint_60_);
lean_dec_ref(v_cmd_59_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(lean_object* v_s_63_, lean_object* v_replacement_64_, lean_object* v_a_65_, lean_object* v_b_66_){
_start:
{
lean_object* v_it_68_; lean_object* v_startPos_69_; lean_object* v_endPos_70_; lean_object* v_it_79_; 
switch(lean_obj_tag(v_a_65_))
{
case 0:
{
lean_object* v_pos_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_97_; 
v_pos_85_ = lean_ctor_get(v_a_65_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_a_65_);
if (v_isSharedCheck_97_ == 0)
{
v___x_87_ = v_a_65_;
v_isShared_88_ = v_isSharedCheck_97_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_pos_85_);
lean_dec(v_a_65_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_97_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_startInclusive_89_; lean_object* v_endExclusive_90_; lean_object* v___x_91_; uint8_t v_decide_92_; 
v_startInclusive_89_ = lean_ctor_get(v_s_63_, 1);
v_endExclusive_90_ = lean_ctor_get(v_s_63_, 2);
v___x_91_ = lean_nat_sub(v_endExclusive_90_, v_startInclusive_89_);
v_decide_92_ = lean_nat_dec_eq(v_pos_85_, v___x_91_);
lean_dec(v___x_91_);
if (v_decide_92_ == 0)
{
lean_object* v___x_94_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 1);
v___x_94_ = v___x_87_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_pos_85_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
v_it_79_ = v___x_94_;
goto v___jp_78_;
}
}
else
{
lean_object* v___x_96_; 
lean_del_object(v___x_87_);
lean_dec(v_pos_85_);
v___x_96_ = lean_box(3);
v_it_79_ = v___x_96_;
goto v___jp_78_;
}
}
}
case 1:
{
lean_object* v_pos_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_110_; 
v_pos_98_ = lean_ctor_get(v_a_65_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v_a_65_);
if (v_isSharedCheck_110_ == 0)
{
v___x_100_ = v_a_65_;
v_isShared_101_ = v_isSharedCheck_110_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_pos_98_);
lean_dec(v_a_65_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_110_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v_str_102_; lean_object* v_startInclusive_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
v_str_102_ = lean_ctor_get(v_s_63_, 0);
v_startInclusive_103_ = lean_ctor_get(v_s_63_, 1);
v___x_104_ = lean_nat_add(v_startInclusive_103_, v_pos_98_);
v___x_105_ = lean_string_utf8_next_fast(v_str_102_, v___x_104_);
lean_dec(v___x_104_);
v___x_106_ = lean_nat_sub(v___x_105_, v_startInclusive_103_);
lean_inc(v___x_106_);
if (v_isShared_101_ == 0)
{
lean_ctor_set_tag(v___x_100_, 0);
lean_ctor_set(v___x_100_, 0, v___x_106_);
v___x_108_ = v___x_100_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
v_it_68_ = v___x_108_;
v_startPos_69_ = v_pos_98_;
v_endPos_70_ = v___x_106_;
goto v___jp_67_;
}
}
}
case 2:
{
lean_object* v_needle_111_; lean_object* v_table_112_; lean_object* v_stackPos_113_; lean_object* v_needlePos_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_175_; 
v_needle_111_ = lean_ctor_get(v_a_65_, 0);
v_table_112_ = lean_ctor_get(v_a_65_, 1);
v_stackPos_113_ = lean_ctor_get(v_a_65_, 2);
v_needlePos_114_ = lean_ctor_get(v_a_65_, 3);
v_isSharedCheck_175_ = !lean_is_exclusive(v_a_65_);
if (v_isSharedCheck_175_ == 0)
{
v___x_116_ = v_a_65_;
v_isShared_117_ = v_isSharedCheck_175_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_needlePos_114_);
lean_inc(v_stackPos_113_);
lean_inc(v_table_112_);
lean_inc(v_needle_111_);
lean_dec(v_a_65_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_175_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_str_118_; lean_object* v_startInclusive_119_; lean_object* v_endExclusive_120_; lean_object* v_str_121_; lean_object* v_startInclusive_122_; lean_object* v_endExclusive_123_; lean_object* v_basePos_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_str_118_ = lean_ctor_get(v_needle_111_, 0);
v_startInclusive_119_ = lean_ctor_get(v_needle_111_, 1);
v_endExclusive_120_ = lean_ctor_get(v_needle_111_, 2);
v_str_121_ = lean_ctor_get(v_s_63_, 0);
v_startInclusive_122_ = lean_ctor_get(v_s_63_, 1);
v_endExclusive_123_ = lean_ctor_get(v_s_63_, 2);
v_basePos_124_ = lean_nat_sub(v_stackPos_113_, v_needlePos_114_);
v___x_125_ = lean_nat_sub(v_endExclusive_120_, v_startInclusive_119_);
v___x_126_ = lean_nat_add(v_basePos_124_, v___x_125_);
v___x_127_ = lean_nat_sub(v_endExclusive_123_, v_startInclusive_122_);
v___x_128_ = lean_nat_dec_le(v___x_126_, v___x_127_);
lean_dec(v___x_126_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
lean_dec(v___x_125_);
lean_del_object(v___x_116_);
lean_dec(v_needlePos_114_);
lean_dec(v_stackPos_113_);
lean_dec_ref(v_table_112_);
lean_dec_ref(v_needle_111_);
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_nat_add(v_basePos_124_, v___x_129_);
v___x_131_ = lean_nat_dec_le(v___x_130_, v___x_127_);
lean_dec(v___x_130_);
if (v___x_131_ == 0)
{
lean_dec(v___x_127_);
lean_dec(v_basePos_124_);
lean_dec_ref(v_s_63_);
return v_b_66_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = l_String_Slice_pos_x21(v_s_63_, v_basePos_124_);
lean_dec(v_basePos_124_);
v___x_133_ = lean_box(3);
v_it_68_ = v___x_133_;
v_startPos_69_ = v___x_132_;
v_endPos_70_ = v___x_127_;
goto v___jp_67_;
}
}
else
{
lean_object* v___x_134_; uint8_t v_stackByte_135_; lean_object* v___x_136_; uint8_t v_patByte_137_; uint8_t v___x_138_; 
lean_dec(v___x_127_);
v___x_134_ = lean_nat_add(v_startInclusive_122_, v_stackPos_113_);
v_stackByte_135_ = lean_string_get_byte_fast(v_str_121_, v___x_134_);
v___x_136_ = lean_nat_add(v_startInclusive_119_, v_needlePos_114_);
v_patByte_137_ = lean_string_get_byte_fast(v_str_118_, v___x_136_);
v___x_138_ = lean_uint8_dec_eq(v_stackByte_135_, v_patByte_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; uint8_t v_decide_140_; 
lean_dec(v___x_125_);
v___x_139_ = lean_unsigned_to_nat(0u);
v_decide_140_ = lean_nat_dec_eq(v_needlePos_114_, v___x_139_);
if (v_decide_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_newNeedlePos_143_; uint8_t v___x_144_; 
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = lean_nat_sub(v_needlePos_114_, v___x_141_);
lean_dec(v_needlePos_114_);
v_newNeedlePos_143_ = lean_array_fget_borrowed(v_table_112_, v___x_142_);
lean_dec(v___x_142_);
v___x_144_ = lean_nat_dec_eq(v_newNeedlePos_143_, v___x_139_);
if (v___x_144_ == 0)
{
lean_object* v_oldBasePos_145_; lean_object* v___x_146_; lean_object* v_newBasePos_147_; lean_object* v___x_149_; 
lean_inc(v_newNeedlePos_143_);
v_oldBasePos_145_ = l_String_Slice_pos_x21(v_s_63_, v_basePos_124_);
lean_dec(v_basePos_124_);
v___x_146_ = lean_nat_sub(v_stackPos_113_, v_newNeedlePos_143_);
v_newBasePos_147_ = l_String_Slice_pos_x21(v_s_63_, v___x_146_);
lean_dec(v___x_146_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 3, v_newNeedlePos_143_);
v___x_149_ = v___x_116_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_needle_111_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_table_112_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_stackPos_113_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v_newNeedlePos_143_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
v_it_68_ = v___x_149_;
v_startPos_69_ = v_oldBasePos_145_;
v_endPos_70_ = v_newBasePos_147_;
goto v___jp_67_;
}
}
else
{
lean_object* v_basePos_151_; lean_object* v_nextStackPos_152_; lean_object* v___x_154_; 
v_basePos_151_ = l_String_Slice_pos_x21(v_s_63_, v_basePos_124_);
lean_dec(v_basePos_124_);
v_nextStackPos_152_ = l_String_Slice_posGE___redArg(v_s_63_, v_stackPos_113_);
lean_inc(v_nextStackPos_152_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 3, v___x_139_);
lean_ctor_set(v___x_116_, 2, v_nextStackPos_152_);
v___x_154_ = v___x_116_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_needle_111_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_table_112_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_nextStackPos_152_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v___x_139_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
v_it_68_ = v___x_154_;
v_startPos_69_ = v_basePos_151_;
v_endPos_70_ = v_nextStackPos_152_;
goto v___jp_67_;
}
}
}
else
{
lean_object* v_basePos_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_nextStackPos_159_; lean_object* v___x_161_; 
lean_dec(v_basePos_124_);
lean_dec(v_needlePos_114_);
v_basePos_156_ = l_String_Slice_pos_x21(v_s_63_, v_stackPos_113_);
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_add(v_stackPos_113_, v___x_157_);
lean_dec(v_stackPos_113_);
v_nextStackPos_159_ = l_String_Slice_posGE___redArg(v_s_63_, v___x_158_);
lean_inc(v_nextStackPos_159_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 3, v___x_139_);
lean_ctor_set(v___x_116_, 2, v_nextStackPos_159_);
v___x_161_ = v___x_116_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_needle_111_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_table_112_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v_nextStackPos_159_);
lean_ctor_set(v_reuseFailAlloc_162_, 3, v___x_139_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
v_it_68_ = v___x_161_;
v_startPos_69_ = v_basePos_156_;
v_endPos_70_ = v_nextStackPos_159_;
goto v___jp_67_;
}
}
}
else
{
lean_object* v___x_163_; lean_object* v_nextStackPos_164_; lean_object* v_nextNeedlePos_165_; uint8_t v_decide_166_; 
lean_dec(v_basePos_124_);
v___x_163_ = lean_unsigned_to_nat(1u);
v_nextStackPos_164_ = lean_nat_add(v_stackPos_113_, v___x_163_);
lean_dec(v_stackPos_113_);
v_nextNeedlePos_165_ = lean_nat_add(v_needlePos_114_, v___x_163_);
lean_dec(v_needlePos_114_);
v_decide_166_ = lean_nat_dec_eq(v_nextNeedlePos_165_, v___x_125_);
lean_dec(v___x_125_);
if (v_decide_166_ == 0)
{
lean_object* v___x_168_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 3, v_nextNeedlePos_165_);
lean_ctor_set(v___x_116_, 2, v_nextStackPos_164_);
v___x_168_ = v___x_116_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_needle_111_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_table_112_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v_nextStackPos_164_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v_nextNeedlePos_165_);
v___x_168_ = v_reuseFailAlloc_170_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
v_a_65_ = v___x_168_;
goto _start;
}
}
else
{
lean_object* v___x_171_; lean_object* v___x_173_; 
lean_dec(v_nextNeedlePos_165_);
v___x_171_ = lean_unsigned_to_nat(0u);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 3, v___x_171_);
lean_ctor_set(v___x_116_, 2, v_nextStackPos_164_);
v___x_173_ = v___x_116_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_needle_111_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_table_112_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_nextStackPos_164_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
v_it_79_ = v___x_173_;
goto v___jp_78_;
}
}
}
}
}
}
default: 
{
lean_dec_ref(v_s_63_);
return v_b_66_;
}
}
v___jp_67_:
{
lean_object* v___x_71_; lean_object* v_str_72_; lean_object* v_startInclusive_73_; lean_object* v_endExclusive_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
lean_inc_ref(v_s_63_);
v___x_71_ = l_String_Slice_slice_x21(v_s_63_, v_startPos_69_, v_endPos_70_);
lean_dec(v_endPos_70_);
lean_dec(v_startPos_69_);
v_str_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_str_72_);
v_startInclusive_73_ = lean_ctor_get(v___x_71_, 1);
lean_inc(v_startInclusive_73_);
v_endExclusive_74_ = lean_ctor_get(v___x_71_, 2);
lean_inc(v_endExclusive_74_);
lean_dec_ref(v___x_71_);
v___x_75_ = lean_string_utf8_extract_fast(v_str_72_, v_startInclusive_73_, v_endExclusive_74_);
lean_dec(v_endExclusive_74_);
lean_dec(v_startInclusive_73_);
lean_dec_ref(v_str_72_);
v___x_76_ = lean_string_append(v_b_66_, v___x_75_);
lean_dec_ref(v___x_75_);
v_a_65_ = v_it_68_;
v_b_66_ = v___x_76_;
goto _start;
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_string_utf8_byte_size(v_replacement_64_);
v___x_82_ = lean_string_utf8_extract_fast(v_replacement_64_, v___x_80_, v___x_81_);
v___x_83_ = lean_string_append(v_b_66_, v___x_82_);
lean_dec_ref(v___x_82_);
v_a_65_ = v_it_79_;
v_b_66_ = v___x_83_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg___boxed(lean_object* v_s_176_, lean_object* v_replacement_177_, lean_object* v_a_178_, lean_object* v_b_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(v_s_176_, v_replacement_177_, v_a_178_, v_b_179_);
lean_dec_ref(v_replacement_177_);
return v_res_180_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1));
v___x_187_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2, &l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2_once, _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__2);
v___x_190_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__1));
v___x_191_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_188_);
lean_ctor_set(v___x_191_, 3, v___x_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(lean_object* v_s_192_, lean_object* v_replacement_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__0));
v___x_195_ = lean_obj_once(&l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3, &l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3_once, _init_l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__3);
v___x_196_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(v_s_192_, v_replacement_193_, v___x_195_, v___x_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___boxed(lean_object* v_s_197_, lean_object* v_replacement_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(v_s_197_, v_replacement_198_);
lean_dec_ref(v_replacement_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(lean_object* v_s_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_202_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_203_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote___closed__0));
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_string_utf8_byte_size(v_s_201_);
v___x_206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_206_, 0, v_s_201_);
lean_ctor_set(v___x_206_, 1, v___x_204_);
lean_ctor_set(v___x_206_, 2, v___x_205_);
v___x_207_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(v___x_206_, v___x_203_);
v___x_208_ = lean_string_append(v___x_202_, v___x_207_);
lean_dec_ref(v___x_207_);
v___x_209_ = lean_string_append(v___x_208_, v___x_202_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0(lean_object* v_s_210_, lean_object* v_pattern_211_, lean_object* v_replacement_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg(v_s_210_, v_replacement_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___boxed(lean_object* v_s_214_, lean_object* v_pattern_215_, lean_object* v_replacement_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0(v_s_214_, v_pattern_215_, v_replacement_216_);
lean_dec_ref(v_replacement_216_);
lean_dec_ref(v_pattern_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0(lean_object* v_s_218_, lean_object* v_replacement_219_, lean_object* v_inst_220_, lean_object* v_R_221_, lean_object* v_a_222_, lean_object* v_b_223_, lean_object* v_c_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___redArg(v_s_218_, v_replacement_219_, v_a_222_, v_b_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0___boxed(lean_object* v_s_226_, lean_object* v_replacement_227_, lean_object* v_inst_228_, lean_object* v_R_229_, lean_object* v_a_230_, lean_object* v_b_231_, lean_object* v_c_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0_spec__0(v_s_226_, v_replacement_227_, v_inst_228_, v_R_229_, v_a_230_, v_b_231_, v_c_232_);
lean_dec_ref(v_replacement_227_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Samply_0__Lake_Samply_extractToken_spec__1(lean_object* v_s_234_, lean_object* v_pos_235_){
_start:
{
lean_object* v_str_236_; lean_object* v_startInclusive_237_; lean_object* v_endExclusive_238_; lean_object* v___x_239_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v_decide_250_; 
v_str_236_ = lean_ctor_get(v_s_234_, 0);
v_startInclusive_237_ = lean_ctor_get(v_s_234_, 1);
v_endExclusive_238_ = lean_ctor_get(v_s_234_, 2);
v___x_239_ = lean_nat_add(v_startInclusive_237_, v_pos_235_);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_nat_sub(v_endExclusive_238_, v___x_239_);
v_decide_250_ = lean_nat_dec_eq(v___x_248_, v___x_249_);
lean_dec(v___x_249_);
if (v_decide_250_ == 0)
{
uint32_t v___x_251_; uint32_t v___x_262_; uint8_t v___x_263_; 
v___x_251_ = lean_string_utf8_get_fast(v_str_236_, v___x_239_);
v___x_262_ = 65;
v___x_263_ = lean_uint32_dec_le(v___x_262_, v___x_251_);
if (v___x_263_ == 0)
{
goto v___jp_257_;
}
else
{
uint32_t v___x_264_; uint8_t v___x_265_; 
v___x_264_ = 90;
v___x_265_ = lean_uint32_dec_le(v___x_251_, v___x_264_);
if (v___x_265_ == 0)
{
goto v___jp_257_;
}
else
{
goto v___jp_240_;
}
}
v___jp_252_:
{
uint32_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = 48;
v___x_254_ = lean_uint32_dec_le(v___x_253_, v___x_251_);
if (v___x_254_ == 0)
{
lean_dec(v___x_239_);
return v_pos_235_;
}
else
{
uint32_t v___x_255_; uint8_t v___x_256_; 
v___x_255_ = 57;
v___x_256_ = lean_uint32_dec_le(v___x_251_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec(v___x_239_);
return v_pos_235_;
}
else
{
goto v___jp_240_;
}
}
}
v___jp_257_:
{
uint32_t v___x_258_; uint8_t v___x_259_; 
v___x_258_ = 97;
v___x_259_ = lean_uint32_dec_le(v___x_258_, v___x_251_);
if (v___x_259_ == 0)
{
goto v___jp_252_;
}
else
{
uint32_t v___x_260_; uint8_t v___x_261_; 
v___x_260_ = 122;
v___x_261_ = lean_uint32_dec_le(v___x_251_, v___x_260_);
if (v___x_261_ == 0)
{
goto v___jp_252_;
}
else
{
goto v___jp_240_;
}
}
}
}
else
{
lean_dec(v___x_239_);
return v_pos_235_;
}
v___jp_240_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_241_ = lean_string_utf8_next_fast(v_str_236_, v___x_239_);
v___x_242_ = lean_nat_sub(v___x_241_, v___x_239_);
lean_dec(v___x_239_);
v___x_243_ = lean_nat_add(v_pos_235_, v___x_242_);
lean_dec(v___x_242_);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_add(v_pos_235_, v___x_244_);
v___x_246_ = lean_nat_dec_le(v___x_245_, v___x_243_);
lean_dec(v___x_245_);
if (v___x_246_ == 0)
{
lean_dec(v___x_243_);
return v_pos_235_;
}
else
{
lean_dec(v_pos_235_);
v_pos_235_ = v___x_243_;
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
lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(lean_object* v_msg_420_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_1178__overap_423_; lean_object* v___x_424_; 
v___x_422_ = lean_obj_once(&l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0, &l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0_once, _init_l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___closed__0);
v___x_1178__overap_423_ = lean_panic_fn_borrowed(v___x_422_, v_msg_420_);
v___x_424_ = lean_apply_1(v___x_1178__overap_423_, lean_box(0));
return v___x_424_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_420_ = stack[0].m_obj;
lean_object* v_res_425_;
v_res_425_ = l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(v_msg_420_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1___boxed(lean_object* v_msg_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(v_msg_426_);
return v_res_428_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__2));
v___x_433_ = lean_mk_io_user_error(v___x_432_);
return v___x_433_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(lean_object* v_val_434_, lean_object* v_timeoutMs_435_, lean_object* v_cfg_436_, lean_object* v_proc_437_, lean_object* v_logFile_438_, lean_object* v_port_439_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_441_ = lean_box(0);
v___x_442_ = lean_io_mono_ms_now();
v___x_443_ = lean_nat_sub(v___x_442_, v_val_434_);
lean_dec(v___x_442_);
v___x_444_ = lean_nat_dec_lt(v_timeoutMs_435_, v___x_443_);
lean_dec(v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
v___x_445_ = lean_io_process_child_try_wait(v_cfg_436_, v_proc_437_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref_known(v___x_445_, 1);
if (lean_obj_tag(v_a_446_) == 1)
{
lean_object* v_val_447_; lean_object* v___x_448_; 
lean_dec(v_port_439_);
v_val_447_ = lean_ctor_get(v_a_446_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v_a_446_, 1);
v___x_448_ = l_IO_FS_readFile(v_logFile_438_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_465_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_465_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_465_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_465_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; uint32_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_453_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__0));
v___x_454_ = lean_unbox_uint32(v_val_447_);
lean_dec(v_val_447_);
v___x_455_ = lean_uint32_to_nat(v___x_454_);
v___x_456_ = l_Nat_reprFast(v___x_455_);
v___x_457_ = lean_string_append(v___x_453_, v___x_456_);
lean_dec_ref(v___x_456_);
v___x_458_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__1));
v___x_459_ = lean_string_append(v___x_457_, v___x_458_);
v___x_460_ = lean_string_append(v___x_459_, v_a_449_);
lean_dec(v_a_449_);
v___x_461_ = lean_mk_io_user_error(v___x_460_);
if (v_isShared_452_ == 0)
{
lean_ctor_set_tag(v___x_451_, 1);
lean_ctor_set(v___x_451_, 0, v___x_461_);
v___x_463_ = v___x_451_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec(v_val_447_);
v_a_466_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_448_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_448_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
else
{
lean_object* v___x_474_; 
lean_dec(v_a_446_);
v___x_474_ = l_IO_FS_readFile(v_logFile_438_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_487_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_487_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_487_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_487_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; 
lean_inc(v_port_439_);
v___x_479_ = l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken(v_a_475_, v_port_439_);
lean_dec(v_a_475_);
if (lean_obj_tag(v___x_479_) == 1)
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec(v_port_439_);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v___x_441_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_480_);
v___x_482_ = v___x_477_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
else
{
uint32_t v___x_484_; lean_object* v___x_485_; 
lean_dec(v___x_479_);
lean_del_object(v___x_477_);
v___x_484_ = 200;
v___x_485_ = l_IO_sleep(v___x_484_);
goto _start;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v_port_439_);
v_a_488_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_474_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_474_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec(v_port_439_);
v_a_496_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_445_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_445_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v_port_439_);
v___x_504_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___closed__3);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_434_ = stack[0].m_obj;
lean_object* v_timeoutMs_435_ = stack[1].m_obj;
lean_object* v_cfg_436_ = stack[2].m_obj;
lean_object* v_proc_437_ = stack[3].m_obj;
lean_object* v_logFile_438_ = stack[4].m_obj;
lean_object* v_port_439_ = stack[5].m_obj;
lean_object* v_res_506_;
v_res_506_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v_val_434_, v_timeoutMs_435_, v_cfg_436_, v_proc_437_, v_logFile_438_, v_port_439_);
stack->m_obj
 = v_res_506_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg___boxed(lean_object* v_val_507_, lean_object* v_timeoutMs_508_, lean_object* v_cfg_509_, lean_object* v_proc_510_, lean_object* v_logFile_511_, lean_object* v_port_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v_val_507_, v_timeoutMs_508_, v_cfg_509_, v_proc_510_, v_logFile_511_, v_port_512_);
lean_dec_ref(v_logFile_511_);
lean_dec_ref(v_proc_510_);
lean_dec_ref(v_cfg_509_);
lean_dec(v_timeoutMs_508_);
lean_dec(v_val_507_);
return v_res_514_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_518_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__2));
v___x_519_ = lean_unsigned_to_nat(2u);
v___x_520_ = lean_unsigned_to_nat(58u);
v___x_521_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__1));
v___x_522_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__0));
v___x_523_ = l_mkPanicMessageWithDecl(v___x_522_, v___x_521_, v___x_520_, v___x_519_, v___x_518_);
return v___x_523_;
}
}
lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(lean_object* v_cfg_524_, lean_object* v_logFile_525_, lean_object* v_proc_526_, lean_object* v_port_527_, lean_object* v_timeoutMs_528_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_io_mono_ms_now();
v___x_531_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v___x_530_, v_timeoutMs_528_, v_cfg_524_, v_proc_526_, v_logFile_525_, v_port_527_);
lean_dec(v___x_530_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_543_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_543_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_543_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_543_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_fst_536_; 
v_fst_536_ = lean_ctor_get(v_a_532_, 0);
lean_inc(v_fst_536_);
lean_dec(v_a_532_);
if (lean_obj_tag(v_fst_536_) == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_del_object(v___x_534_);
v___x_537_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3, &l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___closed__3);
v___x_538_ = l_panic___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__1(v___x_537_);
return v___x_538_;
}
else
{
lean_object* v_val_539_; lean_object* v___x_541_; 
v_val_539_ = lean_ctor_get(v_fst_536_, 0);
lean_inc(v_val_539_);
lean_dec_ref_known(v_fst_536_, 1);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v_val_539_);
v___x_541_ = v___x_534_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_val_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_a_544_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_531_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_531_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_524_ = stack[0].m_obj;
lean_object* v_logFile_525_ = stack[1].m_obj;
lean_object* v_proc_526_ = stack[2].m_obj;
lean_object* v_port_527_ = stack[3].m_obj;
lean_object* v_timeoutMs_528_ = stack[4].m_obj;
lean_object* v_res_552_;
v_res_552_ = l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(v_cfg_524_, v_logFile_525_, v_proc_526_, v_port_527_, v_timeoutMs_528_);
stack->m_obj
 = v_res_552_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer___boxed(lean_object* v_cfg_553_, lean_object* v_logFile_554_, lean_object* v_proc_555_, lean_object* v_port_556_, lean_object* v_timeoutMs_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(v_cfg_553_, v_logFile_554_, v_proc_555_, v_port_556_, v_timeoutMs_557_);
lean_dec(v_timeoutMs_557_);
lean_dec_ref(v_proc_555_);
lean_dec_ref(v_logFile_554_);
lean_dec_ref(v_cfg_553_);
return v_res_559_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(lean_object* v_val_560_, lean_object* v_timeoutMs_561_, lean_object* v_cfg_562_, lean_object* v_proc_563_, lean_object* v_logFile_564_, lean_object* v_port_565_, lean_object* v_inst_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___redArg(v_val_560_, v_timeoutMs_561_, v_cfg_562_, v_proc_563_, v_logFile_564_, v_port_565_);
return v___x_569_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_560_ = stack[0].m_obj;
lean_object* v_timeoutMs_561_ = stack[1].m_obj;
lean_object* v_cfg_562_ = stack[2].m_obj;
lean_object* v_proc_563_ = stack[3].m_obj;
lean_object* v_logFile_564_ = stack[4].m_obj;
lean_object* v_port_565_ = stack[5].m_obj;
lean_object* v_a_567_ = stack[7].m_obj;
lean_object* v_res_570_;
v_res_570_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(v_val_560_, v_timeoutMs_561_, v_cfg_562_, v_proc_563_, v_logFile_564_, v_port_565_, lean_box(0), v_a_567_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0___boxed(lean_object* v_val_571_, lean_object* v_timeoutMs_572_, lean_object* v_cfg_573_, lean_object* v_proc_574_, lean_object* v_logFile_575_, lean_object* v_port_576_, lean_object* v_inst_577_, lean_object* v_a_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lake_CLI_Samply_0__Lake_Samply_waitForServer_spec__0(v_val_571_, v_timeoutMs_572_, v_cfg_573_, v_proc_574_, v_logFile_575_, v_port_576_, v_inst_577_, v_a_578_);
lean_dec_ref(v_a_578_);
lean_dec_ref(v_logFile_575_);
lean_dec_ref(v_proc_574_);
lean_dec_ref(v_cfg_573_);
lean_dec(v_timeoutMs_572_);
lean_dec(v_val_571_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(lean_object* v_j_581_, lean_object* v_k_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = l_Lean_Json_getObjValD(v_j_581_, v_k_582_);
v___x_584_ = l_Lean_Json_getStr_x3f(v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0___boxed(lean_object* v_j_585_, lean_object* v_k_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_j_585_, v_k_586_);
lean_dec_ref(v_k_586_);
return v_res_587_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(lean_object* v_e_588_){
_start:
{
if (lean_obj_tag(v_e_588_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
v_a_590_ = lean_ctor_get(v_e_588_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_e_588_);
if (v_isSharedCheck_598_ == 0)
{
v___x_592_ = v_e_588_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v_e_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = lean_mk_io_user_error(v_a_590_);
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 1);
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
v_a_599_ = lean_ctor_get(v_e_588_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v_e_588_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v_e_588_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v_e_588_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 0);
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_588_ = stack[0].m_obj;
lean_object* v_res_607_;
v_res_607_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v_e_588_);
stack->m_obj
 = v_res_607_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg___boxed(lean_object* v_e_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v_e_608_);
return v_res_610_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(lean_object* v_00_u03b1_611_, lean_object* v_e_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v_e_612_);
return v___x_614_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_612_ = stack[1].m_obj;
lean_object* v_res_615_;
v_res_615_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(lean_box(0), v_e_612_);
stack->m_obj
 = v_res_615_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___boxed(lean_object* v_00_u03b1_616_, lean_object* v_e_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1(v_00_u03b1_616_, v_e_617_);
return v_res_619_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(size_t v_sz_620_, size_t v_i_621_, lean_object* v_bs_622_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_lt(v_i_621_, v_sz_620_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v_bs_622_);
return v___x_624_;
}
else
{
lean_object* v_v_625_; lean_object* v___x_626_; lean_object* v_bs_x27_627_; size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; 
v_v_625_ = lean_array_uget(v_bs_622_, v_i_621_);
v___x_626_ = lean_unsigned_to_nat(0u);
v_bs_x27_627_ = lean_array_uset(v_bs_622_, v_i_621_, v___x_626_);
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_add(v_i_621_, v___x_628_);
v___x_630_ = lean_array_uset(v_bs_x27_627_, v_i_621_, v_v_625_);
v_i_621_ = v___x_629_;
v_bs_622_ = v___x_630_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_620_ = stack[0].m_num;
size_t v_i_621_ = stack[1].m_num;
lean_object* v_bs_622_ = stack[2].m_obj;
lean_object* v_res_632_;
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(v_sz_620_, v_i_621_, v_bs_622_);
stack->m_obj
 = v_res_632_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_633_, lean_object* v_i_634_, lean_object* v_bs_635_){
_start:
{
size_t v_sz_boxed_636_; size_t v_i_boxed_637_; lean_object* v_res_638_; 
v_sz_boxed_636_ = lean_unbox_usize(v_sz_633_);
lean_dec(v_sz_633_);
v_i_boxed_637_ = lean_unbox_usize(v_i_634_);
lean_dec(v_i_634_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(v_sz_boxed_636_, v_i_boxed_637_, v_bs_635_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(lean_object* v_x_640_){
_start:
{
if (lean_obj_tag(v_x_640_) == 4)
{
lean_object* v_elems_641_; size_t v_sz_642_; size_t v___x_643_; lean_object* v___x_644_; 
v_elems_641_ = lean_ctor_get(v_x_640_, 0);
lean_inc_ref(v_elems_641_);
lean_dec_ref_known(v_x_640_, 1);
v_sz_642_ = lean_array_size(v_elems_641_);
v___x_643_ = ((size_t)0ULL);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4_spec__5(v_sz_642_, v___x_643_, v_elems_641_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_645_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_646_ = lean_unsigned_to_nat(80u);
v___x_647_ = l_Lean_Json_pretty(v_x_640_, v___x_646_);
v___x_648_ = lean_string_append(v___x_645_, v___x_647_);
lean_dec_ref(v___x_647_);
v___x_649_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_650_ = lean_string_append(v___x_648_, v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(lean_object* v_j_652_, lean_object* v_k_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = l_Lean_Json_getObjValD(v_j_652_, v_k_653_);
v___x_655_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3___boxed(lean_object* v_j_656_, lean_object* v_k_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_j_656_, v_k_657_);
lean_dec_ref(v_k_657_);
return v_res_658_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(size_t v_sz_659_, size_t v_i_660_, lean_object* v_bs_661_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = lean_usize_dec_lt(v_i_660_, v_sz_659_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
v___x_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_663_, 0, v_bs_661_);
return v___x_663_;
}
else
{
lean_object* v_v_664_; lean_object* v___x_665_; 
v_v_664_ = lean_array_uget_borrowed(v_bs_661_, v_i_660_);
lean_inc(v_v_664_);
v___x_665_ = l_Lean_Json_getNat_x3f(v_v_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_bs_661_);
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_675_; lean_object* v_bs_x27_676_; size_t v___x_677_; size_t v___x_678_; lean_object* v___x_679_; 
v_a_674_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_665_, 1);
v___x_675_ = lean_unsigned_to_nat(0u);
v_bs_x27_676_ = lean_array_uset(v_bs_661_, v_i_660_, v___x_675_);
v___x_677_ = ((size_t)1ULL);
v___x_678_ = lean_usize_add(v_i_660_, v___x_677_);
v___x_679_ = lean_array_uset(v_bs_x27_676_, v_i_660_, v_a_674_);
v_i_660_ = v___x_678_;
v_bs_661_ = v___x_679_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_659_ = stack[0].m_num;
size_t v_i_660_ = stack[1].m_num;
lean_object* v_bs_661_ = stack[2].m_obj;
lean_object* v_res_681_;
v_res_681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5_spec__7_spec__9(v_sz_659_, v_i_660_, v_bs_661_);
stack->m_obj
 = v_res_681_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(size_t v_sz_707_, size_t v_i_708_, lean_object* v_bs_709_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13_0interp(lean_interpreter_value* stack)
{
size_t v_sz_707_ = stack[0].m_num;
size_t v_i_708_ = stack[1].m_num;
lean_object* v_bs_709_ = stack[2].m_obj;
lean_object* v_res_720_;
v_res_720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(v_sz_707_, v_i_708_, v_bs_709_);
stack->m_obj
 = v_res_720_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13___boxed(lean_object* v_sz_721_, lean_object* v_i_722_, lean_object* v_bs_723_){
_start:
{
size_t v_sz_boxed_724_; size_t v_i_boxed_725_; lean_object* v_res_726_; 
v_sz_boxed_724_ = lean_unbox_usize(v_sz_721_);
lean_dec(v_sz_721_);
v_i_boxed_725_ = lean_unbox_usize(v_i_722_);
lean_dec(v_i_722_);
v_res_726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(v_sz_boxed_724_, v_i_boxed_725_, v_bs_723_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(lean_object* v_a_727_){
_start:
{
size_t v_sz_728_; size_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_sz_728_ = lean_array_size(v_a_727_);
v___x_729_ = ((size_t)0ULL);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8_spec__13(v_sz_728_, v___x_729_, v_a_727_);
v___x_731_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(lean_object* v_a_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 0)
{
uint8_t v___x_734_; 
v___x_734_ = 0;
return v___x_734_;
}
else
{
lean_object* v_key_735_; lean_object* v_tail_736_; uint8_t v___x_737_; 
v_key_735_ = lean_ctor_get(v_x_733_, 0);
v_tail_736_ = lean_ctor_get(v_x_733_, 2);
v___x_737_ = lean_nat_dec_eq(v_key_735_, v_a_732_);
if (v___x_737_ == 0)
{
v_x_733_ = v_tail_736_;
goto _start;
}
else
{
return v___x_737_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_732_ = stack[0].m_obj;
lean_object* v_x_733_ = stack[1].m_obj;
uint8_t v_res_739_;
v_res_739_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_732_, v_x_733_);
stack->m_num = v_res_739_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg___boxed(lean_object* v_a_740_, lean_object* v_x_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_740_, v_x_741_);
lean_dec(v_x_741_);
lean_dec(v_a_740_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(lean_object* v_m_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_buckets_746_; lean_object* v___x_747_; uint64_t v___x_748_; uint64_t v___x_749_; uint64_t v___x_750_; uint64_t v_fold_751_; uint64_t v___x_752_; uint64_t v___x_753_; uint64_t v___x_754_; size_t v___x_755_; size_t v___x_756_; size_t v___x_757_; size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_buckets_746_ = lean_ctor_get(v_m_744_, 1);
v___x_747_ = lean_array_get_size(v_buckets_746_);
v___x_748_ = lean_uint64_of_nat(v_a_745_);
v___x_749_ = 32ULL;
v___x_750_ = lean_uint64_shift_right(v___x_748_, v___x_749_);
v_fold_751_ = lean_uint64_xor(v___x_748_, v___x_750_);
v___x_752_ = 16ULL;
v___x_753_ = lean_uint64_shift_right(v_fold_751_, v___x_752_);
v___x_754_ = lean_uint64_xor(v_fold_751_, v___x_753_);
v___x_755_ = lean_uint64_to_usize(v___x_754_);
v___x_756_ = lean_usize_of_nat(v___x_747_);
v___x_757_ = ((size_t)1ULL);
v___x_758_ = lean_usize_sub(v___x_756_, v___x_757_);
v___x_759_ = lean_usize_land(v___x_755_, v___x_758_);
v___x_760_ = lean_array_uget_borrowed(v_buckets_746_, v___x_759_);
v___x_761_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_745_, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_744_ = stack[0].m_obj;
lean_object* v_a_745_ = stack[1].m_obj;
uint8_t v_res_762_;
v_res_762_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_m_744_, v_a_745_);
stack->m_num = v_res_762_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg___boxed(lean_object* v_m_763_, lean_object* v_a_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_m_763_, v_a_764_);
lean_dec(v_a_764_);
lean_dec_ref(v_m_763_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
return v_x_767_;
}
else
{
lean_object* v_key_769_; lean_object* v_value_770_; lean_object* v_tail_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_794_; 
v_key_769_ = lean_ctor_get(v_x_768_, 0);
v_value_770_ = lean_ctor_get(v_x_768_, 1);
v_tail_771_ = lean_ctor_get(v_x_768_, 2);
v_isSharedCheck_794_ = !lean_is_exclusive(v_x_768_);
if (v_isSharedCheck_794_ == 0)
{
v___x_773_ = v_x_768_;
v_isShared_774_ = v_isSharedCheck_794_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_tail_771_);
lean_inc(v_value_770_);
lean_inc(v_key_769_);
lean_dec(v_x_768_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_794_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; uint64_t v___x_776_; uint64_t v___x_777_; uint64_t v___x_778_; uint64_t v_fold_779_; uint64_t v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; size_t v___x_783_; size_t v___x_784_; size_t v___x_785_; size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_775_ = lean_array_get_size(v_x_767_);
v___x_776_ = lean_uint64_of_nat(v_key_769_);
v___x_777_ = 32ULL;
v___x_778_ = lean_uint64_shift_right(v___x_776_, v___x_777_);
v_fold_779_ = lean_uint64_xor(v___x_776_, v___x_778_);
v___x_780_ = 16ULL;
v___x_781_ = lean_uint64_shift_right(v_fold_779_, v___x_780_);
v___x_782_ = lean_uint64_xor(v_fold_779_, v___x_781_);
v___x_783_ = lean_uint64_to_usize(v___x_782_);
v___x_784_ = lean_usize_of_nat(v___x_775_);
v___x_785_ = ((size_t)1ULL);
v___x_786_ = lean_usize_sub(v___x_784_, v___x_785_);
v___x_787_ = lean_usize_land(v___x_783_, v___x_786_);
v___x_788_ = lean_array_uget_borrowed(v_x_767_, v___x_787_);
lean_inc(v___x_788_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 2, v___x_788_);
v___x_790_ = v___x_773_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_key_769_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_value_770_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v___x_788_);
v___x_790_ = v_reuseFailAlloc_793_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; 
v___x_791_ = lean_array_uset(v_x_767_, v___x_787_, v___x_790_);
v_x_767_ = v___x_791_;
v_x_768_ = v_tail_771_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(lean_object* v_i_795_, lean_object* v_source_796_, lean_object* v_target_797_){
_start:
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = lean_array_get_size(v_source_796_);
v___x_799_ = lean_nat_dec_lt(v_i_795_, v___x_798_);
if (v___x_799_ == 0)
{
lean_dec_ref(v_source_796_);
lean_dec(v_i_795_);
return v_target_797_;
}
else
{
lean_object* v_es_800_; lean_object* v___x_801_; lean_object* v_source_802_; lean_object* v_target_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_es_800_ = lean_array_fget(v_source_796_, v_i_795_);
v___x_801_ = lean_box(0);
v_source_802_ = lean_array_fset(v_source_796_, v_i_795_, v___x_801_);
v_target_803_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(v_target_797_, v_es_800_);
v___x_804_ = lean_unsigned_to_nat(1u);
v___x_805_ = lean_nat_add(v_i_795_, v___x_804_);
lean_dec(v_i_795_);
v_i_795_ = v___x_805_;
v_source_796_ = v_source_802_;
v_target_797_ = v_target_803_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(lean_object* v_data_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_nbuckets_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_808_ = lean_array_get_size(v_data_807_);
v___x_809_ = lean_unsigned_to_nat(2u);
v_nbuckets_810_ = lean_nat_mul(v___x_808_, v___x_809_);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_box(0);
v___x_813_ = lean_mk_array(v_nbuckets_810_, v___x_812_);
v___x_814_ = lean_array_propagate_mark(v_data_807_, v___x_813_);
v___x_815_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(v___x_811_, v_data_807_, v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(lean_object* v_m_816_, lean_object* v_a_817_, lean_object* v_b_818_){
_start:
{
lean_object* v_size_819_; lean_object* v_buckets_820_; lean_object* v___x_821_; uint64_t v___x_822_; uint64_t v___x_823_; uint64_t v___x_824_; uint64_t v_fold_825_; uint64_t v___x_826_; uint64_t v___x_827_; uint64_t v___x_828_; size_t v___x_829_; size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; lean_object* v_bkt_834_; uint8_t v___x_835_; 
v_size_819_ = lean_ctor_get(v_m_816_, 0);
v_buckets_820_ = lean_ctor_get(v_m_816_, 1);
v___x_821_ = lean_array_get_size(v_buckets_820_);
v___x_822_ = lean_uint64_of_nat(v_a_817_);
v___x_823_ = 32ULL;
v___x_824_ = lean_uint64_shift_right(v___x_822_, v___x_823_);
v_fold_825_ = lean_uint64_xor(v___x_822_, v___x_824_);
v___x_826_ = 16ULL;
v___x_827_ = lean_uint64_shift_right(v_fold_825_, v___x_826_);
v___x_828_ = lean_uint64_xor(v_fold_825_, v___x_827_);
v___x_829_ = lean_uint64_to_usize(v___x_828_);
v___x_830_ = lean_usize_of_nat(v___x_821_);
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_sub(v___x_830_, v___x_831_);
v___x_833_ = lean_usize_land(v___x_829_, v___x_832_);
v_bkt_834_ = lean_array_uget_borrowed(v_buckets_820_, v___x_833_);
v___x_835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_817_, v_bkt_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_856_; 
lean_inc_ref(v_buckets_820_);
lean_inc(v_size_819_);
v_isSharedCheck_856_ = !lean_is_exclusive(v_m_816_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; lean_object* v_unused_858_; 
v_unused_857_ = lean_ctor_get(v_m_816_, 1);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_m_816_, 0);
lean_dec(v_unused_858_);
v___x_837_ = v_m_816_;
v_isShared_838_ = v_isSharedCheck_856_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_m_816_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_856_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v_size_x27_840_; lean_object* v___x_841_; lean_object* v_buckets_x27_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_839_ = lean_unsigned_to_nat(1u);
v_size_x27_840_ = lean_nat_add(v_size_819_, v___x_839_);
lean_dec(v_size_819_);
lean_inc(v_bkt_834_);
v___x_841_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_841_, 0, v_a_817_);
lean_ctor_set(v___x_841_, 1, v_b_818_);
lean_ctor_set(v___x_841_, 2, v_bkt_834_);
v_buckets_x27_842_ = lean_array_uset(v_buckets_820_, v___x_833_, v___x_841_);
v___x_843_ = lean_unsigned_to_nat(4u);
v___x_844_ = lean_nat_mul(v_size_x27_840_, v___x_843_);
v___x_845_ = lean_unsigned_to_nat(3u);
v___x_846_ = lean_nat_div(v___x_844_, v___x_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_array_get_size(v_buckets_x27_842_);
v___x_848_ = lean_nat_dec_le(v___x_846_, v___x_847_);
lean_dec(v___x_846_);
if (v___x_848_ == 0)
{
lean_object* v_val_849_; lean_object* v___x_851_; 
v_val_849_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(v_buckets_x27_842_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_val_849_);
lean_ctor_set(v___x_837_, 0, v_size_x27_840_);
v___x_851_ = v___x_837_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_size_x27_840_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_val_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
else
{
lean_object* v___x_854_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_buckets_x27_842_);
lean_ctor_set(v___x_837_, 0, v_size_x27_840_);
v___x_854_ = v___x_837_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_size_x27_840_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_buckets_x27_842_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_dec(v_b_818_);
lean_dec(v_a_817_);
return v_m_816_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_as_862_, size_t v_sz_863_, size_t v_i_864_, lean_object* v_b_865_){
_start:
{
lean_object* v_a_868_; uint8_t v___x_872_; 
v___x_872_ = lean_usize_dec_lt(v_i_864_, v_sz_863_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v_b_865_);
return v___x_873_;
}
else
{
lean_object* v_snd_874_; lean_object* v_snd_875_; lean_object* v_snd_876_; lean_object* v_fst_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_961_; 
v_snd_874_ = lean_ctor_get(v_b_865_, 1);
lean_inc(v_snd_874_);
v_snd_875_ = lean_ctor_get(v_snd_874_, 1);
lean_inc(v_snd_875_);
v_snd_876_ = lean_ctor_get(v_snd_875_, 1);
lean_inc(v_snd_876_);
v_fst_877_ = lean_ctor_get(v_b_865_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v_b_865_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v_b_865_, 1);
lean_dec(v_unused_962_);
v___x_879_ = v_b_865_;
v_isShared_880_ = v_isSharedCheck_961_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_fst_877_);
lean_dec(v_b_865_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_961_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_fst_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_959_; 
v_fst_881_ = lean_ctor_get(v_snd_874_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v_snd_874_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v_snd_874_, 1);
lean_dec(v_unused_960_);
v___x_883_ = v_snd_874_;
v_isShared_884_ = v_isSharedCheck_959_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_fst_881_);
lean_dec(v_snd_874_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_959_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_fst_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_957_; 
v_fst_885_ = lean_ctor_get(v_snd_875_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v_snd_875_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; 
v_unused_958_ = lean_ctor_get(v_snd_875_, 1);
lean_dec(v_unused_958_);
v___x_887_ = v_snd_875_;
v_isShared_888_ = v_isSharedCheck_957_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_fst_885_);
lean_dec(v_snd_875_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_957_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_array_889_; lean_object* v_start_890_; lean_object* v_stop_891_; uint8_t v___x_892_; 
v_array_889_ = lean_ctor_get(v_snd_876_, 0);
v_start_890_ = lean_ctor_get(v_snd_876_, 1);
v_stop_891_ = lean_ctor_get(v_snd_876_, 2);
v___x_892_ = lean_nat_dec_lt(v_start_890_, v_stop_891_);
if (v___x_892_ == 0)
{
lean_object* v___x_894_; 
if (v_isShared_888_ == 0)
{
v___x_894_ = v___x_887_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_fst_885_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_snd_876_);
v___x_894_ = v_reuseFailAlloc_902_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v___x_894_);
v___x_896_ = v___x_883_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_fst_881_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_894_);
v___x_896_ = v_reuseFailAlloc_901_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_898_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v___x_896_);
v___x_898_ = v___x_879_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_fst_877_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_896_);
v___x_898_ = v_reuseFailAlloc_900_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
}
else
{
lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_953_; 
lean_inc(v_stop_891_);
lean_inc(v_start_890_);
lean_inc_ref(v_array_889_);
v_isSharedCheck_953_ = !lean_is_exclusive(v_snd_876_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; 
v_unused_954_ = lean_ctor_get(v_snd_876_, 2);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_snd_876_, 1);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_snd_876_, 0);
lean_dec(v_unused_956_);
v___x_904_ = v_snd_876_;
v_isShared_905_ = v_isSharedCheck_953_;
goto v_resetjp_903_;
}
else
{
lean_dec(v_snd_876_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_953_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v_a_906_ = lean_array_uget_borrowed(v_as_862_, v_i_864_);
v___x_907_ = lean_array_fget(v_array_889_, v_start_890_);
v___x_908_ = lean_unsigned_to_nat(1u);
v___x_909_ = lean_nat_add(v_start_890_, v___x_908_);
lean_dec(v_start_890_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v___x_909_);
v___x_911_ = v___x_904_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_array_889_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_stop_891_);
v___x_911_ = v_reuseFailAlloc_952_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
uint8_t v___x_922_; 
v___x_922_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_fst_877_, v_a_906_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Json_getNat_x3f(v___x_907_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_dec_ref_known(v___x_923_, 1);
goto v___jp_912_;
}
else
{
lean_object* v_a_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
v___x_925_ = lean_array_get_size(v_a_859_);
v___x_926_ = lean_nat_dec_lt(v_a_906_, v___x_925_);
if (v___x_926_ == 0)
{
lean_dec(v_a_924_);
goto v___jp_912_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_array_fget_borrowed(v_a_859_, v_a_906_);
lean_inc(v___x_927_);
v___x_928_ = l_Lean_Json_getNat_x3f(v___x_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_dec_ref_known(v___x_928_, 1);
lean_dec(v_a_924_);
goto v___jp_912_;
}
else
{
lean_object* v_a_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = lean_array_get_size(v_a_860_);
v___x_931_ = lean_nat_dec_lt(v_a_929_, v___x_930_);
if (v___x_931_ == 0)
{
lean_dec(v_a_929_);
lean_dec(v_a_924_);
goto v___jp_912_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_array_fget_borrowed(v_a_860_, v_a_929_);
lean_dec(v_a_929_);
lean_inc(v___x_932_);
v___x_933_ = l_Lean_Json_getNat_x3f(v___x_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_dec_ref_known(v___x_933_, 1);
lean_dec(v_a_924_);
goto v___jp_912_;
}
else
{
lean_object* v_a_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
v___x_935_ = lean_array_get_size(v_a_861_);
v___x_936_ = lean_nat_dec_lt(v_a_934_, v___x_935_);
if (v___x_936_ == 0)
{
lean_dec(v_a_934_);
lean_dec(v_a_924_);
goto v___jp_912_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
lean_del_object(v___x_887_);
lean_del_object(v___x_883_);
lean_del_object(v___x_879_);
v___x_937_ = lean_box(0);
lean_inc_n(v_a_906_, 2);
v___x_938_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(v_fst_877_, v_a_906_, v___x_937_);
v___x_939_ = lean_unsigned_to_nat(2u);
v___x_940_ = lean_mk_empty_array_with_capacity(v___x_939_);
v___x_941_ = lean_array_push(v___x_940_, v_a_934_);
v___x_942_ = lean_array_push(v___x_941_, v_a_924_);
v___x_943_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(v___x_942_);
v___x_944_ = lean_array_push(v_fst_881_, v___x_943_);
v___x_945_ = lean_array_push(v_fst_885_, v_a_906_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_911_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_944_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_938_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v_a_868_ = v___x_948_;
goto v___jp_867_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec(v___x_907_);
lean_del_object(v___x_887_);
lean_del_object(v___x_883_);
lean_del_object(v___x_879_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_fst_885_);
lean_ctor_set(v___x_949_, 1, v___x_911_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v_fst_881_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v_fst_877_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v_a_868_ = v___x_951_;
goto v___jp_867_;
}
v___jp_912_:
{
lean_object* v___x_914_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v___x_911_);
v___x_914_ = v___x_887_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_fst_885_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v___x_911_);
v___x_914_ = v_reuseFailAlloc_921_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v___x_914_);
v___x_916_ = v___x_883_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_fst_881_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_914_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v___x_916_);
v___x_918_ = v___x_879_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_fst_877_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
v_a_868_ = v___x_918_;
goto v___jp_867_;
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
v___jp_867_:
{
size_t v___x_869_; size_t v___x_870_; 
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_add(v_i_864_, v___x_869_);
v_i_864_ = v___x_870_;
v_b_865_ = v_a_868_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_859_ = stack[0].m_obj;
lean_object* v_a_860_ = stack[1].m_obj;
lean_object* v_a_861_ = stack[2].m_obj;
lean_object* v_as_862_ = stack[3].m_obj;
size_t v_sz_863_ = stack[4].m_num;
size_t v_i_864_ = stack[5].m_num;
lean_object* v_b_865_ = stack[6].m_obj;
lean_object* v_res_963_;
v_res_963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(v_a_859_, v_a_860_, v_a_861_, v_as_862_, v_sz_863_, v_i_864_, v_b_865_);
stack->m_obj
 = v_res_963_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9___boxed(lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_as_967_, lean_object* v_sz_968_, lean_object* v_i_969_, lean_object* v_b_970_, lean_object* v___y_971_){
_start:
{
size_t v_sz_boxed_972_; size_t v_i_boxed_973_; lean_object* v_res_974_; 
v_sz_boxed_972_ = lean_unbox_usize(v_sz_968_);
lean_dec(v_sz_968_);
v_i_boxed_973_ = lean_unbox_usize(v_i_969_);
lean_dec(v_i_969_);
v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(v_a_964_, v_a_965_, v_a_966_, v_as_967_, v_sz_boxed_972_, v_i_boxed_973_, v_b_970_);
lean_dec_ref(v_as_967_);
lean_dec_ref(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec_ref(v_a_964_);
return v_res_974_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = lean_box(0);
v___x_985_ = lean_unsigned_to_nat(16u);
v___x_986_ = lean_mk_array(v___x_985_, v___x_984_);
return v___x_986_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__8);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___x_987_);
return v___x_989_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(lean_object* v_a_990_, lean_object* v_as_991_, size_t v_sz_992_, size_t v_i_993_, lean_object* v_b_994_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = lean_usize_dec_lt(v_i_993_, v_sz_992_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; 
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v_b_994_);
return v___x_997_;
}
else
{
lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1128_; 
v_fst_998_ = lean_ctor_get(v_b_994_, 0);
v_snd_999_ = lean_ctor_get(v_b_994_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_b_994_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1001_ = v_b_994_;
v_isShared_1002_ = v_isSharedCheck_1128_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snd_999_);
lean_inc(v_fst_998_);
lean_dec(v_b_994_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1128_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__0));
v_a_1005_ = lean_array_uget_borrowed(v_as_991_, v_i_993_);
v___x_1006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__1));
lean_inc(v_a_1005_);
v___x_1007_ = l_Lean_Json_getObjVal_x3f(v_a_1005_, v___x_1006_);
v___x_1008_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2));
lean_inc(v_a_1005_);
v___x_1011_ = l_Lean_Json_getObjVal_x3f(v_a_1005_, v___x_1010_);
v___x_1012_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1011_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__3));
lean_inc(v_a_1005_);
v___x_1015_ = l_Lean_Json_getObjVal_x3f(v_a_1005_, v___x_1014_);
v___x_1016_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1015_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v___x_1018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__4));
lean_inc(v_a_1009_);
v___x_1019_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_a_1009_, v___x_1018_);
v___x_1020_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1019_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__5));
v___x_1023_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_1009_, v___x_1022_);
v___x_1024_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1023_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___x_1026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__6));
v___x_1027_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_1013_, v___x_1026_);
v___x_1028_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1027_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v___x_1030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__7));
v___x_1031_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_a_1017_, v___x_1030_);
v___x_1032_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1031_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v___x_1034_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__9);
v___x_1035_ = lean_array_get_size(v_a_1025_);
v___x_1036_ = l_Array_toSubarray___redArg(v_a_1025_, v___x_1003_, v___x_1035_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 1, v___x_1036_);
lean_ctor_set(v___x_1001_, 0, v___x_1004_);
v___x_1038_ = v___x_1001_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; size_t v_sz_1041_; size_t v___x_1042_; lean_object* v___x_1043_; 
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1004_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1034_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v_sz_1041_ = lean_array_size(v_a_1021_);
v___x_1042_ = ((size_t)0ULL);
v___x_1043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__9(v_a_1029_, v_a_1033_, v_a_990_, v_a_1021_, v_sz_1041_, v___x_1042_, v___x_1040_);
lean_dec(v_a_1021_);
lean_dec(v_a_1033_);
lean_dec(v_a_1029_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v_snd_1045_; lean_object* v_snd_1046_; lean_object* v_fst_1047_; lean_object* v_fst_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1061_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v_snd_1045_ = lean_ctor_get(v_a_1044_, 1);
lean_inc(v_snd_1045_);
lean_dec(v_a_1044_);
v_snd_1046_ = lean_ctor_get(v_snd_1045_, 1);
lean_inc(v_snd_1046_);
v_fst_1047_ = lean_ctor_get(v_snd_1045_, 0);
lean_inc(v_fst_1047_);
lean_dec(v_snd_1045_);
v_fst_1048_ = lean_ctor_get(v_snd_1046_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_snd_1046_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_snd_1046_, 1);
lean_dec(v_unused_1062_);
v___x_1050_ = v_snd_1046_;
v_isShared_1051_ = v_isSharedCheck_1061_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_fst_1048_);
lean_dec(v_snd_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1061_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1052_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1052_, 0, v_fst_1047_);
v___x_1053_ = lean_array_push(v_fst_998_, v___x_1052_);
v___x_1054_ = lean_array_push(v_snd_999_, v_fst_1048_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1054_);
lean_ctor_set(v___x_1050_, 0, v___x_1053_);
v___x_1056_ = v___x_1050_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
size_t v___x_1057_; size_t v___x_1058_; 
v___x_1057_ = ((size_t)1ULL);
v___x_1058_ = lean_usize_add(v_i_993_, v___x_1057_);
v_i_993_ = v___x_1058_;
v_b_994_ = v___x_1056_;
goto _start;
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_snd_999_);
lean_dec(v_fst_998_);
v_a_1063_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1043_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1043_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
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
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec(v_a_1029_);
lean_dec(v_a_1025_);
lean_dec(v_a_1021_);
lean_del_object(v___x_1001_);
lean_dec(v_snd_999_);
lean_dec(v_fst_998_);
v_a_1072_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1032_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1032_);
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
lean_dec(v_a_1025_);
lean_dec(v_a_1021_);
lean_dec(v_a_1017_);
lean_del_object(v___x_1001_);
lean_dec(v_snd_999_);
lean_dec(v_fst_998_);
v_a_1080_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1028_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1028_);
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
lean_dec(v_a_1021_);
lean_dec(v_a_1017_);
lean_dec(v_a_1013_);
lean_del_object(v___x_1001_);
lean_dec(v_snd_999_);
lean_dec(v_fst_998_);
v_a_1088_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1024_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1024_);
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
lean_dec(v_a_1017_);
lean_dec(v_a_1013_);
lean_dec(v_a_1009_);
lean_del_object(v___x_1001_);
lean_dec(v_snd_999_);
lean_dec(v_fst_998_);
v_a_1096_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1020_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1020_);
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
lean_dec(v_a_1013_);
lean_dec(v_a_1009_);
lean_del_object(v___x_1001_);
lean_dec(v_snd_999_);
lean_dec(v_fst_998_);
v_a_1104_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1016_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1016_);
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
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v_a_1009_);
lean_del_object(v___x_1001_);
lean_dec(v_snd_999_);
lean_dec(v_fst_998_);
v_a_1112_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1012_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1012_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
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
lean_del_object(v___x_1001_);
lean_dec(v_snd_999_);
lean_dec(v_fst_998_);
v_a_1120_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1008_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1008_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_990_ = stack[0].m_obj;
lean_object* v_as_991_ = stack[1].m_obj;
size_t v_sz_992_ = stack[2].m_num;
size_t v_i_993_ = stack[3].m_num;
lean_object* v_b_994_ = stack[4].m_obj;
lean_object* v_res_1129_;
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(v_a_990_, v_as_991_, v_sz_992_, v_i_993_, v_b_994_);
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___boxed(lean_object* v_a_1130_, lean_object* v_as_1131_, lean_object* v_sz_1132_, lean_object* v_i_1133_, lean_object* v_b_1134_, lean_object* v___y_1135_){
_start:
{
size_t v_sz_boxed_1136_; size_t v_i_boxed_1137_; lean_object* v_res_1138_; 
v_sz_boxed_1136_ = lean_unbox_usize(v_sz_1132_);
lean_dec(v_sz_1132_);
v_i_boxed_1137_ = lean_unbox_usize(v_i_1133_);
lean_dec(v_i_1133_);
v_res_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(v_a_1130_, v_as_1131_, v_sz_boxed_1136_, v_i_boxed_1137_, v_b_1134_);
lean_dec_ref(v_as_1131_);
lean_dec_ref(v_a_1130_);
return v_res_1138_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(size_t v_sz_1139_, size_t v_i_1140_, lean_object* v_bs_1141_){
_start:
{
uint8_t v___x_1142_; 
v___x_1142_ = lean_usize_dec_lt(v_i_1140_, v_sz_1139_);
if (v___x_1142_ == 0)
{
return v_bs_1141_;
}
else
{
lean_object* v_v_1143_; lean_object* v___x_1144_; lean_object* v_bs_x27_1145_; lean_object* v___x_1146_; size_t v___x_1147_; size_t v___x_1148_; lean_object* v___x_1149_; 
v_v_1143_ = lean_array_uget(v_bs_1141_, v_i_1140_);
v___x_1144_ = lean_unsigned_to_nat(0u);
v_bs_x27_1145_ = lean_array_uset(v_bs_1141_, v_i_1140_, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_v_1143_);
v___x_1147_ = ((size_t)1ULL);
v___x_1148_ = lean_usize_add(v_i_1140_, v___x_1147_);
v___x_1149_ = lean_array_uset(v_bs_x27_1145_, v_i_1140_, v___x_1146_);
v_i_1140_ = v___x_1148_;
v_bs_1141_ = v___x_1149_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1139_ = stack[0].m_num;
size_t v_i_1140_ = stack[1].m_num;
lean_object* v_bs_1141_ = stack[2].m_obj;
lean_object* v_res_1151_;
v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(v_sz_1139_, v_i_1140_, v_bs_1141_);
stack->m_obj
 = v_res_1151_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2___boxed(lean_object* v_sz_1152_, lean_object* v_i_1153_, lean_object* v_bs_1154_){
_start:
{
size_t v_sz_boxed_1155_; size_t v_i_boxed_1156_; lean_object* v_res_1157_; 
v_sz_boxed_1155_ = lean_unbox_usize(v_sz_1152_);
lean_dec(v_sz_1152_);
v_i_boxed_1156_ = lean_unbox_usize(v_i_1153_);
lean_dec(v_i_1153_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(v_sz_boxed_1155_, v_i_boxed_1156_, v_bs_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(lean_object* v_a_1158_){
_start:
{
size_t v_sz_1159_; size_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_sz_1159_ = lean_array_size(v_a_1158_);
v___x_1160_ = ((size_t)0ULL);
v___x_1161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2_spec__2(v_sz_1159_, v___x_1160_, v_a_1158_);
v___x_1162_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(size_t v_sz_1165_, size_t v_i_1166_, lean_object* v_bs_1167_){
_start:
{
uint8_t v___x_1169_; 
v___x_1169_ = lean_usize_dec_lt(v_i_1166_, v_sz_1165_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v_bs_1167_);
return v___x_1170_;
}
else
{
lean_object* v_v_1171_; lean_object* v___x_1172_; lean_object* v_bs_x27_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_v_1171_ = lean_array_uget(v_bs_1167_, v_i_1166_);
v___x_1172_ = lean_unsigned_to_nat(0u);
v_bs_x27_1173_ = lean_array_uset(v_bs_1167_, v_i_1166_, v___x_1172_);
v___x_1174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__0));
lean_inc(v_v_1171_);
v___x_1175_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_v_1171_, v___x_1174_);
v___x_1176_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1175_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___closed__1));
v___x_1179_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v_v_1171_, v___x_1178_);
v___x_1180_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1179_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = lean_unsigned_to_nat(2u);
v___x_1183_ = lean_mk_empty_array_with_capacity(v___x_1182_);
v___x_1184_ = lean_array_push(v___x_1183_, v_a_1177_);
v___x_1185_ = lean_array_push(v___x_1184_, v_a_1181_);
v___x_1186_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(v___x_1185_);
v___x_1187_ = ((size_t)1ULL);
v___x_1188_ = lean_usize_add(v_i_1166_, v___x_1187_);
v___x_1189_ = lean_array_uset(v_bs_x27_1173_, v_i_1166_, v___x_1186_);
v_i_1166_ = v___x_1188_;
v_bs_1167_ = v___x_1189_;
goto _start;
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_a_1177_);
lean_dec_ref(v_bs_x27_1173_);
v_a_1191_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1180_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1180_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v_bs_x27_1173_);
lean_dec(v_v_1171_);
v_a_1199_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1176_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1176_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1165_ = stack[0].m_num;
size_t v_i_1166_ = stack[1].m_num;
lean_object* v_bs_1167_ = stack[2].m_obj;
lean_object* v_res_1207_;
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(v_sz_1165_, v_i_1166_, v_bs_1167_);
stack->m_obj
 = v_res_1207_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4___boxed(lean_object* v_sz_1208_, lean_object* v_i_1209_, lean_object* v_bs_1210_, lean_object* v___y_1211_){
_start:
{
size_t v_sz_boxed_1212_; size_t v_i_boxed_1213_; lean_object* v_res_1214_; 
v_sz_boxed_1212_ = lean_unbox_usize(v_sz_1208_);
lean_dec(v_sz_1208_);
v_i_boxed_1213_ = lean_unbox_usize(v_i_1209_);
lean_dec(v_i_1209_);
v_res_1214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(v_sz_boxed_1212_, v_i_boxed_1213_, v_bs_1210_);
return v_res_1214_;
}
}
lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(lean_object* v_profile_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__0));
lean_inc(v_profile_1221_);
v___x_1224_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1221_, v___x_1223_);
v___x_1225_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1224_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; size_t v_sz_1227_; size_t v___x_1228_; lean_object* v___x_1229_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc_n(v_a_1226_, 2);
lean_dec_ref_known(v___x_1225_, 1);
v_sz_1227_ = lean_array_size(v_a_1226_);
v___x_1228_ = ((size_t)0ULL);
v___x_1229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__4(v_sz_1227_, v___x_1228_, v_a_1226_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v___x_1231_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1));
v___x_1232_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1221_, v___x_1231_);
v___x_1233_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1232_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1235_; size_t v_sz_1236_; lean_object* v___x_1237_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1233_, 1);
v___x_1235_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__2));
v_sz_1236_ = lean_array_size(v_a_1234_);
v___x_1237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10(v_a_1226_, v_a_1234_, v_sz_1236_, v___x_1228_, v___x_1235_);
lean_dec(v_a_1234_);
lean_dec(v_a_1226_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1264_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1264_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1264_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v_fst_1242_; lean_object* v_snd_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1263_; 
v_fst_1242_ = lean_ctor_get(v_a_1238_, 0);
v_snd_1243_ = lean_ctor_get(v_a_1238_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_a_1238_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1245_ = v_a_1238_;
v_isShared_1246_ = v_isSharedCheck_1263_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_snd_1243_);
lean_inc(v_fst_1242_);
lean_dec(v_a_1238_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1263_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1247_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__3));
v___x_1248_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_a_1230_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1248_);
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1250_ = v___x_1245_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1251_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4));
v___x_1252_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1252_, 0, v_fst_1242_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = lean_box(0);
v___x_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1253_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1250_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = l_Lean_Json_mkObj(v___x_1256_);
lean_dec_ref_known(v___x_1256_, 2);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_snd_1243_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1258_);
v___x_1260_ = v___x_1240_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_a_1230_);
v_a_1265_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1237_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1237_);
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
lean_dec(v_a_1230_);
lean_dec(v_a_1226_);
v_a_1273_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1233_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1233_);
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
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_a_1226_);
lean_dec(v_profile_1221_);
v_a_1281_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1229_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1229_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v_profile_1221_);
v_a_1289_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1225_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1225_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_profile_1221_ = stack[0].m_obj;
lean_object* v_res_1297_;
v_res_1297_ = l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(v_profile_1221_);
stack->m_obj
 = v_res_1297_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___boxed(lean_object* v_profile_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(v_profile_1298_);
return v_res_1300_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(lean_object* v_00_u03b2_1301_, lean_object* v_m_1302_, lean_object* v_a_1303_){
_start:
{
uint8_t v___x_1304_; 
v___x_1304_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___redArg(v_m_1302_, v_a_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1302_ = stack[1].m_obj;
lean_object* v_a_1303_ = stack[2].m_obj;
uint8_t v_res_1305_;
v_res_1305_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(lean_box(0), v_m_1302_, v_a_1303_);
stack->m_num = v_res_1305_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6___boxed(lean_object* v_00_u03b2_1306_, lean_object* v_m_1307_, lean_object* v_a_1308_){
_start:
{
uint8_t v_res_1309_; lean_object* v_r_1310_; 
v_res_1309_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6(v_00_u03b2_1306_, v_m_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_m_1307_);
v_r_1310_ = lean_box(v_res_1309_);
return v_r_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7(lean_object* v_00_u03b2_1311_, lean_object* v_m_1312_, lean_object* v_a_1313_, lean_object* v_b_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7___redArg(v_m_1312_, v_a_1313_, v_b_1314_);
return v___x_1315_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(lean_object* v_00_u03b2_1316_, lean_object* v_a_1317_, lean_object* v_x_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___redArg(v_a_1317_, v_x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1317_ = stack[1].m_obj;
lean_object* v_x_1318_ = stack[2].m_obj;
uint8_t v_res_1320_;
v_res_1320_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(lean_box(0), v_a_1317_, v_x_1318_);
stack->m_num = v_res_1320_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1321_, lean_object* v_a_1322_, lean_object* v_x_1323_){
_start:
{
uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_res_1324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__6_spec__9(v_00_u03b2_1321_, v_a_1322_, v_x_1323_);
lean_dec(v_x_1323_);
lean_dec(v_a_1322_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11(lean_object* v_00_u03b2_1326_, lean_object* v_data_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11___redArg(v_data_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14(lean_object* v_00_u03b2_1329_, lean_object* v_i_1330_, lean_object* v_source_1331_, lean_object* v_target_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14___redArg(v_i_1330_, v_source_1331_, v_target_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18(lean_object* v_00_u03b2_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__7_spec__11_spec__14_spec__18___redArg(v_x_1335_, v_x_1336_);
return v___x_1337_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_bs_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1342_, 0, v_bs_1340_);
return v___x_1342_;
}
else
{
lean_object* v_v_1343_; lean_object* v___x_1344_; 
v_v_1343_ = lean_array_uget_borrowed(v_bs_1340_, v_i_1339_);
lean_inc(v_v_1343_);
v___x_1344_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4(v_v_1343_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_bs_1340_);
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1354_; lean_object* v_bs_x27_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v_a_1353_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1354_ = lean_unsigned_to_nat(0u);
v_bs_x27_1355_ = lean_array_uset(v_bs_1340_, v_i_1339_, v___x_1354_);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_add(v_i_1339_, v___x_1356_);
v___x_1358_ = lean_array_uset(v_bs_x27_1355_, v_i_1339_, v_a_1353_);
v_i_1339_ = v___x_1357_;
v_bs_1340_ = v___x_1358_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1338_ = stack[0].m_num;
size_t v_i_1339_ = stack[1].m_num;
lean_object* v_bs_1340_ = stack[2].m_obj;
lean_object* v_res_1360_;
v_res_1360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(v_sz_1338_, v_i_1339_, v_bs_1340_);
stack->m_obj
 = v_res_1360_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_1361_, lean_object* v_i_1362_, lean_object* v_bs_1363_){
_start:
{
size_t v_sz_boxed_1364_; size_t v_i_boxed_1365_; lean_object* v_res_1366_; 
v_sz_boxed_1364_ = lean_unbox_usize(v_sz_1361_);
lean_dec(v_sz_1361_);
v_i_boxed_1365_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_res_1366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(v_sz_boxed_1364_, v_i_boxed_1365_, v_bs_1363_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0(lean_object* v_x_1367_){
_start:
{
if (lean_obj_tag(v_x_1367_) == 4)
{
lean_object* v_elems_1368_; size_t v_sz_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v_elems_1368_ = lean_ctor_get(v_x_1367_, 0);
lean_inc_ref(v_elems_1368_);
lean_dec_ref_known(v_x_1367_, 1);
v_sz_1369_ = lean_array_size(v_elems_1368_);
v___x_1370_ = ((size_t)0ULL);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0_spec__1(v_sz_1369_, v___x_1370_, v_elems_1368_);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1372_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_1373_ = lean_unsigned_to_nat(80u);
v___x_1374_ = l_Lean_Json_pretty(v_x_1367_, v___x_1373_);
v___x_1375_ = lean_string_append(v___x_1372_, v___x_1374_);
lean_dec_ref(v___x_1374_);
v___x_1376_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(lean_object* v_j_1379_, lean_object* v_k_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = l_Lean_Json_getObjValD(v_j_1379_, v_k_1380_);
v___x_1382_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0_spec__0(v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0___boxed(lean_object* v_j_1383_, lean_object* v_k_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(v_j_1383_, v_k_1384_);
lean_dec_ref(v_k_1384_);
return v_res_1385_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(size_t v_sz_1386_, size_t v_i_1387_, lean_object* v_bs_1388_){
_start:
{
uint8_t v___x_1389_; 
v___x_1389_ = lean_usize_dec_lt(v_i_1387_, v_sz_1386_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1390_, 0, v_bs_1388_);
return v___x_1390_;
}
else
{
lean_object* v_v_1391_; lean_object* v___x_1392_; 
v_v_1391_ = lean_array_uget_borrowed(v_bs_1388_, v_i_1387_);
lean_inc(v_v_1391_);
v___x_1392_ = l_Lean_Json_getStr_x3f(v_v_1391_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v_bs_1388_);
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1392_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1392_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1402_; lean_object* v_bs_x27_1403_; size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v_a_1401_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1402_ = lean_unsigned_to_nat(0u);
v_bs_x27_1403_ = lean_array_uset(v_bs_1388_, v_i_1387_, v___x_1402_);
v___x_1404_ = ((size_t)1ULL);
v___x_1405_ = lean_usize_add(v_i_1387_, v___x_1404_);
v___x_1406_ = lean_array_uset(v_bs_x27_1403_, v_i_1387_, v_a_1401_);
v_i_1387_ = v___x_1405_;
v_bs_1388_ = v___x_1406_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1386_ = stack[0].m_num;
size_t v_i_1387_ = stack[1].m_num;
lean_object* v_bs_1388_ = stack[2].m_obj;
lean_object* v_res_1408_;
v_res_1408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(v_sz_1386_, v_i_1387_, v_bs_1388_);
stack->m_obj
 = v_res_1408_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_1409_, lean_object* v_i_1410_, lean_object* v_bs_1411_){
_start:
{
size_t v_sz_boxed_1412_; size_t v_i_boxed_1413_; lean_object* v_res_1414_; 
v_sz_boxed_1412_ = lean_unbox_usize(v_sz_1409_);
lean_dec(v_sz_1409_);
v_i_boxed_1413_ = lean_unbox_usize(v_i_1410_);
lean_dec(v_i_1410_);
v_res_1414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(v_sz_boxed_1412_, v_i_boxed_1413_, v_bs_1411_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2(lean_object* v_x_1415_){
_start:
{
if (lean_obj_tag(v_x_1415_) == 4)
{
lean_object* v_elems_1416_; size_t v_sz_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v_elems_1416_ = lean_ctor_get(v_x_1415_, 0);
lean_inc_ref(v_elems_1416_);
lean_dec_ref_known(v_x_1415_, 1);
v_sz_1417_ = lean_array_size(v_elems_1416_);
v___x_1418_ = ((size_t)0ULL);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2_spec__4(v_sz_1417_, v___x_1418_, v_elems_1416_);
return v___x_1419_;
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1420_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3_spec__4___closed__0));
v___x_1421_ = lean_unsigned_to_nat(80u);
v___x_1422_ = l_Lean_Json_pretty(v_x_1415_, v___x_1421_);
v___x_1423_ = lean_string_append(v___x_1420_, v___x_1422_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__6));
v___x_1425_ = lean_string_append(v___x_1423_, v___x_1424_);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(lean_object* v_j_1427_, lean_object* v_k_1428_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = l_Lean_Json_getObjValD(v_j_1427_, v_k_1428_);
v___x_1430_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1_spec__2(v___x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1___boxed(lean_object* v_j_1431_, lean_object* v_k_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(v_j_1431_, v_k_1432_);
lean_dec_ref(v_k_1432_);
return v_res_1433_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(lean_object* v_as_1435_, size_t v_sz_1436_, size_t v_i_1437_, lean_object* v_b_1438_){
_start:
{
lean_object* v_a_1441_; uint8_t v___x_1445_; 
v___x_1445_ = lean_usize_dec_lt(v_i_1437_, v_sz_1436_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_b_1438_);
return v___x_1446_;
}
else
{
lean_object* v_snd_1447_; lean_object* v_snd_1448_; lean_object* v_fst_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1509_; 
v_snd_1447_ = lean_ctor_get(v_b_1438_, 1);
lean_inc(v_snd_1447_);
v_snd_1448_ = lean_ctor_get(v_snd_1447_, 1);
lean_inc(v_snd_1448_);
v_fst_1449_ = lean_ctor_get(v_b_1438_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_b_1438_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v_b_1438_, 1);
lean_dec(v_unused_1510_);
v___x_1451_ = v_b_1438_;
v_isShared_1452_ = v_isSharedCheck_1509_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_fst_1449_);
lean_dec(v_b_1438_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1509_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_fst_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1507_; 
v_fst_1453_ = lean_ctor_get(v_snd_1447_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_snd_1447_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v_snd_1447_, 1);
lean_dec(v_unused_1508_);
v___x_1455_ = v_snd_1447_;
v_isShared_1456_ = v_isSharedCheck_1507_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_fst_1453_);
lean_dec(v_snd_1447_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1507_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v_array_1457_; lean_object* v_start_1458_; lean_object* v_stop_1459_; uint8_t v___x_1460_; 
v_array_1457_ = lean_ctor_get(v_snd_1448_, 0);
v_start_1458_ = lean_ctor_get(v_snd_1448_, 1);
v_stop_1459_ = lean_ctor_get(v_snd_1448_, 2);
v___x_1460_ = lean_nat_dec_lt(v_start_1458_, v_stop_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1462_; 
if (v_isShared_1456_ == 0)
{
v___x_1462_ = v___x_1455_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_fst_1453_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_snd_1448_);
v___x_1462_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1462_);
v___x_1464_ = v___x_1451_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_fst_1449_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
}
}
else
{
lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1503_; 
lean_inc(v_stop_1459_);
lean_inc(v_start_1458_);
lean_inc_ref(v_array_1457_);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_snd_1448_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; 
v_unused_1504_ = lean_ctor_get(v_snd_1448_, 2);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_snd_1448_, 1);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_snd_1448_, 0);
lean_dec(v_unused_1506_);
v___x_1469_ = v_snd_1448_;
v_isShared_1470_ = v_isSharedCheck_1503_;
goto v_resetjp_1468_;
}
else
{
lean_dec(v_snd_1448_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1503_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v_a_1471_ = lean_array_uget_borrowed(v_as_1435_, v_i_1437_);
v___x_1472_ = lean_array_fget(v_array_1457_, v_start_1458_);
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v_start_1458_, v___x_1473_);
lean_dec(v_start_1458_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___x_1474_);
v___x_1476_ = v___x_1469_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_array_1457_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_stop_1459_);
v___x_1476_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___y_1478_; lean_object* v___y_1489_; lean_object* v___x_1499_; 
lean_inc(v___x_1472_);
v___x_1499_ = l_Lean_Json_getStr_x3f(v___x_1472_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec_ref_known(v___x_1499_, 1);
v___x_1500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___closed__0));
v___x_1501_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__0(v___x_1472_, v___x_1500_);
v___y_1489_ = v___x_1501_;
goto v___jp_1488_;
}
else
{
lean_dec(v___x_1472_);
v___y_1489_ = v___x_1499_;
goto v___jp_1488_;
}
v___jp_1477_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1479_ = lean_array_get_size(v_fst_1453_);
v___x_1480_ = lean_array_fset(v_fst_1449_, v_a_1471_, v___x_1479_);
v___x_1481_ = lean_array_push(v_fst_1453_, v___y_1478_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v___x_1476_);
lean_ctor_set(v___x_1455_, 0, v___x_1481_);
v___x_1483_ = v___x_1455_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1476_);
v___x_1483_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1483_);
lean_ctor_set(v___x_1451_, 0, v___x_1480_);
v___x_1485_ = v___x_1451_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
v_a_1441_ = v___x_1485_;
goto v___jp_1440_;
}
}
}
v___jp_1488_:
{
if (lean_obj_tag(v___y_1489_) == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec_ref_known(v___y_1489_, 1);
lean_del_object(v___x_1455_);
lean_del_object(v___x_1451_);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_fst_1453_);
lean_ctor_set(v___x_1490_, 1, v___x_1476_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_fst_1449_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v_a_1441_ = v___x_1491_;
goto v___jp_1440_;
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v_a_1492_ = lean_ctor_get(v___y_1489_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___y_1489_, 1);
v___x_1493_ = lean_array_get_size(v_fst_1449_);
v___x_1494_ = lean_nat_dec_lt(v_a_1471_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec(v_a_1492_);
lean_del_object(v___x_1455_);
lean_del_object(v___x_1451_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_fst_1453_);
lean_ctor_set(v___x_1495_, 1, v___x_1476_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v_fst_1449_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v_a_1441_ = v___x_1496_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1497_; 
lean_inc(v_a_1492_);
v___x_1497_ = l_Lean_Name_Demangle_demangleSymbol(v_a_1492_);
if (lean_obj_tag(v___x_1497_) == 0)
{
v___y_1478_ = v_a_1492_;
goto v___jp_1477_;
}
else
{
lean_object* v_val_1498_; 
lean_dec(v_a_1492_);
v_val_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___y_1478_ = v_val_1498_;
goto v___jp_1477_;
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
v___jp_1440_:
{
size_t v___x_1442_; size_t v___x_1443_; 
v___x_1442_ = ((size_t)1ULL);
v___x_1443_ = lean_usize_add(v_i_1437_, v___x_1442_);
v_i_1437_ = v___x_1443_;
v_b_1438_ = v_a_1441_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1435_ = stack[0].m_obj;
size_t v_sz_1436_ = stack[1].m_num;
size_t v_i_1437_ = stack[2].m_num;
lean_object* v_b_1438_ = stack[3].m_obj;
lean_object* v_res_1511_;
v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(v_as_1435_, v_sz_1436_, v_i_1437_, v_b_1438_);
stack->m_obj
 = v_res_1511_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2___boxed(lean_object* v_as_1512_, lean_object* v_sz_1513_, lean_object* v_i_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_){
_start:
{
size_t v_sz_boxed_1517_; size_t v_i_boxed_1518_; lean_object* v_res_1519_; 
v_sz_boxed_1517_ = lean_unbox_usize(v_sz_1513_);
lean_dec(v_sz_1513_);
v_i_boxed_1518_ = lean_unbox_usize(v_i_1514_);
lean_dec(v_i_1514_);
v_res_1519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(v_as_1512_, v_sz_boxed_1517_, v_i_boxed_1518_, v_b_1515_);
lean_dec_ref(v_as_1512_);
return v_res_1519_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Array_instInhabited___redArg();
return v___x_1520_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__1));
v___x_1523_ = lean_mk_io_user_error(v___x_1522_);
return v___x_1523_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(lean_object* v_a_1526_, lean_object* v_funcMaps_1527_, size_t v_sz_1528_, size_t v_i_1529_, lean_object* v_bs_1530_){
_start:
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_usize_dec_lt(v_i_1529_, v_sz_1528_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v_bs_1530_);
return v___x_1533_;
}
else
{
lean_object* v___x_1534_; lean_object* v_v_1535_; lean_object* v___x_1536_; lean_object* v_bs_x27_1537_; lean_object* v_a_1539_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__0);
v_v_1535_ = lean_array_uget(v_bs_1530_, v_i_1529_);
v___x_1536_ = lean_unsigned_to_nat(0u);
v_bs_x27_1537_ = lean_array_uset(v_bs_1530_, v_i_1529_, v___x_1536_);
v___x_1544_ = lean_usize_to_nat(v_i_1529_);
v___x_1545_ = lean_array_get_borrowed(v___x_1534_, v_a_1526_, v___x_1544_);
v___x_1546_ = lean_array_get_borrowed(v___x_1534_, v_funcMaps_1527_, v___x_1544_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_array_get_size(v___x_1545_);
v___x_1548_ = lean_array_get_size(v___x_1546_);
v___x_1549_ = lean_nat_dec_eq(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref(v_bs_x27_1537_);
lean_dec(v_v_1535_);
v___x_1550_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__2);
v___x_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__10___closed__2));
lean_inc(v_v_1535_);
v___x_1553_ = l_Lean_Json_getObjVal_x3f(v_v_1535_, v___x_1552_);
v___x_1554_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc_n(v_a_1555_, 2);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__3));
v___x_1557_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__5(v_a_1555_, v___x_1556_);
v___x_1558_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___closed__4));
lean_inc(v_v_1535_);
v___x_1561_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__1(v_v_1535_, v___x_1560_);
v___x_1562_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1561_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; size_t v_sz_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
lean_inc(v___x_1545_);
v___x_1564_ = l_Array_toSubarray___redArg(v___x_1545_, v___x_1536_, v___x_1547_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_a_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v_a_1559_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v_sz_1567_ = lean_array_size(v___x_1546_);
v___x_1568_ = ((size_t)0ULL);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__2(v___x_1546_, v_sz_1567_, v___x_1568_, v___x_1566_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v_snd_1571_; lean_object* v_fst_1572_; lean_object* v_fst_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v_snd_1571_ = lean_ctor_get(v_a_1570_, 1);
lean_inc(v_snd_1571_);
v_fst_1572_ = lean_ctor_get(v_a_1570_, 0);
lean_inc(v_fst_1572_);
lean_dec(v_a_1570_);
v_fst_1573_ = lean_ctor_get(v_snd_1571_, 0);
lean_inc(v_fst_1573_);
lean_dec(v_snd_1571_);
v___x_1574_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__8(v_fst_1572_);
v___x_1575_ = l_Lean_Json_setObjVal_x21(v_a_1555_, v___x_1556_, v___x_1574_);
v___x_1576_ = l_Lean_Json_setObjVal_x21(v_v_1535_, v___x_1552_, v___x_1575_);
v___x_1577_ = l_Lean_Array_toJson___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__2(v_fst_1573_);
v___x_1578_ = l_Lean_Json_setObjVal_x21(v___x_1576_, v___x_1560_, v___x_1577_);
v_a_1539_ = v___x_1578_;
goto v___jp_1538_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_a_1555_);
lean_dec_ref(v_bs_x27_1537_);
lean_dec(v_v_1535_);
v_a_1579_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1569_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1569_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v_a_1559_);
lean_dec(v_a_1555_);
lean_dec_ref(v_bs_x27_1537_);
lean_dec(v_v_1535_);
v_a_1587_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1562_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1562_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_a_1555_);
lean_dec_ref(v_bs_x27_1537_);
lean_dec(v_v_1535_);
v_a_1595_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1558_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1558_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_dec(v_v_1535_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1603_; 
v_a_1603_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1554_, 1);
v_a_1539_ = v_a_1603_;
goto v___jp_1538_;
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec_ref(v_bs_x27_1537_);
v_a_1604_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1554_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1554_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
v___jp_1538_:
{
size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = ((size_t)1ULL);
v___x_1541_ = lean_usize_add(v_i_1529_, v___x_1540_);
v___x_1542_ = lean_array_uset(v_bs_x27_1537_, v_i_1529_, v_a_1539_);
v_i_1529_ = v___x_1541_;
v_bs_1530_ = v___x_1542_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1526_ = stack[0].m_obj;
lean_object* v_funcMaps_1527_ = stack[1].m_obj;
size_t v_sz_1528_ = stack[2].m_num;
size_t v_i_1529_ = stack[3].m_num;
lean_object* v_bs_1530_ = stack[4].m_obj;
lean_object* v_res_1612_;
v_res_1612_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1526_, v_funcMaps_1527_, v_sz_1528_, v_i_1529_, v_bs_1530_);
stack->m_obj
 = v_res_1612_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg___boxed(lean_object* v_a_1613_, lean_object* v_funcMaps_1614_, lean_object* v_sz_1615_, lean_object* v_i_1616_, lean_object* v_bs_1617_, lean_object* v___y_1618_){
_start:
{
size_t v_sz_boxed_1619_; size_t v_i_boxed_1620_; lean_object* v_res_1621_; 
v_sz_boxed_1619_ = lean_unbox_usize(v_sz_1615_);
lean_dec(v_sz_1615_);
v_i_boxed_1620_ = lean_unbox_usize(v_i_1616_);
lean_dec(v_i_1616_);
v_res_1621_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1613_, v_funcMaps_1614_, v_sz_boxed_1619_, v_i_boxed_1620_, v_bs_1617_);
lean_dec_ref(v_funcMaps_1614_);
lean_dec_ref(v_a_1613_);
return v_res_1621_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__1));
v___x_1625_ = lean_mk_io_user_error(v___x_1624_);
return v___x_1625_;
}
}
static lean_object* _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__3));
v___x_1628_ = lean_mk_io_user_error(v___x_1627_);
return v___x_1628_;
}
}
lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(lean_object* v_profile_1631_, lean_object* v_response_1632_, lean_object* v_funcMaps_1633_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__0));
v___x_1636_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_response_1632_, v___x_1635_);
v___x_1637_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1636_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1717_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1717_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1717_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1642_ = lean_unsigned_to_nat(0u);
v___x_1643_ = lean_array_get_size(v_a_1638_);
v___x_1644_ = lean_nat_dec_lt(v___x_1642_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
lean_dec(v_a_1638_);
lean_dec(v_profile_1631_);
v___x_1645_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2, &l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__2);
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
lean_ctor_set(v___x_1640_, 0, v___x_1645_);
v___x_1647_ = v___x_1640_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_del_object(v___x_1640_);
v___x_1649_ = lean_array_fget(v_a_1638_, v___x_1642_);
lean_dec(v_a_1638_);
v___x_1650_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__4));
v___x_1651_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__0(v___x_1649_, v___x_1650_);
v___x_1652_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1651_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest___closed__1));
lean_inc(v_profile_1631_);
v___x_1655_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__3(v_profile_1631_, v___x_1654_);
v___x_1656_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1655_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1700_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1700_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1700_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1666_ = lean_array_get_size(v_a_1653_);
v___x_1667_ = lean_array_get_size(v_a_1657_);
v___x_1668_ = lean_nat_dec_eq(v___x_1666_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_dec(v_a_1657_);
lean_dec(v_a_1653_);
lean_dec(v_profile_1631_);
goto v___jp_1661_;
}
else
{
lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = lean_array_get_size(v_funcMaps_1633_);
v___x_1670_ = lean_nat_dec_eq(v___x_1669_, v___x_1667_);
if (v___x_1670_ == 0)
{
lean_dec(v_a_1657_);
lean_dec(v_a_1653_);
lean_dec(v_profile_1631_);
goto v___jp_1661_;
}
else
{
size_t v_sz_1671_; size_t v___x_1672_; lean_object* v___x_1673_; 
lean_del_object(v___x_1659_);
v_sz_1671_ = lean_array_size(v_a_1657_);
v___x_1672_ = ((size_t)0ULL);
v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1653_, v_funcMaps_1633_, v_sz_1671_, v___x_1672_, v_a_1657_);
lean_dec(v_a_1653_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v___x_1675_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__5));
lean_inc(v_profile_1631_);
v___x_1676_ = l_Lean_Json_getObjVal_x3f(v_profile_1631_, v___x_1675_);
v___x_1677_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_1676_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1691_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1691_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1691_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1682_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_a_1674_);
v___x_1683_ = l_Lean_Json_setObjVal_x21(v_profile_1631_, v___x_1654_, v___x_1682_);
v___x_1684_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__6));
v___x_1685_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1685_, 0, v___x_1670_);
v___x_1686_ = l_Lean_Json_setObjVal_x21(v_a_1678_, v___x_1684_, v___x_1685_);
v___x_1687_ = l_Lean_Json_setObjVal_x21(v___x_1683_, v___x_1675_, v___x_1686_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1687_);
v___x_1689_ = v___x_1680_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
else
{
lean_dec(v_a_1674_);
lean_dec(v_profile_1631_);
return v___x_1677_;
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_profile_1631_);
v_a_1692_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1673_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1673_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
v___jp_1661_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4, &l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___closed__4);
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 1);
lean_ctor_set(v___x_1659_, 0, v___x_1662_);
v___x_1664_ = v___x_1659_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_a_1653_);
lean_dec(v_profile_1631_);
v_a_1701_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1656_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1656_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_profile_1631_);
v_a_1709_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1652_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1652_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_profile_1631_);
v_a_1718_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1637_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1637_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_0interp(lean_interpreter_value* stack)
{
lean_object* v_profile_1631_ = stack[0].m_obj;
lean_object* v_response_1632_ = stack[1].m_obj;
lean_object* v_funcMaps_1633_ = stack[2].m_obj;
lean_object* v_res_1726_;
v_res_1726_ = l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(v_profile_1631_, v_response_1632_, v_funcMaps_1633_);
stack->m_obj
 = v_res_1726_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols___boxed(lean_object* v_profile_1727_, lean_object* v_response_1728_, lean_object* v_funcMaps_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(v_profile_1727_, v_response_1728_, v_funcMaps_1729_);
lean_dec_ref(v_funcMaps_1729_);
return v_res_1731_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(lean_object* v_a_1732_, lean_object* v_funcMaps_1733_, lean_object* v_as_1734_, size_t v_sz_1735_, size_t v_i_1736_, lean_object* v_bs_1737_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___redArg(v_a_1732_, v_funcMaps_1733_, v_sz_1735_, v_i_1736_, v_bs_1737_);
return v___x_1739_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1732_ = stack[0].m_obj;
lean_object* v_funcMaps_1733_ = stack[1].m_obj;
lean_object* v_as_1734_ = stack[2].m_obj;
size_t v_sz_1735_ = stack[3].m_num;
size_t v_i_1736_ = stack[4].m_num;
lean_object* v_bs_1737_ = stack[5].m_obj;
lean_object* v_res_1740_;
v_res_1740_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(v_a_1732_, v_funcMaps_1733_, v_as_1734_, v_sz_1735_, v_i_1736_, v_bs_1737_);
stack->m_obj
 = v_res_1740_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3___boxed(lean_object* v_a_1741_, lean_object* v_funcMaps_1742_, lean_object* v_as_1743_, lean_object* v_sz_1744_, lean_object* v_i_1745_, lean_object* v_bs_1746_, lean_object* v___y_1747_){
_start:
{
size_t v_sz_boxed_1748_; size_t v_i_boxed_1749_; lean_object* v_res_1750_; 
v_sz_boxed_1748_ = lean_unbox_usize(v_sz_1744_);
lean_dec(v_sz_1744_);
v_i_boxed_1749_ = lean_unbox_usize(v_i_1745_);
lean_dec(v_i_1745_);
v_res_1750_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lake_CLI_Samply_0__Lake_Samply_applySymbols_spec__3(v_a_1741_, v_funcMaps_1742_, v_as_1743_, v_sz_boxed_1748_, v_i_boxed_1749_, v_bs_1746_);
lean_dec_ref(v_as_1743_);
lean_dec_ref(v_funcMaps_1742_);
lean_dec_ref(v_a_1741_);
return v_res_1750_;
}
}
lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(lean_object* v_cfg_1751_, lean_object* v_proc_1752_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_io_process_child_kill(v_cfg_1751_, v_proc_1752_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v___x_1758_; 
lean_dec_ref_known(v___x_1757_, 1);
v___x_1758_ = lean_io_process_child_wait(v_cfg_1751_, v_proc_1752_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1766_; 
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v___x_1758_, 0);
lean_dec(v_unused_1767_);
v___x_1760_ = v___x_1758_;
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v___x_1758_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = lean_box(0);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
lean_dec_ref_known(v___x_1758_, 1);
goto v___jp_1754_;
}
}
else
{
if (lean_obj_tag(v___x_1757_) == 0)
{
return v___x_1757_;
}
else
{
lean_dec_ref_known(v___x_1757_, 1);
goto v___jp_1754_;
}
}
v___jp_1754_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
}
}
LEAN_EXPORT void l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1751_ = stack[0].m_obj;
lean_object* v_proc_1752_ = stack[1].m_obj;
lean_object* v_res_1768_;
v_res_1768_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v_cfg_1751_, v_proc_1752_);
stack->m_obj
 = v_res_1768_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe___boxed(lean_object* v_cfg_1769_, lean_object* v_proc_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v_cfg_1769_, v_proc_1770_);
lean_dec_ref(v_proc_1770_);
lean_dec_ref(v_cfg_1769_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(lean_object* v_as_1774_, lean_object* v_j_1775_){
_start:
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_array_get_size(v_as_1774_);
v___x_1777_ = lean_nat_dec_lt(v_j_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_dec(v_j_1775_);
v___x_1778_ = lean_box(0);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1779_ = lean_array_fget_borrowed(v_as_1774_, v_j_1775_);
v___x_1780_ = ((lean_object*)(l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0));
v___x_1781_ = lean_string_dec_eq(v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_unsigned_to_nat(1u);
v___x_1783_ = lean_nat_add(v_j_1775_, v___x_1782_);
lean_dec(v_j_1775_);
v_j_1775_ = v___x_1783_;
goto _start;
}
else
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_j_1775_);
return v___x_1785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___boxed(lean_object* v_as_1786_, lean_object* v_j_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(v_as_1786_, v_j_1787_);
lean_dec_ref(v_as_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash(lean_object* v_args_1791_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0(v_args_1791_, v___x_1792_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash___closed__0));
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_args_1791_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
return v___x_1795_;
}
else
{
lean_object* v_val_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_val_1796_ = lean_ctor_get(v___x_1793_, 0);
lean_inc_n(v_val_1796_, 2);
lean_dec_ref_known(v___x_1793_, 1);
v___x_1797_ = l_Array_extract___redArg(v_args_1791_, v___x_1792_, v_val_1796_);
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_nat_add(v_val_1796_, v___x_1798_);
lean_dec(v_val_1796_);
v___x_1800_ = lean_array_get_size(v_args_1791_);
v___x_1801_ = l_Array_extract___redArg(v_args_1791_, v___x_1799_, v___x_1800_);
lean_dec_ref(v_args_1791_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1797_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
return v___x_1802_;
}
}
}
lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(lean_object* v_f_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_io_create_tempdir();
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v_r_1807_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc_n(v_a_1806_, 2);
lean_dec_ref_known(v___x_1805_, 1);
v_r_1807_ = lean_apply_2(v_f_1803_, v_a_1806_, lean_box(0));
if (lean_obj_tag(v_r_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; 
v_a_1808_ = lean_ctor_get(v_r_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v_r_1807_, 1);
v___x_1809_ = l_IO_FS_removeDirAll(v_a_1806_);
lean_dec(v_a_1806_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; 
v_unused_1817_ = lean_ctor_get(v___x_1809_, 0);
lean_dec(v_unused_1817_);
v___x_1811_ = v___x_1809_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v___x_1809_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v_a_1808_);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1808_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_a_1808_);
v_a_1818_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1809_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1809_);
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
else
{
lean_object* v_a_1826_; lean_object* v___x_1827_; 
v_a_1826_ = lean_ctor_get(v_r_1807_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v_r_1807_, 1);
v___x_1827_ = l_IO_FS_removeDirAll(v_a_1806_);
lean_dec(v_a_1806_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1834_ == 0)
{
lean_object* v_unused_1835_; 
v_unused_1835_ = lean_ctor_get(v___x_1827_, 0);
lean_dec(v_unused_1835_);
v___x_1829_ = v___x_1827_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_dec(v___x_1827_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set_tag(v___x_1829_, 1);
lean_ctor_set(v___x_1829_, 0, v_a_1826_);
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1826_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_a_1826_);
v_a_1836_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1827_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1827_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v_f_1803_);
v_a_1844_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1805_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1805_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
LEAN_EXPORT void l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1803_ = stack[0].m_obj;
lean_object* v_res_1852_;
v_res_1852_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v_f_1803_);
stack->m_obj
 = v_res_1852_;
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg___boxed(lean_object* v_f_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v_f_1853_);
return v_res_1855_;
}
}
lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(lean_object* v_00_u03b1_1856_, lean_object* v_f_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v_f_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT void l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1857_ = stack[1].m_obj;
lean_object* v_res_1860_;
v_res_1860_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(lean_box(0), v_f_1857_);
stack->m_obj
 = v_res_1860_;
}
LEAN_EXPORT lean_object* l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___boxed(lean_object* v_00_u03b1_1861_, lean_object* v_f_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1(v_00_u03b1_1861_, v_f_1862_);
return v_res_1864_;
}
}
lean_object* l_Lake_Samply_run___lam__0(lean_object* v___y_1865_, lean_object* v_____r_1866_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___y_1865_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT void l_Lake_Samply_run___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1865_ = stack[0].m_obj;
lean_object* v_____r_1866_ = stack[1].m_obj;
lean_object* v_res_1870_;
v_res_1870_ = l_Lake_Samply_run___lam__0(v___y_1865_, v_____r_1866_);
stack->m_obj
 = v_res_1870_;
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__0___boxed(lean_object* v___y_1871_, lean_object* v_____r_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lake_Samply_run___lam__0(v___y_1871_, v_____r_1872_);
return v_res_1874_;
}
}
lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(lean_object* v_s_1875_){
_start:
{
lean_object* v___x_1877_; lean_object* v_putStr_1878_; lean_object* v___x_1879_; 
v___x_1877_ = lean_get_stderr();
v_putStr_1878_ = lean_ctor_get(v___x_1877_, 4);
lean_inc_ref(v_putStr_1878_);
lean_dec_ref(v___x_1877_);
v___x_1879_ = lean_apply_2(v_putStr_1878_, v_s_1875_, lean_box(0));
return v___x_1879_;
}
}
LEAN_EXPORT void l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1875_ = stack[0].m_obj;
lean_object* v_res_1880_;
v_res_1880_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(v_s_1875_);
stack->m_obj
 = v_res_1880_;
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0___boxed(lean_object* v_s_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(v_s_1881_);
return v_res_1883_;
}
}
lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0(lean_object* v_s_1884_){
_start:
{
uint32_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = 10;
v___x_1887_ = lean_string_push(v_s_1884_, v___x_1886_);
v___x_1888_ = l_IO_eprint___at___00IO_eprintln___at___00Lake_Samply_run_spec__0_spec__0(v___x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT void l_IO_eprintln___at___00Lake_Samply_run_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1884_ = stack[0].m_obj;
lean_object* v_res_1889_;
v_res_1889_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v_s_1884_);
stack->m_obj
 = v_res_1889_;
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_Samply_run_spec__0___boxed(lean_object* v_s_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v_s_1890_);
return v_res_1892_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1898_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__2));
v___x_1899_ = lean_unsigned_to_nat(4u);
v___x_1900_ = lean_mk_empty_array_with_capacity(v___x_1899_);
v___x_1901_ = lean_array_push(v___x_1900_, v___x_1898_);
return v___x_1901_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__3));
v___x_1903_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__5, &l_Lake_Samply_run___lam__1___closed__5_once, _init_l_Lake_Samply_run___lam__1___closed__5);
v___x_1904_ = lean_array_push(v___x_1903_, v___x_1902_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__4));
v___x_1906_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__6, &l_Lake_Samply_run___lam__1___closed__6_once, _init_l_Lake_Samply_run___lam__1___closed__6);
v___x_1907_ = lean_array_push(v___x_1906_, v___x_1905_);
return v___x_1907_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1908_ = ((lean_object*)(l_Array_findIdx_x3f_loop___at___00__private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash_spec__0___closed__0));
v___x_1909_ = lean_unsigned_to_nat(2u);
v___x_1910_ = lean_mk_empty_array_with_capacity(v___x_1909_);
v___x_1911_ = lean_array_push(v___x_1910_, v___x_1908_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__20(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1924_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__19));
v___x_1925_ = lean_unsigned_to_nat(2u);
v___x_1926_ = lean_mk_empty_array_with_capacity(v___x_1925_);
v___x_1927_ = lean_array_push(v___x_1926_, v___x_1924_);
return v___x_1927_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__31(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1938_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__22));
v___x_1939_ = lean_unsigned_to_nat(9u);
v___x_1940_ = lean_mk_empty_array_with_capacity(v___x_1939_);
v___x_1941_ = lean_array_push(v___x_1940_, v___x_1938_);
return v___x_1941_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__32(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__23));
v___x_1943_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__31, &l_Lake_Samply_run___lam__1___closed__31_once, _init_l_Lake_Samply_run___lam__1___closed__31);
v___x_1944_ = lean_array_push(v___x_1943_, v___x_1942_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__33(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__24));
v___x_1946_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__32, &l_Lake_Samply_run___lam__1___closed__32_once, _init_l_Lake_Samply_run___lam__1___closed__32);
v___x_1947_ = lean_array_push(v___x_1946_, v___x_1945_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lake_Samply_run___lam__1___closed__34(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__25));
v___x_1949_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__33, &l_Lake_Samply_run___lam__1___closed__33_once, _init_l_Lake_Samply_run___lam__1___closed__33);
v___x_1950_ = lean_array_push(v___x_1949_, v___x_1948_);
return v___x_1950_;
}
}
lean_object* l_Lake_Samply_run___lam__1(lean_object* v_passthrough_1963_, lean_object* v_binary_1964_, lean_object* v___x_1965_, lean_object* v_env_1966_, uint8_t v_raw_1967_, lean_object* v_port_1968_, lean_object* v___x_1969_, uint8_t v_serve_1970_, lean_object* v_outputPath_1971_, lean_object* v_tmpDir_1972_){
_start:
{
lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v_a_1977_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___y_2021_; 
v___x_2018_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__0));
lean_inc_ref(v_tmpDir_1972_);
v___x_2019_ = l_System_FilePath_join(v_tmpDir_1972_, v___x_2018_);
if (lean_obj_tag(v_outputPath_1971_) == 0)
{
if (v_raw_1967_ == 0)
{
lean_object* v___x_2277_; 
v___x_2277_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__45));
v___y_2021_ = v___x_2277_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2278_; 
v___x_2278_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__46));
v___y_2021_ = v___x_2278_;
goto v___jp_2020_;
}
}
else
{
lean_object* v_val_2279_; 
v_val_2279_ = lean_ctor_get(v_outputPath_1971_, 0);
lean_inc(v_val_2279_);
lean_dec_ref_known(v_outputPath_1971_, 1);
v___y_2021_ = v_val_2279_;
goto v___jp_2020_;
}
v___jp_1974_:
{
lean_object* v___x_1978_; 
v___x_1978_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v___y_1976_, v___y_1975_);
lean_dec_ref(v___y_1975_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1985_ == 0)
{
lean_object* v_unused_1986_; 
v_unused_1986_ = lean_ctor_get(v___x_1978_, 0);
lean_dec(v_unused_1986_);
v___x_1980_ = v___x_1978_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_dec(v___x_1978_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 1);
lean_ctor_set(v___x_1980_, 0, v_a_1977_);
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1977_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_a_1977_);
v_a_1987_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1978_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1978_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
v___jp_1995_:
{
lean_object* v_a_1999_; lean_object* v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___y_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___y_1998_);
v___x_2000_ = l___private_Lake_CLI_Samply_0__Lake_Samply_killSafe(v___y_1997_, v___y_1996_);
lean_dec_ref(v___y_1996_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2008_; 
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v___x_2000_, 0);
lean_dec(v_unused_2009_);
v___x_2002_ = v___x_2000_;
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
else
{
lean_dec(v___x_2000_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v_a_2004_; lean_object* v___x_2006_; 
v_a_2004_ = lean_ctor_get(v_a_1999_, 0);
lean_inc(v_a_2004_);
lean_dec(v_a_1999_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v_a_2004_);
v___x_2006_ = v___x_2002_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec(v_a_1999_);
v_a_2010_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_2000_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2000_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
v___jp_2020_:
{
lean_object* v___x_2022_; lean_object* v_fst_2023_; lean_object* v_snd_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2022_ = l___private_Lake_CLI_Samply_0__Lake_Samply_splitOnDash(v_passthrough_1963_);
v_fst_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_fst_2023_);
v_snd_2024_ = lean_ctor_get(v___x_2022_, 1);
lean_inc(v_snd_2024_);
lean_dec_ref(v___x_2022_);
v___x_2025_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__1));
v___x_2026_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec_ref_known(v___x_2026_, 1);
v___x_2027_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__0));
v___x_2028_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__7, &l_Lake_Samply_run___lam__1___closed__7_once, _init_l_Lake_Samply_run___lam__1___closed__7);
lean_inc_ref(v___x_2019_);
v___x_2029_ = lean_array_push(v___x_2028_, v___x_2019_);
v___x_2030_ = l_Array_append___redArg(v___x_2029_, v_fst_2023_);
lean_dec(v_fst_2023_);
v___x_2031_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__8, &l_Lake_Samply_run___lam__1___closed__8_once, _init_l_Lake_Samply_run___lam__1___closed__8);
v___x_2032_ = lean_array_push(v___x_2031_, v_binary_1964_);
v___x_2033_ = l_Array_append___redArg(v___x_2030_, v___x_2032_);
lean_dec_ref(v___x_2032_);
v___x_2034_ = l_Array_append___redArg(v___x_2033_, v_snd_2024_);
lean_dec(v_snd_2024_);
v___x_2035_ = lean_box(0);
v___x_2036_ = 1;
v___x_2037_ = 0;
v___x_2038_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2038_, 0, v___x_2027_);
lean_ctor_set(v___x_2038_, 1, v___x_1965_);
lean_ctor_set(v___x_2038_, 2, v___x_2034_);
lean_ctor_set(v___x_2038_, 3, v___x_2035_);
lean_ctor_set(v___x_2038_, 4, v_env_1966_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*5, v___x_2036_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*5 + 1, v___x_2037_);
v___x_2039_ = lean_io_process_spawn(v___x_2038_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = lean_io_process_child_wait(v___x_2027_, v_a_2040_);
lean_dec(v_a_2040_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2252_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2252_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2252_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
uint32_t v___x_2046_; uint32_t v___x_2047_; uint8_t v___x_2048_; 
v___x_2046_ = 0;
v___x_2047_ = lean_unbox_uint32(v_a_2042_);
v___x_2048_ = lean_uint32_dec_eq(v___x_2047_, v___x_2046_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; uint32_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
lean_dec(v_port_1968_);
v___x_2049_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__9));
v___x_2050_ = lean_unbox_uint32(v_a_2042_);
lean_dec(v_a_2042_);
v___x_2051_ = lean_uint32_to_nat(v___x_2050_);
v___x_2052_ = l_Nat_reprFast(v___x_2051_);
v___x_2053_ = lean_string_append(v___x_2049_, v___x_2052_);
lean_dec_ref(v___x_2052_);
v___x_2054_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__10));
v___x_2055_ = lean_string_append(v___x_2053_, v___x_2054_);
v___x_2056_ = lean_mk_io_user_error(v___x_2055_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 1);
lean_ctor_set(v___x_2044_, 0, v___x_2056_);
v___x_2058_ = v___x_2044_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
else
{
lean_del_object(v___x_2044_);
lean_dec(v_a_2042_);
if (v_raw_1967_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__11));
v___x_2061_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2060_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_dec_ref_known(v___x_2061_, 1);
v___x_2062_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__12));
lean_inc_ref(v_tmpDir_1972_);
v___x_2063_ = l_System_FilePath_join(v_tmpDir_1972_, v___x_2062_);
v___x_2064_ = ((lean_object*)(l_String_Slice_replace___at___00__private_Lake_CLI_Samply_0__Lake_Samply_shellQuote_spec__0___redArg___closed__0));
v___x_2065_ = l_IO_FS_writeFile(v___x_2063_, v___x_2064_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec_ref_known(v___x_2065_, 1);
v___x_2066_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__13));
v___x_2067_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__1));
v___x_2068_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__14));
lean_inc(v_port_1968_);
v___x_2069_ = l_Nat_reprFast(v_port_1968_);
v___x_2070_ = lean_string_append(v___x_2068_, v___x_2069_);
v___x_2071_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__15));
v___x_2072_ = lean_string_append(v___x_2070_, v___x_2071_);
lean_inc_ref(v___x_2019_);
v___x_2073_ = l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(v___x_2019_);
v___x_2074_ = lean_string_append(v___x_2072_, v___x_2073_);
lean_dec_ref(v___x_2073_);
v___x_2075_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__16));
v___x_2076_ = lean_string_append(v___x_2074_, v___x_2075_);
lean_inc_ref(v___x_2063_);
v___x_2077_ = l___private_Lake_CLI_Samply_0__Lake_Samply_shellQuote(v___x_2063_);
v___x_2078_ = lean_string_append(v___x_2076_, v___x_2077_);
lean_dec_ref(v___x_2077_);
v___x_2079_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__17));
v___x_2080_ = lean_string_append(v___x_2078_, v___x_2079_);
v___x_2081_ = lean_obj_once(&l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4, &l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4_once, _init_l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__4);
v___x_2082_ = lean_array_push(v___x_2081_, v___x_2080_);
v___x_2083_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd___closed__5));
v___x_2084_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2084_, 0, v___x_2066_);
lean_ctor_set(v___x_2084_, 1, v___x_2067_);
lean_ctor_set(v___x_2084_, 2, v___x_2082_);
lean_ctor_set(v___x_2084_, 3, v___x_2035_);
lean_ctor_set(v___x_2084_, 4, v___x_2083_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*5, v___x_2036_);
lean_ctor_set_uint8(v___x_2084_, sizeof(void*)*5 + 1, v___x_2037_);
v___x_2085_ = lean_io_process_spawn(v___x_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2087_ = lean_unsigned_to_nat(30000u);
v___x_2088_ = l___private_Lake_CLI_Samply_0__Lake_Samply_waitForServer(v___x_2066_, v___x_2063_, v_a_2086_, v_port_1968_, v___x_2087_);
lean_dec_ref(v___x_2063_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2090_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__0));
v___x_2091_ = lean_string_append(v___x_2090_, v___x_2069_);
lean_dec_ref(v___x_2069_);
v___x_2092_ = ((lean_object*)(l___private_Lake_CLI_Samply_0__Lake_Samply_extractToken___closed__1));
v___x_2093_ = lean_string_append(v___x_2091_, v___x_2092_);
v___x_2094_ = lean_string_append(v___x_2093_, v_a_2089_);
lean_dec(v_a_2089_);
v___x_2095_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__18));
v___x_2096_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2095_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec_ref_known(v___x_2096_, 1);
v___x_2097_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__20, &l_Lake_Samply_run___lam__1___closed__20_once, _init_l_Lake_Samply_run___lam__1___closed__20);
lean_inc_ref(v___x_2019_);
v___x_2098_ = lean_array_push(v___x_2097_, v___x_2019_);
lean_inc_ref(v___x_1969_);
v___x_2099_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2099_, 0, v___x_2027_);
lean_ctor_set(v___x_2099_, 1, v___x_1969_);
lean_ctor_set(v___x_2099_, 2, v___x_2098_);
lean_ctor_set(v___x_2099_, 3, v___x_2035_);
lean_ctor_set(v___x_2099_, 4, v___x_2083_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*5, v___x_2036_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*5 + 1, v___x_2037_);
v___x_2100_ = l_IO_Process_run(v___x_2099_, v___x_2035_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = l_Lean_Json_parse(v_a_2101_);
v___x_2103_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_2102_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc_n(v_a_2104_, 2);
lean_dec_ref_known(v___x_2103_, 1);
v___x_2105_ = l___private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest(v_a_2104_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2194_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2194_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2194_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v_fst_2110_; lean_object* v_snd_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2128_; 
v_fst_2110_ = lean_ctor_get(v_a_2106_, 0);
lean_inc(v_fst_2110_);
v_snd_2111_ = lean_ctor_get(v_a_2106_, 1);
lean_inc(v_snd_2111_);
lean_dec(v_a_2106_);
v___x_2112_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__21));
v___x_2113_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__26));
lean_inc_ref(v___x_2094_);
v___x_2114_ = lean_string_append(v___x_2094_, v___x_2113_);
v___x_2115_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__27));
v___x_2116_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__28));
v___x_2117_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__29));
v___x_2118_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__30));
v___x_2119_ = lean_obj_once(&l_Lake_Samply_run___lam__1___closed__34, &l_Lake_Samply_run___lam__1___closed__34_once, _init_l_Lake_Samply_run___lam__1___closed__34);
v___x_2120_ = lean_array_push(v___x_2119_, v___x_2114_);
v___x_2121_ = lean_array_push(v___x_2120_, v___x_2115_);
v___x_2122_ = lean_array_push(v___x_2121_, v___x_2116_);
v___x_2123_ = lean_array_push(v___x_2122_, v___x_2117_);
v___x_2124_ = lean_array_push(v___x_2123_, v___x_2118_);
v___x_2125_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2125_, 0, v___x_2027_);
lean_ctor_set(v___x_2125_, 1, v___x_2112_);
lean_ctor_set(v___x_2125_, 2, v___x_2124_);
lean_ctor_set(v___x_2125_, 3, v___x_2035_);
lean_ctor_set(v___x_2125_, 4, v___x_2083_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*5, v___x_2036_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*5 + 1, v___x_2037_);
v___x_2126_ = l_Lean_Json_compress(v_fst_2110_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set_tag(v___x_2108_, 1);
lean_ctor_set(v___x_2108_, 0, v___x_2126_);
v___x_2128_ = v___x_2108_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_IO_Process_run(v___x_2125_, v___x_2128_);
lean_dec_ref(v___x_2128_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = l_Lean_Json_parse(v_a_2130_);
v___x_2132_ = l_IO_ofExcept___at___00__private_Lake_CLI_Samply_0__Lake_Samply_buildSymbolicationRequest_spec__1___redArg(v___x_2131_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = l___private_Lake_CLI_Samply_0__Lake_Samply_applySymbols(v_a_2104_, v_a_2133_, v_snd_2111_);
lean_dec(v_snd_2111_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__35));
lean_inc_ref(v_tmpDir_1972_);
v___x_2137_ = l_System_FilePath_join(v_tmpDir_1972_, v___x_2136_);
v___x_2138_ = l_Lean_Json_compress(v_a_2135_);
v___x_2139_ = l_IO_FS_writeFile(v___x_2137_, v___x_2138_);
lean_dec_ref(v___x_2138_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_dec_ref_known(v___x_2139_, 1);
v___x_2140_ = lean_unsigned_to_nat(1u);
v___x_2141_ = lean_mk_empty_array_with_capacity(v___x_2140_);
v___x_2142_ = lean_array_push(v___x_2141_, v___x_2137_);
v___x_2143_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2143_, 0, v___x_2027_);
lean_ctor_set(v___x_2143_, 1, v___x_1969_);
lean_ctor_set(v___x_2143_, 2, v___x_2142_);
lean_ctor_set(v___x_2143_, 3, v___x_2035_);
lean_ctor_set(v___x_2143_, 4, v___x_2083_);
lean_ctor_set_uint8(v___x_2143_, sizeof(void*)*5, v___x_2036_);
lean_ctor_set_uint8(v___x_2143_, sizeof(void*)*5 + 1, v___x_2037_);
v___x_2144_ = l_IO_Process_run(v___x_2143_, v___x_2035_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec_ref_known(v___x_2144_, 1);
v___x_2145_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__36));
v___x_2146_ = l_System_FilePath_join(v_tmpDir_1972_, v___x_2145_);
v___x_2147_ = lean_io_rename(v___x_2146_, v___x_2019_);
lean_dec_ref(v___x_2146_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v___x_2148_; 
lean_dec_ref_known(v___x_2147_, 1);
v___x_2148_ = l_Lake_copyFile(v___x_2019_, v___y_2021_);
lean_dec_ref(v___x_2019_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref_known(v___x_2148_, 1);
v___x_2149_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__37));
v___x_2150_ = lean_string_append(v___x_2149_, v___y_2021_);
v___x_2151_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2150_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_dec_ref_known(v___x_2151_, 1);
if (v_serve_1970_ == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec_ref(v___x_2094_);
v___x_2152_ = lean_box(0);
v___x_2153_ = l_Lake_Samply_run___lam__0(v___y_2021_, v___x_2152_);
v___y_1996_ = v_a_2086_;
v___y_1997_ = v___x_2066_;
v___y_1998_ = v___x_2153_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2154_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__38));
v___x_2155_ = lean_string_append(v___x_2154_, v___x_2094_);
v___x_2156_ = lean_string_append(v___x_2155_, v___x_2092_);
v___x_2157_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2156_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
lean_dec_ref_known(v___x_2157_, 1);
v___x_2158_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__39));
v___x_2159_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2158_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref_known(v___x_2159_, 1);
v___x_2160_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__40));
v___x_2161_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__41));
v___x_2162_ = lean_string_append(v___x_2094_, v___x_2161_);
v___x_2163_ = l_Lake_uriEncode(v___x_2162_, v___x_2064_);
lean_dec_ref(v___x_2162_);
v___x_2164_ = lean_string_append(v___x_2160_, v___x_2163_);
lean_dec_ref(v___x_2163_);
v___x_2165_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2164_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_dec_ref_known(v___x_2165_, 1);
v___x_2166_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__42));
v___x_2167_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2166_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v___x_2168_; 
lean_dec_ref_known(v___x_2167_, 1);
v___x_2168_ = lean_io_process_child_wait(v___x_2066_, v_a_2086_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; uint32_t v___x_2170_; uint8_t v___x_2171_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v___x_2170_ = lean_unbox_uint32(v_a_2169_);
v___x_2171_ = lean_uint32_dec_eq(v___x_2170_, v___x_2046_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; uint32_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_dec_ref(v___y_2021_);
v___x_2172_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__43));
v___x_2173_ = lean_unbox_uint32(v_a_2169_);
lean_dec(v_a_2169_);
v___x_2174_ = lean_uint32_to_nat(v___x_2173_);
v___x_2175_ = l_Nat_reprFast(v___x_2174_);
v___x_2176_ = lean_string_append(v___x_2172_, v___x_2175_);
lean_dec_ref(v___x_2175_);
v___x_2177_ = lean_mk_io_user_error(v___x_2176_);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v___x_2177_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_dec(v_a_2169_);
v___x_2178_ = lean_box(0);
v___x_2179_ = l_Lake_Samply_run___lam__0(v___y_2021_, v___x_2178_);
v___y_1996_ = v_a_2086_;
v___y_1997_ = v___x_2066_;
v___y_1998_ = v___x_2179_;
goto v___jp_1995_;
}
}
else
{
lean_object* v_a_2180_; 
lean_dec_ref(v___y_2021_);
v_a_2180_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2168_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2180_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2181_; 
lean_dec_ref(v___y_2021_);
v_a_2181_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2167_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2181_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2182_; 
lean_dec_ref(v___y_2021_);
v_a_2182_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2165_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2182_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2183_; 
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
v_a_2183_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2159_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2183_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2184_; 
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
v_a_2184_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2157_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2184_;
goto v___jp_1974_;
}
}
}
else
{
lean_object* v_a_2185_; 
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
v_a_2185_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2151_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2185_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2186_; 
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
v_a_2186_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2148_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2186_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2187_; 
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
v_a_2187_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2147_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2187_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2188_; 
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
v_a_2188_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2144_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2188_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2189_; 
lean_dec_ref(v___x_2137_);
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
v_a_2189_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2139_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2189_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2190_; 
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
v_a_2190_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2134_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2190_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2191_; 
lean_dec(v_snd_2111_);
lean_dec(v_a_2104_);
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
v_a_2191_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2132_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2191_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2192_; 
lean_dec(v_snd_2111_);
lean_dec(v_a_2104_);
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
v_a_2192_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v___x_2129_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2192_;
goto v___jp_1974_;
}
}
}
}
else
{
lean_object* v_a_2195_; 
lean_dec(v_a_2104_);
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
v_a_2195_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2105_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2195_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2196_; 
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
v_a_2196_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2103_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2196_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2197_; 
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
v_a_2197_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2100_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2197_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2198_; 
lean_dec_ref(v___x_2094_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
v_a_2198_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2096_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2198_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2199_; 
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
v_a_2199_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2088_, 1);
v___y_1975_ = v_a_2086_;
v___y_1976_ = v___x_2066_;
v_a_1977_ = v_a_2199_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec_ref(v___x_2069_);
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
lean_dec(v_port_1968_);
v_a_2200_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2085_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2085_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref(v___x_2063_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
lean_dec(v_port_1968_);
v_a_2208_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2065_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2065_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
lean_dec(v_port_1968_);
v_a_2216_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2061_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2061_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v___x_2224_; 
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
lean_dec(v_port_1968_);
v___x_2224_ = l_Lake_copyFile(v___x_2019_, v___y_2021_);
lean_dec_ref(v___x_2019_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec_ref_known(v___x_2224_, 1);
v___x_2225_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__44));
v___x_2226_ = lean_string_append(v___x_2225_, v___y_2021_);
v___x_2227_ = l_IO_eprintln___at___00Lake_Samply_run_spec__0(v___x_2226_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; 
v_unused_2235_ = lean_ctor_get(v___x_2227_, 0);
lean_dec(v_unused_2235_);
v___x_2229_ = v___x_2227_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_dec(v___x_2227_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___y_2021_);
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___y_2021_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref(v___y_2021_);
v_a_2236_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2227_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2227_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec_ref(v___y_2021_);
v_a_2244_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2224_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2224_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
lean_dec(v_port_1968_);
v_a_2253_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2041_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2041_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
lean_dec(v_port_1968_);
v_a_2261_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2039_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2039_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v_snd_2024_);
lean_dec(v_fst_2023_);
lean_dec_ref(v___y_2021_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v_tmpDir_1972_);
lean_dec_ref(v___x_1969_);
lean_dec(v_port_1968_);
lean_dec_ref(v_env_1966_);
lean_dec_ref(v___x_1965_);
lean_dec_ref(v_binary_1964_);
v_a_2269_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2026_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2026_);
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
}
}
LEAN_EXPORT void l_Lake_Samply_run___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_passthrough_1963_ = stack[0].m_obj;
lean_object* v_binary_1964_ = stack[1].m_obj;
lean_object* v___x_1965_ = stack[2].m_obj;
lean_object* v_env_1966_ = stack[3].m_obj;
uint8_t v_raw_1967_ = stack[4].m_num;
lean_object* v_port_1968_ = stack[5].m_obj;
lean_object* v___x_1969_ = stack[6].m_obj;
uint8_t v_serve_1970_ = stack[7].m_num;
lean_object* v_outputPath_1971_ = stack[8].m_obj;
lean_object* v_tmpDir_1972_ = stack[9].m_obj;
lean_object* v_res_2280_;
v_res_2280_ = l_Lake_Samply_run___lam__1(v_passthrough_1963_, v_binary_1964_, v___x_1965_, v_env_1966_, v_raw_1967_, v_port_1968_, v___x_1969_, v_serve_1970_, v_outputPath_1971_, v_tmpDir_1972_);
stack->m_obj
 = v_res_2280_;
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___lam__1___boxed(lean_object* v_passthrough_2281_, lean_object* v_binary_2282_, lean_object* v___x_2283_, lean_object* v_env_2284_, lean_object* v_raw_2285_, lean_object* v_port_2286_, lean_object* v___x_2287_, lean_object* v_serve_2288_, lean_object* v_outputPath_2289_, lean_object* v_tmpDir_2290_, lean_object* v___y_2291_){
_start:
{
uint8_t v_raw_boxed_2292_; uint8_t v_serve_boxed_2293_; lean_object* v_res_2294_; 
v_raw_boxed_2292_ = lean_unbox(v_raw_2285_);
v_serve_boxed_2293_ = lean_unbox(v_serve_2288_);
v_res_2294_ = l_Lake_Samply_run___lam__1(v_passthrough_2281_, v_binary_2282_, v___x_2283_, v_env_2284_, v_raw_boxed_2292_, v_port_2286_, v___x_2287_, v_serve_boxed_2293_, v_outputPath_2289_, v_tmpDir_2290_);
return v_res_2294_;
}
}
lean_object* l_Lake_Samply_run(lean_object* v_binary_2300_, lean_object* v_passthrough_2301_, lean_object* v_outputPath_2302_, lean_object* v_port_2303_, uint8_t v_raw_2304_, uint8_t v_serve_2305_, lean_object* v_env_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = ((lean_object*)(l_Lake_Samply_run___closed__0));
v___x_2309_ = ((lean_object*)(l_Lake_Samply_run___closed__1));
v___x_2310_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2308_, v___x_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___f_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_dec_ref_known(v___x_2310_, 1);
v___x_2311_ = ((lean_object*)(l_Lake_Samply_run___closed__2));
v___x_2312_ = lean_box(v_raw_2304_);
v___x_2313_ = lean_box(v_serve_2305_);
v___f_2314_ = lean_alloc_closure((void*)(l_Lake_Samply_run___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2314_, 0, v_passthrough_2301_);
lean_closure_set(v___f_2314_, 1, v_binary_2300_);
lean_closure_set(v___f_2314_, 2, v___x_2308_);
lean_closure_set(v___f_2314_, 3, v_env_2306_);
lean_closure_set(v___f_2314_, 4, v___x_2312_);
lean_closure_set(v___f_2314_, 5, v_port_2303_);
lean_closure_set(v___f_2314_, 6, v___x_2311_);
lean_closure_set(v___f_2314_, 7, v___x_2313_);
lean_closure_set(v___f_2314_, 8, v_outputPath_2302_);
v___x_2315_ = ((lean_object*)(l_Lake_Samply_run___closed__3));
v___x_2316_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2311_, v___x_2315_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_dec_ref_known(v___x_2316_, 1);
if (v_raw_2304_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = ((lean_object*)(l_Lake_Samply_run___lam__1___closed__21));
v___x_2318_ = ((lean_object*)(l_Lake_Samply_run___closed__4));
v___x_2319_ = l___private_Lake_CLI_Samply_0__Lake_Samply_requireCmd(v___x_2317_, v___x_2318_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v___x_2320_; 
lean_dec_ref_known(v___x_2319_, 1);
v___x_2320_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v___f_2314_);
return v___x_2320_;
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v___f_2314_);
v_a_2321_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2319_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2319_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v___x_2329_; 
v___x_2329_ = l_IO_FS_withTempDir___at___00Lake_Samply_run_spec__1___redArg(v___f_2314_);
return v___x_2329_;
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec_ref(v___f_2314_);
v_a_2330_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2316_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2316_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v_env_2306_);
lean_dec(v_port_2303_);
lean_dec(v_outputPath_2302_);
lean_dec_ref(v_passthrough_2301_);
lean_dec_ref(v_binary_2300_);
v_a_2338_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2310_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2310_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Samply_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_binary_2300_ = stack[0].m_obj;
lean_object* v_passthrough_2301_ = stack[1].m_obj;
lean_object* v_outputPath_2302_ = stack[2].m_obj;
lean_object* v_port_2303_ = stack[3].m_obj;
uint8_t v_raw_2304_ = stack[4].m_num;
uint8_t v_serve_2305_ = stack[5].m_num;
lean_object* v_env_2306_ = stack[6].m_obj;
lean_object* v_res_2346_;
v_res_2346_ = l_Lake_Samply_run(v_binary_2300_, v_passthrough_2301_, v_outputPath_2302_, v_port_2303_, v_raw_2304_, v_serve_2305_, v_env_2306_);
stack->m_obj
 = v_res_2346_;
}
LEAN_EXPORT lean_object* l_Lake_Samply_run___boxed(lean_object* v_binary_2347_, lean_object* v_passthrough_2348_, lean_object* v_outputPath_2349_, lean_object* v_port_2350_, lean_object* v_raw_2351_, lean_object* v_serve_2352_, lean_object* v_env_2353_, lean_object* v_a_2354_){
_start:
{
uint8_t v_raw_boxed_2355_; uint8_t v_serve_boxed_2356_; lean_object* v_res_2357_; 
v_raw_boxed_2355_ = lean_unbox(v_raw_2351_);
v_serve_boxed_2356_ = lean_unbox(v_serve_2352_);
v_res_2357_ = l_Lake_Samply_run(v_binary_2347_, v_passthrough_2348_, v_outputPath_2349_, v_port_2350_, v_raw_boxed_2355_, v_serve_boxed_2356_, v_env_2353_);
return v_res_2357_;
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
