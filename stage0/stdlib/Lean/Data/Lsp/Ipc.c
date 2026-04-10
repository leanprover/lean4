// Lean compiler output
// Module: Lean.Data.Lsp.Ipc
// Imports: public import Lean.Data.Lsp.Communication public import Lean.Data.Lsp.Diagnostics public import Lean.Data.Lsp.Extra import Init.Data.List.Sort.Basic public import Lean.Data.Lsp.LanguageFeatures import Init.While
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyOutgoingCallsParams_toJson(lean_object*);
lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t l_Lean_JsonRpc_instBEqRequestID_beq(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCallHierarchyOutgoingCall_fromJson(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyIncomingCallsParams_toJson(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyPrepareParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCallHierarchyIncomingCall_fromJson(lean_object*);
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Json_isNull(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Lsp_instToJsonLeanImport_toJson(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object*);
uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyItem_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mergeSort___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig = (const lean_object*)&l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Data.Lsp.Ipc"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Lsp.Ipc.shutdown"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: result.isNull\n      "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "exit"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Expected id "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", got id "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_shutdown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "shutdown"};
static const lean_object* l_Lean_Lsp_Ipc_shutdown___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_shutdown___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unexpected result '"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'\n"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Expected JSON-RPC response, got: '"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2_value;
static const lean_closure_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "jsonrpc"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "2.0"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5_value)}};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4_value),((lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6_value)}};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12_value;
static const lean_string_object l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13 = (const lean_object*)&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60;
static lean_once_cell_t l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Waiting for diagnostics failed: "};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "textDocument/publishDiagnostics"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1_value;
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Cannot decode publishDiagnostics parameters\n"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_collectDiagnostics___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "textDocument/waitForDiagnostics"};
static const lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_collectDiagnostics___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Waiting for ILeans failed: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_waitForILeans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "$/lean/waitForILeans"};
static const lean_object* l_Lean_Lsp_Ipc_waitForILeans___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_waitForILeans___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "item"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 25, 3, 135, 237, 12, 111, 54)}};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7_value;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "CallHierarchy"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__4_value;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ipc"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__3_value;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_0),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_1),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(35, 217, 114, 230, 122, 150, 157, 83)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value_aux_2),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(200, 239, 250, 28, 105, 0, 0, 121)}};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fromRanges"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(22, 83, 65, 87, 105, 214, 49, 248)}};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18;
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "children"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19_value),LEAN_SCALAR_PTR_LITERAL(207, 29, 161, 81, 49, 98, 4, 106)}};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(lean_object*);
static const lean_array_object l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "callHierarchy/incomingCalls"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0_value;
static const lean_array_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1_value;
static const lean_array_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2_value;
static const lean_array_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "textDocument/prepareCallHierarchy"};
static const lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0_value;
static const lean_array_object l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "callHierarchy/outgoingCalls"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0_value;
static const lean_array_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ModuleHierarchy"};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(35, 217, 114, 230, 122, 150, 157, 83)}};
static const lean_ctor_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value_aux_2),((lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 116, 164, 77, 111, 32, 93, 177)}};
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "$/lean/moduleHierarchy/imports"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0_value;
static const lean_array_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "$/lean/prepareModuleHierarchy"};
static const lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 2, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "$/lean/moduleHierarchy/importedBy"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_Ipc_runWith___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_Ipc_runWith___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_runWith___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin(lean_object* v_a_5_){
_start:
{
lean_object* v_stdin_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_stdin_7_ = lean_ctor_get(v_a_5_, 0);
lean_inc(v_stdin_7_);
v___x_8_ = lean_stream_of_handle(v_stdin_7_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin___boxed(lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Lsp_Ipc_stdin(v_a_10_);
lean_dec_ref(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout(lean_object* v_a_13_){
_start:
{
lean_object* v_stdout_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_stdout_15_ = lean_ctor_get(v_a_13_, 1);
lean_inc(v_stdout_15_);
v___x_16_ = lean_stream_of_handle(v_stdout_15_);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout___boxed(lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Lsp_Ipc_stdout(v_a_18_);
lean_dec_ref(v_a_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg(lean_object* v_inst_21_, lean_object* v_r_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_25_; lean_object* v_a_26_; lean_object* v___x_27_; 
v___x_25_ = l_Lean_Lsp_Ipc_stdin(v_a_23_);
v_a_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_a_26_);
lean_dec_ref(v___x_25_);
v___x_27_ = l_IO_FS_Stream_writeLspRequest___redArg(v_inst_21_, v_a_26_, v_r_22_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg___boxed(lean_object* v_inst_28_, lean_object* v_r_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Lsp_Ipc_writeRequest___redArg(v_inst_28_, v_r_29_, v_a_30_);
lean_dec_ref(v_a_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object* v_00_u03b1_33_, lean_object* v_inst_34_, lean_object* v_r_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Lsp_Ipc_writeRequest___redArg(v_inst_34_, v_r_35_, v_a_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___boxed(lean_object* v_00_u03b1_39_, lean_object* v_inst_40_, lean_object* v_r_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Lsp_Ipc_writeRequest(v_00_u03b1_39_, v_inst_40_, v_r_41_, v_a_42_);
lean_dec_ref(v_a_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg(lean_object* v_inst_45_, lean_object* v_n_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___x_49_; lean_object* v_a_50_; lean_object* v___x_51_; 
v___x_49_ = l_Lean_Lsp_Ipc_stdin(v_a_47_);
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
lean_dec_ref(v___x_49_);
v___x_51_ = l_IO_FS_Stream_writeLspNotification___redArg(v_inst_45_, v_a_50_, v_n_46_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg___boxed(lean_object* v_inst_52_, lean_object* v_n_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Lsp_Ipc_writeNotification___redArg(v_inst_52_, v_n_53_, v_a_54_);
lean_dec_ref(v_a_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_n_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Lsp_Ipc_writeNotification___redArg(v_inst_58_, v_n_59_, v_a_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___boxed(lean_object* v_00_u03b1_63_, lean_object* v_inst_64_, lean_object* v_n_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Lsp_Ipc_writeNotification(v_00_u03b1_63_, v_inst_64_, v_n_65_, v_a_66_);
lean_dec_ref(v_a_66_);
return v_res_68_;
}
}
static lean_object* _init_l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = l_instInhabitedError;
v___x_70_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_70_, 0, lean_box(0));
lean_closure_set(v___x_70_, 1, lean_box(0));
lean_closure_set(v___x_70_, 2, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(lean_object* v_msg_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; lean_object* v___f_75_; lean_object* v___x_2948__overap_76_; lean_object* v___x_77_; 
v___x_74_ = lean_obj_once(&l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0, &l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0_once, _init_l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0);
v___f_75_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_75_, 0, v___x_74_);
v___x_2948__overap_76_ = lean_panic_fn_borrowed(v___f_75_, v_msg_71_);
lean_dec_ref(v___f_75_);
lean_inc_ref(v___y_72_);
v___x_77_ = lean_apply_2(v___x_2948__overap_76_, v___y_72_, lean_box(0));
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___boxed(lean_object* v_msg_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(v_msg_78_, v___y_79_);
lean_dec_ref(v___y_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(lean_object* v_h_82_, lean_object* v_n_83_){
_start:
{
lean_object* v_method_85_; lean_object* v_param_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_106_; 
v_method_85_ = lean_ctor_get(v_n_83_, 0);
v_param_86_ = lean_ctor_get(v_n_83_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_n_83_);
if (v_isSharedCheck_106_ == 0)
{
v___x_88_ = v_n_83_;
v_isShared_89_ = v_isSharedCheck_106_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_param_86_);
lean_inc(v_method_85_);
lean_dec(v_n_83_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_106_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___y_91_; lean_object* v___x_96_; 
v___x_96_ = l_Lean_Json_Structured_fromJson_x3f(v_param_86_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v___x_96_);
v___x_97_ = lean_box(0);
v___y_91_ = v___x_97_;
goto v___jp_90_;
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
v_a_98_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_96_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
v___y_91_ = v___x_103_;
goto v___jp_90_;
}
}
}
v___jp_90_:
{
lean_object* v___x_93_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set_tag(v___x_88_, 1);
lean_ctor_set(v___x_88_, 1, v___y_91_);
v___x_93_ = v___x_88_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_method_85_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___y_91_);
v___x_93_ = v_reuseFailAlloc_95_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; 
v___x_94_ = l_IO_FS_Stream_writeLspMessage(v_h_82_, v___x_93_);
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1___boxed(lean_object* v_h_107_, lean_object* v_n_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(v_h_107_, v_n_108_);
return v_res_110_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_114_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2));
v___x_115_ = lean_unsigned_to_nat(6u);
v___x_116_ = lean_unsigned_to_nat(56u);
v___x_117_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1));
v___x_118_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0));
v___x_119_ = l_mkPanicMessageWithDecl(v___x_118_, v___x_117_, v___x_116_, v___x_115_, v___x_114_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v___x_130_, lean_object* v_requestNo_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
lean_inc_ref(v_a_128_);
v___x_134_ = l_IO_FS_Stream_readLspMessage(v_a_128_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_195_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_195_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_195_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_195_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
if (lean_obj_tag(v_a_135_) == 2)
{
lean_object* v_id_139_; lean_object* v_result_140_; uint8_t v___x_141_; 
v_id_139_ = lean_ctor_get(v_a_135_, 0);
lean_inc(v_id_139_);
v_result_140_ = lean_ctor_get(v_a_135_, 1);
lean_inc(v_result_140_);
lean_dec_ref(v_a_135_);
v___x_141_ = l_Lean_Json_isNull(v_result_140_);
lean_dec(v_result_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_id_139_);
lean_del_object(v___x_137_);
v___x_142_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3);
v___x_143_ = l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(v___x_142_, v___y_132_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_153_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_153_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
if (lean_obj_tag(v_a_144_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_150_; 
lean_dec(v_requestNo_131_);
lean_dec_ref(v_a_129_);
lean_dec_ref(v_a_128_);
v_a_148_ = lean_ctor_get(v_a_144_, 0);
lean_inc(v_a_148_);
lean_dec_ref(v_a_144_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v_a_148_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
else
{
lean_dec_ref(v_a_144_);
lean_del_object(v___x_146_);
goto _start;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec(v_requestNo_131_);
lean_dec_ref(v_a_129_);
lean_dec_ref(v_a_128_);
v_a_154_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_143_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_143_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v___x_162_; uint8_t v___x_174_; 
lean_dec_ref(v_a_128_);
v___x_162_ = lean_box(0);
v___x_174_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_139_, v___x_130_);
if (v___x_174_ == 0)
{
if (v___x_141_ == 0)
{
lean_dec(v_id_139_);
lean_del_object(v___x_137_);
lean_dec(v_requestNo_131_);
goto v___jp_163_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___y_181_; 
lean_dec_ref(v_a_129_);
v___x_175_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_176_ = l_Nat_reprFast(v_requestNo_131_);
v___x_177_ = lean_string_append(v___x_175_, v___x_176_);
lean_dec_ref(v___x_176_);
v___x_178_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_179_ = lean_string_append(v___x_177_, v___x_178_);
switch(lean_obj_tag(v_id_139_))
{
case 0:
{
lean_object* v_s_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_s_187_ = lean_ctor_get(v_id_139_, 0);
lean_inc_ref(v_s_187_);
lean_dec_ref(v_id_139_);
v___x_188_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_189_ = lean_string_append(v___x_188_, v_s_187_);
lean_dec_ref(v_s_187_);
v___x_190_ = lean_string_append(v___x_189_, v___x_188_);
v___y_181_ = v___x_190_;
goto v___jp_180_;
}
case 1:
{
lean_object* v_n_191_; lean_object* v___x_192_; 
v_n_191_ = lean_ctor_get(v_id_139_, 0);
lean_inc_ref(v_n_191_);
lean_dec_ref(v_id_139_);
v___x_192_ = l_Lean_JsonNumber_toString(v_n_191_);
v___y_181_ = v___x_192_;
goto v___jp_180_;
}
default: 
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_181_ = v___x_193_;
goto v___jp_180_;
}
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_182_ = lean_string_append(v___x_179_, v___y_181_);
lean_dec_ref(v___y_181_);
v___x_183_ = lean_mk_io_user_error(v___x_182_);
if (v_isShared_138_ == 0)
{
lean_ctor_set_tag(v___x_137_, 1);
lean_ctor_set(v___x_137_, 0, v___x_183_);
v___x_185_ = v___x_137_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
else
{
lean_dec(v_id_139_);
lean_del_object(v___x_137_);
lean_dec(v_requestNo_131_);
goto v___jp_163_;
}
v___jp_163_:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5));
v___x_165_ = l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(v_a_129_, v___x_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_172_ == 0)
{
lean_object* v_unused_173_; 
v_unused_173_ = lean_ctor_get(v___x_165_, 0);
lean_dec(v_unused_173_);
v___x_167_ = v___x_165_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_dec(v___x_165_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_162_);
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_162_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
else
{
return v___x_165_;
}
}
}
}
else
{
lean_del_object(v___x_137_);
lean_dec(v_a_135_);
goto _start;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec(v_requestNo_131_);
lean_dec_ref(v_a_129_);
lean_dec_ref(v_a_128_);
v_a_196_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_134_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_134_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___boxed(lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v___x_206_, lean_object* v_requestNo_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_204_, v_a_205_, v___x_206_, v_requestNo_207_, v___y_208_);
lean_dec_ref(v___y_208_);
lean_dec(v___x_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(lean_object* v_h_211_, lean_object* v_r_212_){
_start:
{
lean_object* v_id_214_; lean_object* v_method_215_; lean_object* v_param_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_236_; 
v_id_214_ = lean_ctor_get(v_r_212_, 0);
v_method_215_ = lean_ctor_get(v_r_212_, 1);
v_param_216_ = lean_ctor_get(v_r_212_, 2);
v_isSharedCheck_236_ = !lean_is_exclusive(v_r_212_);
if (v_isSharedCheck_236_ == 0)
{
v___x_218_ = v_r_212_;
v_isShared_219_ = v_isSharedCheck_236_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_param_216_);
lean_inc(v_method_215_);
lean_inc(v_id_214_);
lean_dec(v_r_212_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_236_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___y_221_; lean_object* v___x_226_; 
v___x_226_ = l_Lean_Json_Structured_fromJson_x3f(v_param_216_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; 
lean_dec_ref(v___x_226_);
v___x_227_ = lean_box(0);
v___y_221_ = v___x_227_;
goto v___jp_220_;
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v_a_228_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_226_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_226_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
v___y_221_ = v___x_233_;
goto v___jp_220_;
}
}
}
v___jp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 2, v___y_221_);
v___x_223_ = v___x_218_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_id_214_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_method_215_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v___y_221_);
v___x_223_ = v_reuseFailAlloc_225_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; 
v___x_224_ = l_IO_FS_Stream_writeLspMessage(v_h_211_, v___x_223_);
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0___boxed(lean_object* v_h_237_, lean_object* v_r_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(v_h_237_, v_r_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object* v_requestNo_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; lean_object* v_a_246_; lean_object* v___x_247_; lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_270_; 
v___x_245_ = l_Lean_Lsp_Ipc_stdout(v_a_243_);
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref(v___x_245_);
v___x_247_ = l_Lean_Lsp_Ipc_stdin(v_a_243_);
v_a_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_270_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_270_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_270_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
lean_inc(v_requestNo_242_);
v___x_252_ = l_Lean_JsonNumber_fromNat(v_requestNo_242_);
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 1);
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_269_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_255_ = ((lean_object*)(l_Lean_Lsp_Ipc_shutdown___closed__0));
v___x_256_ = lean_box(0);
lean_inc_ref(v___x_254_);
v___x_257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_257_, 0, v___x_254_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
lean_inc(v_a_248_);
v___x_258_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(v_a_248_, v___x_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v___x_259_; 
lean_dec_ref(v___x_258_);
v___x_259_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_246_, v_a_248_, v___x_254_, v_requestNo_242_, v_a_243_);
lean_dec_ref(v___x_254_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_267_; 
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v___x_259_, 0);
lean_dec(v_unused_268_);
v___x_261_ = v___x_259_;
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
else
{
lean_dec(v___x_259_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_267_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_box(0);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
return v___x_259_;
}
}
else
{
lean_dec_ref(v___x_254_);
lean_dec(v_a_248_);
lean_dec(v_a_246_);
lean_dec(v_requestNo_242_);
return v___x_258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown___boxed(lean_object* v_requestNo_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Lsp_Ipc_shutdown(v_requestNo_271_, v_a_272_);
lean_dec_ref(v_a_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object* v_v_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Json_Structured_fromJson_x3f(v_v_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3(lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v___x_279_, lean_object* v_requestNo_280_, lean_object* v_b_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_277_, v_a_278_, v___x_279_, v_requestNo_280_, v___y_282_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___boxed(lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v___x_287_, lean_object* v_requestNo_288_, lean_object* v_b_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3(v_a_285_, v_a_286_, v___x_287_, v_requestNo_288_, v_b_289_, v___y_290_);
lean_dec_ref(v___y_290_);
lean_dec(v___x_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; lean_object* v_a_296_; lean_object* v___x_297_; 
v___x_295_ = l_Lean_Lsp_Ipc_stdout(v_a_293_);
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref(v___x_295_);
v___x_297_ = l_IO_FS_Stream_readLspMessage(v_a_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage___boxed(lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Lsp_Ipc_readMessage(v_a_298_);
lean_dec_ref(v_a_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg(lean_object* v_expectedMethod_301_, lean_object* v_inst_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_305_; lean_object* v_a_306_; lean_object* v___x_307_; 
v___x_305_ = l_Lean_Lsp_Ipc_stdout(v_a_303_);
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref(v___x_305_);
v___x_307_ = l_IO_FS_Stream_readLspRequestAs___redArg(v_a_306_, v_expectedMethod_301_, v_inst_302_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg___boxed(lean_object* v_expectedMethod_308_, lean_object* v_inst_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Lsp_Ipc_readRequestAs___redArg(v_expectedMethod_308_, v_inst_309_, v_a_310_);
lean_dec_ref(v_a_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object* v_expectedMethod_313_, lean_object* v_00_u03b1_314_, lean_object* v_inst_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Lsp_Ipc_readRequestAs___redArg(v_expectedMethod_313_, v_inst_315_, v_a_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___boxed(lean_object* v_expectedMethod_319_, lean_object* v_00_u03b1_320_, lean_object* v_inst_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Lsp_Ipc_readRequestAs(v_expectedMethod_319_, v_00_u03b1_320_, v_inst_321_, v_a_322_);
lean_dec_ref(v_a_322_);
return v_res_324_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(32700u);
v___x_343_ = lean_nat_to_int(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14);
v___x_345_ = lean_int_neg(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15);
v___x_347_ = l_Lean_JsonNumber_fromInt(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16);
v___x_349_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(32600u);
v___x_351_ = lean_nat_to_int(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18);
v___x_353_ = lean_int_neg(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19);
v___x_355_ = l_Lean_JsonNumber_fromInt(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20);
v___x_357_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(32601u);
v___x_359_ = lean_nat_to_int(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22);
v___x_361_ = lean_int_neg(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23);
v___x_363_ = l_Lean_JsonNumber_fromInt(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24);
v___x_365_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(32602u);
v___x_367_ = lean_nat_to_int(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26);
v___x_369_ = lean_int_neg(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27);
v___x_371_ = l_Lean_JsonNumber_fromInt(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28);
v___x_373_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_unsigned_to_nat(32603u);
v___x_375_ = lean_nat_to_int(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30);
v___x_377_ = lean_int_neg(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31);
v___x_379_ = l_Lean_JsonNumber_fromInt(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32);
v___x_381_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(32002u);
v___x_383_ = lean_nat_to_int(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34);
v___x_385_ = lean_int_neg(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35);
v___x_387_ = l_Lean_JsonNumber_fromInt(v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36);
v___x_389_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_unsigned_to_nat(32001u);
v___x_391_ = lean_nat_to_int(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38);
v___x_393_ = lean_int_neg(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39);
v___x_395_ = l_Lean_JsonNumber_fromInt(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40);
v___x_397_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(32801u);
v___x_399_ = lean_nat_to_int(v___x_398_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42);
v___x_401_ = lean_int_neg(v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43);
v___x_403_ = l_Lean_JsonNumber_fromInt(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44);
v___x_405_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_unsigned_to_nat(32800u);
v___x_407_ = lean_nat_to_int(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46);
v___x_409_ = lean_int_neg(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47);
v___x_411_ = l_Lean_JsonNumber_fromInt(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48);
v___x_413_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_unsigned_to_nat(32900u);
v___x_415_ = lean_nat_to_int(v___x_414_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50);
v___x_417_ = lean_int_neg(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51);
v___x_419_ = l_Lean_JsonNumber_fromInt(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52);
v___x_421_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(32901u);
v___x_423_ = lean_nat_to_int(v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54);
v___x_425_ = lean_int_neg(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55);
v___x_427_ = l_Lean_JsonNumber_fromInt(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56);
v___x_429_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_unsigned_to_nat(32902u);
v___x_431_ = lean_nat_to_int(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58);
v___x_433_ = lean_int_neg(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59);
v___x_435_ = l_Lean_JsonNumber_fromInt(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60);
v___x_437_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg(lean_object* v_expectedID_438_, lean_object* v_inst_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Lsp_Ipc_stdout(v_a_440_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_587_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_587_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_587_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_587_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; 
v___x_447_ = l_IO_FS_Stream_readLspMessage(v_a_443_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_578_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_578_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_578_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_578_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___y_453_; lean_object* v___y_454_; 
switch(lean_obj_tag(v_a_448_))
{
case 2:
{
lean_object* v_id_460_; lean_object* v_result_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_505_; 
v_id_460_ = lean_ctor_get(v_a_448_, 0);
v_result_461_ = lean_ctor_get(v_a_448_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_505_ == 0)
{
v___x_463_ = v_a_448_;
v_isShared_464_ = v_isSharedCheck_505_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_result_461_);
lean_inc(v_id_460_);
lean_dec(v_a_448_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_505_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
uint8_t v___x_465_; 
v___x_465_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_460_, v_expectedID_438_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___y_468_; 
lean_del_object(v___x_463_);
lean_dec(v_result_461_);
lean_del_object(v___x_445_);
lean_dec_ref(v_inst_439_);
v___x_466_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_438_))
{
case 0:
{
lean_object* v_s_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_s_479_ = lean_ctor_get(v_expectedID_438_, 0);
lean_inc_ref(v_s_479_);
lean_dec_ref(v_expectedID_438_);
v___x_480_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_481_ = lean_string_append(v___x_480_, v_s_479_);
lean_dec_ref(v_s_479_);
v___x_482_ = lean_string_append(v___x_481_, v___x_480_);
v___y_468_ = v___x_482_;
goto v___jp_467_;
}
case 1:
{
lean_object* v_n_483_; lean_object* v___x_484_; 
v_n_483_ = lean_ctor_get(v_expectedID_438_, 0);
lean_inc_ref(v_n_483_);
lean_dec_ref(v_expectedID_438_);
v___x_484_ = l_Lean_JsonNumber_toString(v_n_483_);
v___y_468_ = v___x_484_;
goto v___jp_467_;
}
default: 
{
lean_object* v___x_485_; 
v___x_485_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_468_ = v___x_485_;
goto v___jp_467_;
}
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_string_append(v___x_466_, v___y_468_);
lean_dec_ref(v___y_468_);
v___x_470_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_471_ = lean_string_append(v___x_469_, v___x_470_);
switch(lean_obj_tag(v_id_460_))
{
case 0:
{
lean_object* v_s_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_s_472_ = lean_ctor_get(v_id_460_, 0);
lean_inc_ref(v_s_472_);
lean_dec_ref(v_id_460_);
v___x_473_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_474_ = lean_string_append(v___x_473_, v_s_472_);
lean_dec_ref(v_s_472_);
v___x_475_ = lean_string_append(v___x_474_, v___x_473_);
v___y_453_ = v___x_471_;
v___y_454_ = v___x_475_;
goto v___jp_452_;
}
case 1:
{
lean_object* v_n_476_; lean_object* v___x_477_; 
v_n_476_ = lean_ctor_get(v_id_460_, 0);
lean_inc_ref(v_n_476_);
lean_dec_ref(v_id_460_);
v___x_477_ = l_Lean_JsonNumber_toString(v_n_476_);
v___y_453_ = v___x_471_;
v___y_454_ = v___x_477_;
goto v___jp_452_;
}
default: 
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_453_ = v___x_471_;
v___y_454_ = v___x_478_;
goto v___jp_452_;
}
}
}
}
else
{
lean_object* v___x_486_; 
lean_dec(v_id_460_);
lean_del_object(v___x_450_);
lean_inc(v_result_461_);
v___x_486_ = lean_apply_1(v_inst_439_, v_result_461_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
lean_del_object(v___x_463_);
lean_dec(v_expectedID_438_);
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref(v___x_486_);
v___x_488_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_489_ = l_Lean_Json_compress(v_result_461_);
v___x_490_ = lean_string_append(v___x_488_, v___x_489_);
lean_dec_ref(v___x_489_);
v___x_491_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_492_ = lean_string_append(v___x_490_, v___x_491_);
v___x_493_ = lean_string_append(v___x_492_, v_a_487_);
lean_dec(v_a_487_);
v___x_494_ = lean_mk_io_user_error(v___x_493_);
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 1);
lean_ctor_set(v___x_445_, 0, v___x_494_);
v___x_496_ = v___x_445_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; 
lean_dec(v_result_461_);
v_a_498_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_498_);
lean_dec_ref(v___x_486_);
if (v_isShared_464_ == 0)
{
lean_ctor_set_tag(v___x_463_, 0);
lean_ctor_set(v___x_463_, 1, v_a_498_);
lean_ctor_set(v___x_463_, 0, v_expectedID_438_);
v___x_500_ = v___x_463_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_expectedID_438_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_a_498_);
v___x_500_ = v_reuseFailAlloc_504_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_500_);
v___x_502_ = v___x_445_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_506_; uint8_t v_code_507_; lean_object* v_message_508_; lean_object* v_data_x3f_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___x_542_; lean_object* v___y_544_; 
lean_del_object(v___x_450_);
lean_dec_ref(v_inst_439_);
lean_dec(v_expectedID_438_);
v_id_506_ = lean_ctor_get(v_a_448_, 0);
lean_inc(v_id_506_);
v_code_507_ = lean_ctor_get_uint8(v_a_448_, sizeof(void*)*3);
v_message_508_ = lean_ctor_get(v_a_448_, 1);
lean_inc_ref(v_message_508_);
v_data_x3f_509_ = lean_ctor_get(v_a_448_, 2);
lean_inc(v_data_x3f_509_);
lean_dec_ref(v_a_448_);
v___x_510_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_511_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3));
v___x_512_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_542_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_506_))
{
case 0:
{
lean_object* v_s_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
v_s_560_ = lean_ctor_get(v_id_506_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v_id_506_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v_id_506_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_s_560_);
lean_dec(v_id_506_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set_tag(v___x_562_, 3);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_s_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
v___y_544_ = v___x_565_;
goto v___jp_543_;
}
}
}
case 1:
{
lean_object* v_n_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_n_568_ = lean_ctor_get(v_id_506_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v_id_506_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v_id_506_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_n_568_);
lean_dec(v_id_506_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 2);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_n_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
v___y_544_ = v___x_573_;
goto v___jp_543_;
}
}
}
default: 
{
lean_object* v___x_576_; 
v___x_576_ = lean_box(0);
v___y_544_ = v___x_576_;
goto v___jp_543_;
}
}
v___jp_513_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
lean_inc(v___y_517_);
lean_inc_ref(v___y_514_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v___y_514_);
lean_ctor_set(v___x_518_, 1, v___y_517_);
v___x_519_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_520_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_520_, 0, v_message_508_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_518_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_526_ = l_Lean_Json_opt___redArg(v___x_511_, v___x_525_, v_data_x3f_509_);
v___x_527_ = l_List_appendTR___redArg(v___x_524_, v___x_526_);
v___x_528_ = l_Lean_Json_mkObj(v___x_527_);
lean_inc_ref(v___y_515_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___y_515_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___x_522_);
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v___y_516_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_512_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_Json_mkObj(v___x_532_);
v___x_534_ = l_Lean_Json_compress(v___x_533_);
v___x_535_ = lean_string_append(v___x_510_, v___x_534_);
lean_dec_ref(v___x_534_);
v___x_536_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_537_ = lean_string_append(v___x_535_, v___x_536_);
v___x_538_ = lean_mk_io_user_error(v___x_537_);
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 1);
lean_ctor_set(v___x_445_, 0, v___x_538_);
v___x_540_ = v___x_445_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_542_);
lean_ctor_set(v___x_545_, 1, v___y_544_);
v___x_546_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_547_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_507_)
{
case 0:
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_548_;
goto v___jp_513_;
}
case 1:
{
lean_object* v___x_549_; 
v___x_549_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_549_;
goto v___jp_513_;
}
case 2:
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_550_;
goto v___jp_513_;
}
case 3:
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_551_;
goto v___jp_513_;
}
case 4:
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_552_;
goto v___jp_513_;
}
case 5:
{
lean_object* v___x_553_; 
v___x_553_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_553_;
goto v___jp_513_;
}
case 6:
{
lean_object* v___x_554_; 
v___x_554_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_554_;
goto v___jp_513_;
}
case 7:
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_555_;
goto v___jp_513_;
}
case 8:
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_556_;
goto v___jp_513_;
}
case 9:
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_557_;
goto v___jp_513_;
}
case 10:
{
lean_object* v___x_558_; 
v___x_558_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_558_;
goto v___jp_513_;
}
default: 
{
lean_object* v___x_559_; 
v___x_559_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_514_ = v___x_547_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_545_;
v___y_517_ = v___x_559_;
goto v___jp_513_;
}
}
}
}
default: 
{
lean_del_object(v___x_450_);
lean_dec(v_a_448_);
lean_del_object(v___x_445_);
goto _start;
}
}
v___jp_452_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_455_ = lean_string_append(v___y_453_, v___y_454_);
lean_dec_ref(v___y_454_);
v___x_456_ = lean_mk_io_user_error(v___x_455_);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 1);
lean_ctor_set(v___x_450_, 0, v___x_456_);
v___x_458_ = v___x_450_;
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
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_del_object(v___x_445_);
lean_dec_ref(v_inst_439_);
lean_dec(v_expectedID_438_);
v_a_579_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_447_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_447_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_inst_439_);
lean_dec(v_expectedID_438_);
v_a_588_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_442_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_442_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___boxed(lean_object* v_expectedID_596_, lean_object* v_inst_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Lsp_Ipc_readResponseAs___redArg(v_expectedID_596_, v_inst_597_, v_a_598_);
lean_dec_ref(v_a_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object* v_expectedID_601_, lean_object* v_00_u03b1_602_, lean_object* v_inst_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Lsp_Ipc_readResponseAs___redArg(v_expectedID_601_, v_inst_603_, v_a_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___boxed(lean_object* v_expectedID_607_, lean_object* v_00_u03b1_608_, lean_object* v_inst_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Lsp_Ipc_readResponseAs(v_expectedID_607_, v_00_u03b1_608_, v_inst_609_, v_a_610_);
lean_dec_ref(v_a_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object* v_a_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_616_ = lean_io_process_child_wait(v___x_615_, v_a_613_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Lsp_Ipc_waitForExit(v_a_617_);
lean_dec_ref(v_a_617_);
return v_res_619_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(lean_object* v_d1_620_, lean_object* v_d2_621_){
_start:
{
uint8_t v___y_623_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d1_620_);
v___x_627_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d2_621_);
v___x_628_ = l_Lean_Lsp_instOrdRange_ord(v___x_626_, v___x_627_);
lean_dec_ref(v___x_627_);
lean_dec_ref(v___x_626_);
if (v___x_628_ == 1)
{
lean_object* v_message_629_; lean_object* v_message_630_; uint8_t v___x_631_; 
v_message_629_ = lean_ctor_get(v_d1_620_, 6);
v_message_630_ = lean_ctor_get(v_d2_621_, 6);
v___x_631_ = lean_string_dec_lt(v_message_629_, v_message_630_);
if (v___x_631_ == 0)
{
uint8_t v___x_632_; 
v___x_632_ = lean_string_dec_eq(v_message_629_, v_message_630_);
if (v___x_632_ == 0)
{
return v___x_632_;
}
else
{
v___y_623_ = v___x_628_;
goto v___jp_622_;
}
}
else
{
return v___x_631_;
}
}
else
{
v___y_623_ = v___x_628_;
goto v___jp_622_;
}
v___jp_622_:
{
if (v___y_623_ == 2)
{
uint8_t v___x_624_; 
v___x_624_ = 0;
return v___x_624_;
}
else
{
uint8_t v___x_625_; 
v___x_625_ = 1;
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed(lean_object* v_d1_633_, lean_object* v_d2_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(v_d1_633_, v_d2_634_);
lean_dec_ref(v_d2_634_);
lean_dec_ref(v_d1_633_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(lean_object* v_p_638_){
_start:
{
lean_object* v_uri_639_; lean_object* v_version_x3f_640_; lean_object* v_diagnostics_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_652_; 
v_uri_639_ = lean_ctor_get(v_p_638_, 0);
v_version_x3f_640_ = lean_ctor_get(v_p_638_, 1);
v_diagnostics_641_ = lean_ctor_get(v_p_638_, 2);
v_isSharedCheck_652_ = !lean_is_exclusive(v_p_638_);
if (v_isSharedCheck_652_ == 0)
{
v___x_643_ = v_p_638_;
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_diagnostics_641_);
lean_inc(v_version_x3f_640_);
lean_inc(v_uri_639_);
lean_dec(v_p_638_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___f_645_; lean_object* v___x_646_; lean_object* v_sorted_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
v___f_645_ = ((lean_object*)(l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0));
v___x_646_ = lean_array_to_list(v_diagnostics_641_);
v_sorted_647_ = l_List_mergeSort___redArg(v___x_646_, v___f_645_);
v___x_648_ = lean_array_mk(v_sorted_647_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 2, v___x_648_);
v___x_650_ = v___x_643_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_uri_639_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_version_x3f_640_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object* v_waitForDiagnosticsId_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Lsp_Ipc_readMessage(v_a_657_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_726_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_726_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_726_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_726_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
switch(lean_obj_tag(v_a_660_))
{
case 2:
{
lean_object* v_id_664_; uint8_t v___x_665_; 
v_id_664_ = lean_ctor_get(v_a_660_, 0);
lean_inc(v_id_664_);
lean_dec_ref(v_a_660_);
v___x_665_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_664_, v_waitForDiagnosticsId_656_);
lean_dec(v_id_664_);
if (v___x_665_ == 0)
{
lean_del_object(v___x_662_);
goto _start;
}
else
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_box(0);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_667_);
v___x_669_ = v___x_662_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
case 3:
{
lean_object* v_id_671_; lean_object* v_message_672_; uint8_t v___x_673_; 
v_id_671_ = lean_ctor_get(v_a_660_, 0);
lean_inc(v_id_671_);
v_message_672_ = lean_ctor_get(v_a_660_, 1);
lean_inc_ref(v_message_672_);
lean_dec_ref(v_a_660_);
v___x_673_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_671_, v_waitForDiagnosticsId_656_);
lean_dec(v_id_671_);
if (v___x_673_ == 0)
{
lean_dec_ref(v_message_672_);
lean_del_object(v___x_662_);
goto _start;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_675_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_676_ = lean_string_append(v___x_675_, v_message_672_);
lean_dec_ref(v_message_672_);
v___x_677_ = lean_mk_io_user_error(v___x_676_);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 1);
lean_ctor_set(v___x_662_, 0, v___x_677_);
v___x_679_ = v___x_662_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
case 1:
{
lean_object* v_method_681_; lean_object* v_params_x3f_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_724_; 
v_method_681_ = lean_ctor_get(v_a_660_, 0);
v_params_x3f_682_ = lean_ctor_get(v_a_660_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_a_660_);
if (v_isSharedCheck_724_ == 0)
{
v___x_684_ = v_a_660_;
v_isShared_685_ = v_isSharedCheck_724_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_params_x3f_682_);
lean_inc(v_method_681_);
lean_dec(v_a_660_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_724_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1));
v___x_687_ = lean_string_dec_eq(v_method_681_, v___x_686_);
lean_dec_ref(v_method_681_);
if (v___x_687_ == 0)
{
lean_del_object(v___x_684_);
lean_dec(v_params_x3f_682_);
lean_del_object(v___x_662_);
goto _start;
}
else
{
if (lean_obj_tag(v_params_x3f_682_) == 1)
{
lean_object* v_val_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_722_; 
v_val_689_ = lean_ctor_get(v_params_x3f_682_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_params_x3f_682_);
if (v_isSharedCheck_722_ == 0)
{
v___x_691_ = v_params_x3f_682_;
v_isShared_692_ = v_isSharedCheck_722_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_val_689_);
lean_dec(v_params_x3f_682_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_722_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l_Lean_Json_Structured_toJson(v_val_689_);
v___x_694_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(v___x_693_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
lean_del_object(v___x_691_);
lean_del_object(v___x_684_);
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v___x_694_);
v___x_696_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2));
v___x_697_ = lean_string_append(v___x_696_, v_a_695_);
lean_dec(v_a_695_);
v___x_698_ = lean_mk_io_user_error(v___x_697_);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 1);
lean_ctor_set(v___x_662_, 0, v___x_698_);
v___x_700_ = v___x_662_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_703_; 
lean_del_object(v___x_662_);
v_a_702_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_702_);
lean_dec_ref(v___x_694_);
v___x_703_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_656_, v_a_657_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_721_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_721_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_721_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_721_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___y_709_; 
if (lean_obj_tag(v_a_704_) == 0)
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(v_a_702_);
if (v_isShared_685_ == 0)
{
lean_ctor_set_tag(v___x_684_, 0);
lean_ctor_set(v___x_684_, 1, v___x_716_);
lean_ctor_set(v___x_684_, 0, v___x_686_);
v___x_718_ = v___x_684_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
v___y_709_ = v___x_718_;
goto v___jp_708_;
}
}
else
{
lean_object* v_val_720_; 
lean_dec(v_a_702_);
lean_del_object(v___x_684_);
v_val_720_ = lean_ctor_get(v_a_704_, 0);
lean_inc(v_val_720_);
lean_dec_ref(v_a_704_);
v___y_709_ = v_val_720_;
goto v___jp_708_;
}
v___jp_708_:
{
lean_object* v___x_711_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___y_709_);
v___x_711_ = v___x_691_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___y_709_);
v___x_711_ = v_reuseFailAlloc_715_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_711_);
v___x_713_ = v___x_706_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
else
{
lean_dec(v_a_702_);
lean_del_object(v___x_691_);
lean_del_object(v___x_684_);
return v___x_703_;
}
}
}
}
else
{
lean_del_object(v___x_684_);
lean_dec(v_params_x3f_682_);
lean_del_object(v___x_662_);
goto _start;
}
}
}
}
default: 
{
lean_del_object(v___x_662_);
lean_dec(v_a_660_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_727_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_659_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_659_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object* v_waitForDiagnosticsId_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_735_, v_a_736_);
lean_dec_ref(v_a_736_);
lean_dec(v_waitForDiagnosticsId_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(lean_object* v_v_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(v_v_739_);
v___x_741_ = l_Lean_Json_Structured_fromJson_x3f(v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object* v_h_742_, lean_object* v_r_743_){
_start:
{
lean_object* v_id_745_; lean_object* v_method_746_; lean_object* v_param_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_767_; 
v_id_745_ = lean_ctor_get(v_r_743_, 0);
v_method_746_ = lean_ctor_get(v_r_743_, 1);
v_param_747_ = lean_ctor_get(v_r_743_, 2);
v_isSharedCheck_767_ = !lean_is_exclusive(v_r_743_);
if (v_isSharedCheck_767_ == 0)
{
v___x_749_ = v_r_743_;
v_isShared_750_ = v_isSharedCheck_767_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_param_747_);
lean_inc(v_method_746_);
lean_inc(v_id_745_);
lean_dec(v_r_743_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_767_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___y_752_; lean_object* v___x_757_; 
v___x_757_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(v_param_747_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v___x_758_; 
lean_dec_ref(v___x_757_);
v___x_758_ = lean_box(0);
v___y_752_ = v___x_758_;
goto v___jp_751_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
v_a_759_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_757_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_757_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
v___y_752_ = v___x_764_;
goto v___jp_751_;
}
}
}
v___jp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 2, v___y_752_);
v___x_754_ = v___x_749_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_id_745_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_method_746_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v___y_752_);
v___x_754_ = v_reuseFailAlloc_756_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; 
v___x_755_ = l_IO_FS_Stream_writeLspMessage(v_h_742_, v___x_754_);
return v___x_755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0___boxed(lean_object* v_h_768_, lean_object* v_r_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_h_768_, v_r_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object* v_r_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___x_775_; lean_object* v_a_776_; lean_object* v___x_777_; 
v___x_775_ = l_Lean_Lsp_Ipc_stdin(v_a_773_);
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___x_775_);
v___x_777_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_a_776_, v_r_772_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0___boxed(lean_object* v_r_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v_r_778_, v_a_779_);
lean_dec_ref(v_a_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object* v_waitForDiagnosticsId_783_, lean_object* v_target_784_, lean_object* v_version_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_788_ = ((lean_object*)(l_Lean_Lsp_Ipc_collectDiagnostics___closed__0));
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_target_784_);
lean_ctor_set(v___x_789_, 1, v_version_785_);
lean_inc(v_waitForDiagnosticsId_783_);
v___x_790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_790_, 0, v_waitForDiagnosticsId_783_);
lean_ctor_set(v___x_790_, 1, v___x_788_);
lean_ctor_set(v___x_790_, 2, v___x_789_);
v___x_791_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v___x_790_, v_a_786_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v___x_792_; 
lean_dec_ref(v___x_791_);
v___x_792_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_783_, v_a_786_);
lean_dec(v_waitForDiagnosticsId_783_);
return v___x_792_;
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec(v_waitForDiagnosticsId_783_);
v_a_793_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_791_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___boxed(lean_object* v_waitForDiagnosticsId_801_, lean_object* v_target_802_, lean_object* v_version_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Lsp_Ipc_collectDiagnostics(v_waitForDiagnosticsId_801_, v_target_802_, v_version_803_, v_a_804_);
lean_dec_ref(v_a_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(lean_object* v_v_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(v_v_807_);
v___x_809_ = l_Lean_Json_Structured_fromJson_x3f(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object* v_h_810_, lean_object* v_r_811_){
_start:
{
lean_object* v_id_813_; lean_object* v_method_814_; lean_object* v_param_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_835_; 
v_id_813_ = lean_ctor_get(v_r_811_, 0);
v_method_814_ = lean_ctor_get(v_r_811_, 1);
v_param_815_ = lean_ctor_get(v_r_811_, 2);
v_isSharedCheck_835_ = !lean_is_exclusive(v_r_811_);
if (v_isSharedCheck_835_ == 0)
{
v___x_817_ = v_r_811_;
v_isShared_818_ = v_isSharedCheck_835_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_param_815_);
lean_inc(v_method_814_);
lean_inc(v_id_813_);
lean_dec(v_r_811_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_835_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___y_820_; lean_object* v___x_825_; 
v___x_825_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(v_param_815_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v___x_826_; 
lean_dec_ref(v___x_825_);
v___x_826_ = lean_box(0);
v___y_820_ = v___x_826_;
goto v___jp_819_;
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_825_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_825_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
v___y_820_ = v___x_832_;
goto v___jp_819_;
}
}
}
v___jp_819_:
{
lean_object* v___x_822_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 2, v___y_820_);
v___x_822_ = v___x_817_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_id_813_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_method_814_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v___y_820_);
v___x_822_ = v_reuseFailAlloc_824_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; 
v___x_823_ = l_IO_FS_Stream_writeLspMessage(v_h_810_, v___x_822_);
return v___x_823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0___boxed(lean_object* v_h_836_, lean_object* v_r_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_h_836_, v_r_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object* v_r_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; lean_object* v_a_844_; lean_object* v___x_845_; 
v___x_843_ = l_Lean_Lsp_Ipc_stdin(v_a_841_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref(v___x_843_);
v___x_845_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_a_844_, v_r_840_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0___boxed(lean_object* v_r_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v_r_846_, v_a_847_);
lean_dec_ref(v_a_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(lean_object* v_waitForILeansId_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Lsp_Ipc_readMessage(v___y_857_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_882_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_882_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_882_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_882_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
switch(lean_obj_tag(v_a_860_))
{
case 2:
{
lean_object* v_id_864_; uint8_t v___x_865_; 
v_id_864_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_id_864_);
lean_dec_ref(v_a_860_);
v___x_865_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_864_, v_waitForILeansId_856_);
lean_dec(v_id_864_);
if (v___x_865_ == 0)
{
lean_del_object(v___x_862_);
goto _start;
}
else
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1));
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_867_);
v___x_869_ = v___x_862_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
case 3:
{
lean_object* v_id_871_; lean_object* v_message_872_; uint8_t v___x_873_; 
v_id_871_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_id_871_);
v_message_872_ = lean_ctor_get(v_a_860_, 1);
lean_inc_ref(v_message_872_);
lean_dec_ref(v_a_860_);
v___x_873_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_871_, v_waitForILeansId_856_);
lean_dec(v_id_871_);
if (v___x_873_ == 0)
{
lean_dec_ref(v_message_872_);
lean_del_object(v___x_862_);
goto _start;
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_875_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2));
v___x_876_ = lean_string_append(v___x_875_, v_message_872_);
lean_dec_ref(v_message_872_);
v___x_877_ = lean_mk_io_user_error(v___x_876_);
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 1);
lean_ctor_set(v___x_862_, 0, v___x_877_);
v___x_879_ = v___x_862_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
default: 
{
lean_del_object(v___x_862_);
lean_dec(v_a_860_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_883_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_859_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_859_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___boxed(lean_object* v_waitForILeansId_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_891_, v___y_892_);
lean_dec_ref(v___y_892_);
lean_dec(v_waitForILeansId_891_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object* v_waitForILeansId_896_, lean_object* v_target_897_, lean_object* v_version_898_, lean_object* v_a_899_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_901_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v_target_897_);
v___x_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_903_, 0, v_version_898_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
lean_inc(v_waitForILeansId_896_);
v___x_905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_905_, 0, v_waitForILeansId_896_);
lean_ctor_set(v___x_905_, 1, v___x_901_);
lean_ctor_set(v___x_905_, 2, v___x_904_);
v___x_906_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_905_, v_a_899_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v___x_907_; 
lean_dec_ref(v___x_906_);
v___x_907_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_896_, v_a_899_);
lean_dec(v_waitForILeansId_896_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_921_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_921_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_921_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_921_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v_fst_912_; 
v_fst_912_ = lean_ctor_get(v_a_908_, 0);
lean_inc(v_fst_912_);
lean_dec(v_a_908_);
if (lean_obj_tag(v_fst_912_) == 0)
{
lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_913_ = lean_box(0);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_913_);
v___x_915_ = v___x_910_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
else
{
lean_object* v_val_917_; lean_object* v___x_919_; 
v_val_917_ = lean_ctor_get(v_fst_912_, 0);
lean_inc(v_val_917_);
lean_dec_ref(v_fst_912_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v_val_917_);
v___x_919_ = v___x_910_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_val_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
v_a_922_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_907_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_907_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_dec(v_waitForILeansId_896_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans___boxed(lean_object* v_waitForILeansId_930_, lean_object* v_target_931_, lean_object* v_version_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Lsp_Ipc_waitForILeans(v_waitForILeansId_930_, v_target_931_, v_version_932_, v_a_933_);
lean_dec_ref(v_a_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(lean_object* v_waitForILeansId_936_, lean_object* v_b_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_936_, v___y_938_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___boxed(lean_object* v_waitForILeansId_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(v_waitForILeansId_941_, v_b_942_, v___y_943_);
lean_dec_ref(v___y_943_);
lean_dec_ref(v_b_942_);
lean_dec(v_waitForILeansId_941_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans(lean_object* v_waitForILeansId_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_951_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_952_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0));
lean_inc(v_waitForILeansId_948_);
v___x_953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_953_, 0, v_waitForILeansId_948_);
lean_ctor_set(v___x_953_, 1, v___x_951_);
lean_ctor_set(v___x_953_, 2, v___x_952_);
v___x_954_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_953_, v_a_949_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v___x_955_; 
lean_dec_ref(v___x_954_);
v___x_955_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_948_, v_a_949_);
lean_dec(v_waitForILeansId_948_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_969_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_969_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_969_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_969_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_fst_960_; 
v_fst_960_ = lean_ctor_get(v_a_956_, 0);
lean_inc(v_fst_960_);
lean_dec(v_a_956_);
if (lean_obj_tag(v_fst_960_) == 0)
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_box(0);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
else
{
lean_object* v_val_965_; lean_object* v___x_967_; 
v_val_965_ = lean_ctor_get(v_fst_960_, 0);
lean_inc(v_val_965_);
lean_dec_ref(v_fst_960_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v_val_965_);
v___x_967_ = v___x_958_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_val_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v_a_970_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_955_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_955_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_dec(v_waitForILeansId_948_);
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___boxed(lean_object* v_waitForILeansId_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Lsp_Ipc_waitForWatchdogILeans(v_waitForILeansId_978_, v_a_979_);
lean_dec_ref(v_a_979_);
return v_res_981_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(lean_object* v_msg_982_, lean_object* v_as_983_, size_t v_i_984_, size_t v_stop_985_){
_start:
{
uint8_t v___x_986_; 
v___x_986_ = lean_usize_dec_eq(v_i_984_, v_stop_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v_message_988_; uint8_t v___x_989_; 
v___x_987_ = lean_array_uget_borrowed(v_as_983_, v_i_984_);
v_message_988_ = lean_ctor_get(v___x_987_, 6);
v___x_989_ = lean_string_dec_eq(v_message_988_, v_msg_982_);
if (v___x_989_ == 0)
{
size_t v___x_990_; size_t v___x_991_; 
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_984_, v___x_990_);
v_i_984_ = v___x_991_;
goto _start;
}
else
{
return v___x_989_;
}
}
else
{
uint8_t v___x_993_; 
v___x_993_ = 0;
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0___boxed(lean_object* v_msg_994_, lean_object* v_as_995_, lean_object* v_i_996_, lean_object* v_stop_997_){
_start:
{
size_t v_i_boxed_998_; size_t v_stop_boxed_999_; uint8_t v_res_1000_; lean_object* v_r_1001_; 
v_i_boxed_998_ = lean_unbox_usize(v_i_996_);
lean_dec(v_i_996_);
v_stop_boxed_999_ = lean_unbox_usize(v_stop_997_);
lean_dec(v_stop_997_);
v_res_1000_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(v_msg_994_, v_as_995_, v_i_boxed_998_, v_stop_boxed_999_);
lean_dec_ref(v_as_995_);
lean_dec_ref(v_msg_994_);
v_r_1001_ = lean_box(v_res_1000_);
return v_r_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(lean_object* v_msg_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_Lsp_Ipc_readMessage(v_a_1003_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1042_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1042_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1042_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
if (lean_obj_tag(v_a_1006_) == 1)
{
lean_object* v_method_1010_; lean_object* v_params_x3f_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v_method_1010_ = lean_ctor_get(v_a_1006_, 0);
lean_inc_ref(v_method_1010_);
v_params_x3f_1011_ = lean_ctor_get(v_a_1006_, 1);
lean_inc(v_params_x3f_1011_);
lean_dec_ref(v_a_1006_);
v___x_1012_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1));
v___x_1013_ = lean_string_dec_eq(v_method_1010_, v___x_1012_);
lean_dec_ref(v_method_1010_);
if (v___x_1013_ == 0)
{
lean_dec(v_params_x3f_1011_);
lean_del_object(v___x_1008_);
goto _start;
}
else
{
if (lean_obj_tag(v_params_x3f_1011_) == 1)
{
lean_object* v_val_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_val_1015_ = lean_ctor_get(v_params_x3f_1011_, 0);
lean_inc(v_val_1015_);
lean_dec_ref(v_params_x3f_1011_);
v___x_1016_ = l_Lean_Json_Structured_toJson(v_val_1015_);
v___x_1017_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(v___x_1016_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref(v___x_1017_);
v___x_1019_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2));
v___x_1020_ = lean_string_append(v___x_1019_, v_a_1018_);
lean_dec(v_a_1018_);
v___x_1021_ = lean_mk_io_user_error(v___x_1020_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set_tag(v___x_1008_, 1);
lean_ctor_set(v___x_1008_, 0, v___x_1021_);
v___x_1023_ = v___x_1008_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
else
{
lean_object* v_a_1025_; lean_object* v_diagnostics_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v_a_1025_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1025_);
lean_dec_ref(v___x_1017_);
v_diagnostics_1026_ = lean_ctor_get(v_a_1025_, 2);
lean_inc_ref(v_diagnostics_1026_);
lean_dec(v_a_1025_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = lean_array_get_size(v_diagnostics_1026_);
v___x_1029_ = lean_nat_dec_lt(v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_dec_ref(v_diagnostics_1026_);
lean_del_object(v___x_1008_);
goto _start;
}
else
{
if (v___x_1029_ == 0)
{
lean_dec_ref(v_diagnostics_1026_);
lean_del_object(v___x_1008_);
goto _start;
}
else
{
size_t v___x_1032_; size_t v___x_1033_; uint8_t v___x_1034_; 
v___x_1032_ = ((size_t)0ULL);
v___x_1033_ = lean_usize_of_nat(v___x_1028_);
v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(v_msg_1002_, v_diagnostics_1026_, v___x_1032_, v___x_1033_);
lean_dec_ref(v_diagnostics_1026_);
if (v___x_1034_ == 0)
{
lean_del_object(v___x_1008_);
goto _start;
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_box(0);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1036_);
v___x_1038_ = v___x_1008_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
}
else
{
lean_dec(v_params_x3f_1011_);
lean_del_object(v___x_1008_);
goto _start;
}
}
}
else
{
lean_del_object(v___x_1008_);
lean_dec(v_a_1006_);
goto _start;
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_a_1043_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1005_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1005_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop___boxed(lean_object* v_msg_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(v_msg_1051_, v_a_1052_);
lean_dec_ref(v_a_1052_);
lean_dec_ref(v_msg_1051_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage(lean_object* v_msg_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(v_msg_1055_, v_a_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage___boxed(lean_object* v_msg_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Lsp_Ipc_waitForMessage(v_msg_1059_, v_a_1060_);
lean_dec_ref(v_a_1060_);
lean_dec_ref(v_msg_1059_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(lean_object* v_j_1063_, lean_object* v_k_1064_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = l_Lean_Json_getObjValD(v_j_1063_, v_k_1064_);
v___x_1066_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0___boxed(lean_object* v_j_1067_, lean_object* v_k_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_j_1067_, v_k_1068_);
lean_dec_ref(v_k_1068_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_1070_, size_t v_i_1071_, lean_object* v_bs_1072_){
_start:
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_usize_dec_lt(v_i_1071_, v_sz_1070_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_bs_1072_);
return v___x_1074_;
}
else
{
lean_object* v_v_1075_; lean_object* v___x_1076_; 
v_v_1075_ = lean_array_uget_borrowed(v_bs_1072_, v_i_1071_);
lean_inc(v_v_1075_);
v___x_1076_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_v_1075_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref(v_bs_1072_);
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v_bs_x27_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v_a_1085_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v___x_1076_);
v___x_1086_ = lean_unsigned_to_nat(0u);
v_bs_x27_1087_ = lean_array_uset(v_bs_1072_, v_i_1071_, v___x_1086_);
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_add(v_i_1071_, v___x_1088_);
v___x_1090_ = lean_array_uset(v_bs_x27_1087_, v_i_1071_, v_a_1085_);
v_i_1071_ = v___x_1089_;
v_bs_1072_ = v___x_1090_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1092_, lean_object* v_i_1093_, lean_object* v_bs_1094_){
_start:
{
size_t v_sz_boxed_1095_; size_t v_i_boxed_1096_; lean_object* v_res_1097_; 
v_sz_boxed_1095_ = lean_unbox_usize(v_sz_1092_);
lean_dec(v_sz_1092_);
v_i_boxed_1096_ = lean_unbox_usize(v_i_1093_);
lean_dec(v_i_1093_);
v_res_1097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_1095_, v_i_boxed_1096_, v_bs_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_1099_){
_start:
{
if (lean_obj_tag(v_x_1099_) == 4)
{
lean_object* v_elems_1100_; size_t v_sz_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v_elems_1100_ = lean_ctor_get(v_x_1099_, 0);
lean_inc_ref(v_elems_1100_);
lean_dec_ref(v_x_1099_);
v_sz_1101_ = lean_array_size(v_elems_1100_);
v___x_1102_ = ((size_t)0ULL);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_1101_, v___x_1102_, v_elems_1100_);
return v___x_1103_;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1104_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1105_ = lean_unsigned_to_nat(80u);
v___x_1106_ = l_Lean_Json_pretty(v_x_1099_, v___x_1105_);
v___x_1107_ = lean_string_append(v___x_1104_, v___x_1106_);
lean_dec_ref(v___x_1106_);
v___x_1108_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1109_ = lean_string_append(v___x_1107_, v___x_1108_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(lean_object* v_j_1111_, lean_object* v_k_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = l_Lean_Json_getObjValD(v_j_1111_, v_k_1112_);
v___x_1114_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1___boxed(lean_object* v_j_1115_, lean_object* v_k_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_j_1115_, v_k_1116_);
lean_dec_ref(v_k_1116_);
return v_res_1117_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = 1;
v___x_1123_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9));
v___x_1124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1123_, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = 1;
v___x_1136_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5));
v___x_1137_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_1139_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6);
v___x_1140_ = lean_string_append(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_1142_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1143_ = lean_string_append(v___x_1142_, v___x_1141_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1145_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11);
v___x_1146_ = lean_string_append(v___x_1145_, v___x_1144_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = 1;
v___x_1151_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15));
v___x_1152_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1151_, v___x_1150_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16);
v___x_1154_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1155_ = lean_string_append(v___x_1154_, v___x_1153_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1157_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17);
v___x_1158_ = lean_string_append(v___x_1157_, v___x_1156_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = 1;
v___x_1163_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20));
v___x_1164_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1163_, v___x_1162_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_1166_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1167_ = lean_string_append(v___x_1166_, v___x_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1169_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22);
v___x_1170_ = lean_string_append(v___x_1169_, v___x_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(lean_object* v_json_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_1171_);
v___x_1173_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_json_1171_, v___x_1172_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_json_1171_);
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1183_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1183_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1178_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13);
v___x_1179_ = lean_string_append(v___x_1178_, v_a_1174_);
lean_dec(v_a_1174_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1179_);
v___x_1181_ = v___x_1176_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_json_1171_);
v_a_1184_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1173_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1173_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set_tag(v___x_1186_, 0);
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_a_1192_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1192_);
lean_dec_ref(v___x_1173_);
v___x_1193_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
lean_inc(v_json_1171_);
v___x_1194_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_json_1171_, v___x_1193_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_a_1192_);
lean_dec(v_json_1171_);
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1199_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18);
v___x_1200_ = lean_string_append(v___x_1199_, v_a_1195_);
lean_dec(v_a_1195_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
else
{
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v_a_1192_);
lean_dec(v_json_1171_);
v_a_1205_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1194_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1194_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set_tag(v___x_1207_, 0);
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_a_1213_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1213_);
lean_dec_ref(v___x_1194_);
v___x_1214_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1215_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_json_1171_, v___x_1214_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_a_1213_);
lean_dec(v_a_1192_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1225_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1225_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1220_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23);
v___x_1221_ = lean_string_append(v___x_1220_, v_a_1216_);
lean_dec(v_a_1216_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1221_);
v___x_1223_ = v___x_1218_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
else
{
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v_a_1213_);
lean_dec(v_a_1192_);
v_a_1226_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1215_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1215_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set_tag(v___x_1228_, 0);
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1242_; 
v_a_1234_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1236_ = v___x_1215_;
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1215_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1238_, 0, v_a_1192_);
lean_ctor_set(v___x_1238_, 1, v_a_1213_);
lean_ctor_set(v___x_1238_, 2, v_a_1234_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1238_);
v___x_1240_ = v___x_1236_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(size_t v_sz_1243_, size_t v_i_1244_, lean_object* v_bs_1245_){
_start:
{
uint8_t v___x_1246_; 
v___x_1246_ = lean_usize_dec_lt(v_i_1244_, v_sz_1243_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1247_, 0, v_bs_1245_);
return v___x_1247_;
}
else
{
lean_object* v_v_1248_; lean_object* v___x_1249_; 
v_v_1248_ = lean_array_uget_borrowed(v_bs_1245_, v_i_1244_);
lean_inc(v_v_1248_);
v___x_1249_ = l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(v_v_1248_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_bs_1245_);
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
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
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v_bs_x27_1260_; size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v_a_1258_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1258_);
lean_dec_ref(v___x_1249_);
v___x_1259_ = lean_unsigned_to_nat(0u);
v_bs_x27_1260_ = lean_array_uset(v_bs_1245_, v_i_1244_, v___x_1259_);
v___x_1261_ = ((size_t)1ULL);
v___x_1262_ = lean_usize_add(v_i_1244_, v___x_1261_);
v___x_1263_ = lean_array_uset(v_bs_x27_1260_, v_i_1244_, v_a_1258_);
v_i_1244_ = v___x_1262_;
v_bs_1245_ = v___x_1263_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(lean_object* v_x_1265_){
_start:
{
if (lean_obj_tag(v_x_1265_) == 4)
{
lean_object* v_elems_1266_; size_t v_sz_1267_; size_t v___x_1268_; lean_object* v___x_1269_; 
v_elems_1266_ = lean_ctor_get(v_x_1265_, 0);
lean_inc_ref(v_elems_1266_);
lean_dec_ref(v_x_1265_);
v_sz_1267_ = lean_array_size(v_elems_1266_);
v___x_1268_ = ((size_t)0ULL);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_1267_, v___x_1268_, v_elems_1266_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1270_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1271_ = lean_unsigned_to_nat(80u);
v___x_1272_ = l_Lean_Json_pretty(v_x_1265_, v___x_1271_);
v___x_1273_ = lean_string_append(v___x_1270_, v___x_1272_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1275_ = lean_string_append(v___x_1273_, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(lean_object* v_j_1277_, lean_object* v_k_1278_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = l_Lean_Json_getObjValD(v_j_1277_, v_k_1278_);
v___x_1280_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2___boxed(lean_object* v_j_1281_, lean_object* v_k_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_j_1281_, v_k_1282_);
lean_dec_ref(v_k_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1284_, lean_object* v_i_1285_, lean_object* v_bs_1286_){
_start:
{
size_t v_sz_boxed_1287_; size_t v_i_boxed_1288_; lean_object* v_res_1289_; 
v_sz_boxed_1287_ = lean_unbox_usize(v_sz_1284_);
lean_dec(v_sz_1284_);
v_i_boxed_1288_ = lean_unbox_usize(v_i_1285_);
lean_dec(v_i_1285_);
v_res_1289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_boxed_1287_, v_i_boxed_1288_, v_bs_1286_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
if (lean_obj_tag(v_a_1292_) == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_array_to_list(v_a_1293_);
return v___x_1294_;
}
else
{
lean_object* v_head_1295_; lean_object* v_tail_1296_; lean_object* v___x_1297_; 
v_head_1295_ = lean_ctor_get(v_a_1292_, 0);
lean_inc(v_head_1295_);
v_tail_1296_ = lean_ctor_get(v_a_1292_, 1);
lean_inc(v_tail_1296_);
lean_dec_ref(v_a_1292_);
v___x_1297_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1293_, v_head_1295_);
v_a_1292_ = v_tail_1296_;
v_a_1293_ = v___x_1297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(size_t v_sz_1299_, size_t v_i_1300_, lean_object* v_bs_1301_){
_start:
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_usize_dec_lt(v_i_1300_, v_sz_1299_);
if (v___x_1302_ == 0)
{
return v_bs_1301_;
}
else
{
lean_object* v_v_1303_; lean_object* v___x_1304_; lean_object* v_bs_x27_1305_; lean_object* v___x_1306_; size_t v___x_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
v_v_1303_ = lean_array_uget(v_bs_1301_, v_i_1300_);
v___x_1304_ = lean_unsigned_to_nat(0u);
v_bs_x27_1305_ = lean_array_uset(v_bs_1301_, v_i_1300_, v___x_1304_);
v___x_1306_ = l_Lean_Lsp_instToJsonRange_toJson(v_v_1303_);
v___x_1307_ = ((size_t)1ULL);
v___x_1308_ = lean_usize_add(v_i_1300_, v___x_1307_);
v___x_1309_ = lean_array_uset(v_bs_x27_1305_, v_i_1300_, v___x_1306_);
v_i_1300_ = v___x_1308_;
v_bs_1301_ = v___x_1309_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1311_, lean_object* v_i_1312_, lean_object* v_bs_1313_){
_start:
{
size_t v_sz_boxed_1314_; size_t v_i_boxed_1315_; lean_object* v_res_1316_; 
v_sz_boxed_1314_ = lean_unbox_usize(v_sz_1311_);
lean_dec(v_sz_1311_);
v_i_boxed_1315_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_boxed_1314_, v_i_boxed_1315_, v_bs_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(lean_object* v_a_1317_){
_start:
{
size_t v_sz_1318_; size_t v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_sz_1318_ = lean_array_size(v_a_1317_);
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_1318_, v___x_1319_, v_a_1317_);
v___x_1321_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(lean_object* v_x_1324_){
_start:
{
lean_object* v_item_1325_; lean_object* v_fromRanges_1326_; lean_object* v_children_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_item_1325_ = lean_ctor_get(v_x_1324_, 0);
lean_inc_ref(v_item_1325_);
v_fromRanges_1326_ = lean_ctor_get(v_x_1324_, 1);
lean_inc_ref(v_fromRanges_1326_);
v_children_1327_ = lean_ctor_get(v_x_1324_, 2);
lean_inc_ref(v_children_1327_);
lean_dec_ref(v_x_1324_);
v___x_1328_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_1329_ = l_Lean_Lsp_instToJsonCallHierarchyItem_toJson(v_item_1325_);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_box(0);
v___x_1332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
v___x_1334_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(v_fromRanges_1326_);
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v___x_1331_);
v___x_1337_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1338_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(v_children_1327_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set(v___x_1340_, 1, v___x_1331_);
v___x_1341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v___x_1331_);
v___x_1342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1336_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1332_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_1345_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_1343_, v___x_1344_);
v___x_1346_ = l_Lean_Json_mkObj(v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(size_t v_sz_1347_, size_t v_i_1348_, lean_object* v_bs_1349_){
_start:
{
uint8_t v___x_1350_; 
v___x_1350_ = lean_usize_dec_lt(v_i_1348_, v_sz_1347_);
if (v___x_1350_ == 0)
{
return v_bs_1349_;
}
else
{
lean_object* v_v_1351_; lean_object* v___x_1352_; lean_object* v_bs_x27_1353_; lean_object* v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v_v_1351_ = lean_array_uget(v_bs_1349_, v_i_1348_);
v___x_1352_ = lean_unsigned_to_nat(0u);
v_bs_x27_1353_ = lean_array_uset(v_bs_1349_, v_i_1348_, v___x_1352_);
v___x_1354_ = l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(v_v_1351_);
v___x_1355_ = ((size_t)1ULL);
v___x_1356_ = lean_usize_add(v_i_1348_, v___x_1355_);
v___x_1357_ = lean_array_uset(v_bs_x27_1353_, v_i_1348_, v___x_1354_);
v_i_1348_ = v___x_1356_;
v_bs_1349_ = v___x_1357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(lean_object* v_a_1359_){
_start:
{
size_t v_sz_1360_; size_t v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_sz_1360_ = lean_array_size(v_a_1359_);
v___x_1361_ = ((size_t)0ULL);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_1360_, v___x_1361_, v_a_1359_);
v___x_1363_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2___boxed(lean_object* v_sz_1364_, lean_object* v_i_1365_, lean_object* v_bs_1366_){
_start:
{
size_t v_sz_boxed_1367_; size_t v_i_boxed_1368_; lean_object* v_res_1369_; 
v_sz_boxed_1367_ = lean_unbox_usize(v_sz_1364_);
lean_dec(v_sz_1364_);
v_i_boxed_1368_ = lean_unbox_usize(v_i_1365_);
lean_dec(v_i_1365_);
v_res_1369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_boxed_1367_, v_i_boxed_1368_, v_bs_1366_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(lean_object* v_k_1372_, lean_object* v_v_1373_, lean_object* v_t_1374_){
_start:
{
if (lean_obj_tag(v_t_1374_) == 0)
{
lean_object* v_size_1375_; lean_object* v_k_1376_; lean_object* v_v_1377_; lean_object* v_l_1378_; lean_object* v_r_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1660_; 
v_size_1375_ = lean_ctor_get(v_t_1374_, 0);
v_k_1376_ = lean_ctor_get(v_t_1374_, 1);
v_v_1377_ = lean_ctor_get(v_t_1374_, 2);
v_l_1378_ = lean_ctor_get(v_t_1374_, 3);
v_r_1379_ = lean_ctor_get(v_t_1374_, 4);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_t_1374_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1381_ = v_t_1374_;
v_isShared_1382_ = v_isSharedCheck_1660_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_r_1379_);
lean_inc(v_l_1378_);
lean_inc(v_v_1377_);
lean_inc(v_k_1376_);
lean_inc(v_size_1375_);
lean_dec(v_t_1374_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1660_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_string_dec_lt(v_k_1372_, v_k_1376_);
if (v___x_1383_ == 0)
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_string_dec_eq(v_k_1372_, v_k_1376_);
if (v___x_1384_ == 0)
{
lean_object* v_impl_1385_; lean_object* v___x_1386_; 
lean_dec(v_size_1375_);
v_impl_1385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1372_, v_v_1373_, v_r_1379_);
v___x_1386_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1378_) == 0)
{
lean_object* v_size_1387_; lean_object* v_size_1388_; lean_object* v_k_1389_; lean_object* v_v_1390_; lean_object* v_l_1391_; lean_object* v_r_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_size_1387_ = lean_ctor_get(v_l_1378_, 0);
v_size_1388_ = lean_ctor_get(v_impl_1385_, 0);
lean_inc(v_size_1388_);
v_k_1389_ = lean_ctor_get(v_impl_1385_, 1);
lean_inc(v_k_1389_);
v_v_1390_ = lean_ctor_get(v_impl_1385_, 2);
lean_inc(v_v_1390_);
v_l_1391_ = lean_ctor_get(v_impl_1385_, 3);
lean_inc(v_l_1391_);
v_r_1392_ = lean_ctor_get(v_impl_1385_, 4);
lean_inc(v_r_1392_);
v___x_1393_ = lean_unsigned_to_nat(3u);
v___x_1394_ = lean_nat_mul(v___x_1393_, v_size_1387_);
v___x_1395_ = lean_nat_dec_lt(v___x_1394_, v_size_1388_);
lean_dec(v___x_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
lean_dec(v_r_1392_);
lean_dec(v_l_1391_);
lean_dec(v_v_1390_);
lean_dec(v_k_1389_);
v___x_1396_ = lean_nat_add(v___x_1386_, v_size_1387_);
v___x_1397_ = lean_nat_add(v___x_1396_, v_size_1388_);
lean_dec(v_size_1388_);
lean_dec(v___x_1396_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 4, v_impl_1385_);
lean_ctor_set(v___x_1381_, 0, v___x_1397_);
v___x_1399_ = v___x_1381_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_l_1378_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_impl_1385_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
else
{
lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1464_; 
v_isSharedCheck_1464_ = !lean_is_exclusive(v_impl_1385_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; lean_object* v_unused_1469_; 
v_unused_1465_ = lean_ctor_get(v_impl_1385_, 4);
lean_dec(v_unused_1465_);
v_unused_1466_ = lean_ctor_get(v_impl_1385_, 3);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_impl_1385_, 2);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_impl_1385_, 1);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_impl_1385_, 0);
lean_dec(v_unused_1469_);
v___x_1402_ = v_impl_1385_;
v_isShared_1403_ = v_isSharedCheck_1464_;
goto v_resetjp_1401_;
}
else
{
lean_dec(v_impl_1385_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1464_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v_size_1404_; lean_object* v_k_1405_; lean_object* v_v_1406_; lean_object* v_l_1407_; lean_object* v_r_1408_; lean_object* v_size_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_size_1404_ = lean_ctor_get(v_l_1391_, 0);
v_k_1405_ = lean_ctor_get(v_l_1391_, 1);
v_v_1406_ = lean_ctor_get(v_l_1391_, 2);
v_l_1407_ = lean_ctor_get(v_l_1391_, 3);
v_r_1408_ = lean_ctor_get(v_l_1391_, 4);
v_size_1409_ = lean_ctor_get(v_r_1392_, 0);
v___x_1410_ = lean_unsigned_to_nat(2u);
v___x_1411_ = lean_nat_mul(v___x_1410_, v_size_1409_);
v___x_1412_ = lean_nat_dec_lt(v_size_1404_, v___x_1411_);
lean_dec(v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1440_; 
lean_inc(v_r_1408_);
lean_inc(v_l_1407_);
lean_inc(v_v_1406_);
lean_inc(v_k_1405_);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_l_1391_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; lean_object* v_unused_1442_; lean_object* v_unused_1443_; lean_object* v_unused_1444_; lean_object* v_unused_1445_; 
v_unused_1441_ = lean_ctor_get(v_l_1391_, 4);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_l_1391_, 3);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_l_1391_, 2);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_l_1391_, 1);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v_l_1391_, 0);
lean_dec(v_unused_1445_);
v___x_1414_ = v_l_1391_;
v_isShared_1415_ = v_isSharedCheck_1440_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v_l_1391_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1440_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1430_; 
v___x_1416_ = lean_nat_add(v___x_1386_, v_size_1387_);
v___x_1417_ = lean_nat_add(v___x_1416_, v_size_1388_);
lean_dec(v_size_1388_);
if (lean_obj_tag(v_l_1407_) == 0)
{
lean_object* v_size_1438_; 
v_size_1438_ = lean_ctor_get(v_l_1407_, 0);
lean_inc(v_size_1438_);
v___y_1430_ = v_size_1438_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_unsigned_to_nat(0u);
v___y_1430_ = v___x_1439_;
goto v___jp_1429_;
}
v___jp_1418_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_nat_add(v___y_1419_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec(v___y_1419_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 4, v_r_1392_);
lean_ctor_set(v___x_1414_, 3, v_r_1408_);
lean_ctor_set(v___x_1414_, 2, v_v_1390_);
lean_ctor_set(v___x_1414_, 1, v_k_1389_);
lean_ctor_set(v___x_1414_, 0, v___x_1422_);
v___x_1424_ = v___x_1414_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_r_1408_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v_r_1392_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1426_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 4, v___x_1424_);
lean_ctor_set(v___x_1402_, 3, v___y_1420_);
lean_ctor_set(v___x_1402_, 2, v_v_1406_);
lean_ctor_set(v___x_1402_, 1, v_k_1405_);
lean_ctor_set(v___x_1402_, 0, v___x_1417_);
v___x_1426_ = v___x_1402_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1405_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1406_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v___y_1420_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
v___jp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1431_ = lean_nat_add(v___x_1416_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec(v___x_1416_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 4, v_l_1407_);
lean_ctor_set(v___x_1381_, 0, v___x_1431_);
v___x_1433_ = v___x_1381_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v_l_1378_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v_l_1407_);
v___x_1433_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_nat_add(v___x_1386_, v_size_1409_);
if (lean_obj_tag(v_r_1408_) == 0)
{
lean_object* v_size_1435_; 
v_size_1435_ = lean_ctor_get(v_r_1408_, 0);
lean_inc(v_size_1435_);
v___y_1419_ = v___x_1434_;
v___y_1420_ = v___x_1433_;
v___y_1421_ = v_size_1435_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___y_1419_ = v___x_1434_;
v___y_1420_ = v___x_1433_;
v___y_1421_ = v___x_1436_;
goto v___jp_1418_;
}
}
}
}
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
lean_del_object(v___x_1381_);
v___x_1446_ = lean_nat_add(v___x_1386_, v_size_1387_);
v___x_1447_ = lean_nat_add(v___x_1446_, v_size_1388_);
lean_dec(v_size_1388_);
v___x_1448_ = lean_nat_add(v___x_1446_, v_size_1404_);
lean_dec(v___x_1446_);
lean_inc_ref(v_l_1378_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 4, v_l_1391_);
lean_ctor_set(v___x_1402_, 3, v_l_1378_);
lean_ctor_set(v___x_1402_, 2, v_v_1377_);
lean_ctor_set(v___x_1402_, 1, v_k_1376_);
lean_ctor_set(v___x_1402_, 0, v___x_1448_);
v___x_1450_ = v___x_1402_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v_l_1378_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v_l_1391_);
v___x_1450_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
v_isSharedCheck_1457_ = !lean_is_exclusive(v_l_1378_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; lean_object* v_unused_1462_; 
v_unused_1458_ = lean_ctor_get(v_l_1378_, 4);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_l_1378_, 3);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_l_1378_, 2);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_l_1378_, 1);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_l_1378_, 0);
lean_dec(v_unused_1462_);
v___x_1452_ = v_l_1378_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v_l_1378_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 4, v_r_1392_);
lean_ctor_set(v___x_1452_, 3, v___x_1450_);
lean_ctor_set(v___x_1452_, 2, v_v_1390_);
lean_ctor_set(v___x_1452_, 1, v_k_1389_);
lean_ctor_set(v___x_1452_, 0, v___x_1447_);
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v_r_1392_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1470_; 
v_l_1470_ = lean_ctor_get(v_impl_1385_, 3);
lean_inc(v_l_1470_);
if (lean_obj_tag(v_l_1470_) == 0)
{
lean_object* v_r_1471_; lean_object* v_k_1472_; lean_object* v_v_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1496_; 
v_r_1471_ = lean_ctor_get(v_impl_1385_, 4);
v_k_1472_ = lean_ctor_get(v_impl_1385_, 1);
v_v_1473_ = lean_ctor_get(v_impl_1385_, 2);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_impl_1385_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; 
v_unused_1497_ = lean_ctor_get(v_impl_1385_, 3);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_impl_1385_, 0);
lean_dec(v_unused_1498_);
v___x_1475_ = v_impl_1385_;
v_isShared_1476_ = v_isSharedCheck_1496_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_r_1471_);
lean_inc(v_v_1473_);
lean_inc(v_k_1472_);
lean_dec(v_impl_1385_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1496_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_k_1477_; lean_object* v_v_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1492_; 
v_k_1477_ = lean_ctor_get(v_l_1470_, 1);
v_v_1478_ = lean_ctor_get(v_l_1470_, 2);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_l_1470_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; 
v_unused_1493_ = lean_ctor_get(v_l_1470_, 4);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_l_1470_, 3);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_l_1470_, 0);
lean_dec(v_unused_1495_);
v___x_1480_ = v_l_1470_;
v_isShared_1481_ = v_isSharedCheck_1492_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_v_1478_);
lean_inc(v_k_1477_);
lean_dec(v_l_1470_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1492_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1471_, 2);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 4, v_r_1471_);
lean_ctor_set(v___x_1480_, 3, v_r_1471_);
lean_ctor_set(v___x_1480_, 2, v_v_1377_);
lean_ctor_set(v___x_1480_, 1, v_k_1376_);
lean_ctor_set(v___x_1480_, 0, v___x_1386_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_r_1471_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v_r_1471_);
v___x_1484_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
lean_inc(v_r_1471_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 3, v_r_1471_);
lean_ctor_set(v___x_1475_, 0, v___x_1386_);
v___x_1486_ = v___x_1475_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1472_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1473_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_r_1471_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_r_1471_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1488_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 4, v___x_1486_);
lean_ctor_set(v___x_1381_, 3, v___x_1484_);
lean_ctor_set(v___x_1381_, 2, v_v_1478_);
lean_ctor_set(v___x_1381_, 1, v_k_1477_);
lean_ctor_set(v___x_1381_, 0, v___x_1482_);
v___x_1488_ = v___x_1381_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
}
else
{
lean_object* v_r_1499_; 
v_r_1499_ = lean_ctor_get(v_impl_1385_, 4);
lean_inc(v_r_1499_);
if (lean_obj_tag(v_r_1499_) == 0)
{
lean_object* v_k_1500_; lean_object* v_v_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1512_; 
v_k_1500_ = lean_ctor_get(v_impl_1385_, 1);
v_v_1501_ = lean_ctor_get(v_impl_1385_, 2);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_impl_1385_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; lean_object* v_unused_1514_; lean_object* v_unused_1515_; 
v_unused_1513_ = lean_ctor_get(v_impl_1385_, 4);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_impl_1385_, 3);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v_impl_1385_, 0);
lean_dec(v_unused_1515_);
v___x_1503_ = v_impl_1385_;
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_v_1501_);
lean_inc(v_k_1500_);
lean_dec(v_impl_1385_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1512_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_unsigned_to_nat(3u);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v_l_1470_);
lean_ctor_set(v___x_1503_, 2, v_v_1377_);
lean_ctor_set(v___x_1503_, 1, v_k_1376_);
lean_ctor_set(v___x_1503_, 0, v___x_1386_);
v___x_1507_ = v___x_1503_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1511_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1511_, 3, v_l_1470_);
lean_ctor_set(v_reuseFailAlloc_1511_, 4, v_l_1470_);
v___x_1507_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 4, v_r_1499_);
lean_ctor_set(v___x_1381_, 3, v___x_1507_);
lean_ctor_set(v___x_1381_, 2, v_v_1501_);
lean_ctor_set(v___x_1381_, 1, v_k_1500_);
lean_ctor_set(v___x_1381_, 0, v___x_1505_);
v___x_1509_ = v___x_1381_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_k_1500_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_v_1501_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_r_1499_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1516_ = lean_unsigned_to_nat(2u);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 4, v_impl_1385_);
lean_ctor_set(v___x_1381_, 3, v_r_1499_);
lean_ctor_set(v___x_1381_, 0, v___x_1516_);
v___x_1518_ = v___x_1381_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_r_1499_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_impl_1385_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
else
{
lean_object* v___x_1521_; 
lean_dec(v_v_1377_);
lean_dec(v_k_1376_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 2, v_v_1373_);
lean_ctor_set(v___x_1381_, 1, v_k_1372_);
v___x_1521_ = v___x_1381_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_size_1375_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_k_1372_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_v_1373_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v_l_1378_);
lean_ctor_set(v_reuseFailAlloc_1522_, 4, v_r_1379_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
else
{
lean_object* v_impl_1523_; lean_object* v___x_1524_; 
lean_dec(v_size_1375_);
v_impl_1523_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1372_, v_v_1373_, v_l_1378_);
v___x_1524_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1379_) == 0)
{
lean_object* v_size_1525_; lean_object* v_size_1526_; lean_object* v_k_1527_; lean_object* v_v_1528_; lean_object* v_l_1529_; lean_object* v_r_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v_size_1525_ = lean_ctor_get(v_r_1379_, 0);
v_size_1526_ = lean_ctor_get(v_impl_1523_, 0);
lean_inc(v_size_1526_);
v_k_1527_ = lean_ctor_get(v_impl_1523_, 1);
lean_inc(v_k_1527_);
v_v_1528_ = lean_ctor_get(v_impl_1523_, 2);
lean_inc(v_v_1528_);
v_l_1529_ = lean_ctor_get(v_impl_1523_, 3);
lean_inc(v_l_1529_);
v_r_1530_ = lean_ctor_get(v_impl_1523_, 4);
lean_inc(v_r_1530_);
v___x_1531_ = lean_unsigned_to_nat(3u);
v___x_1532_ = lean_nat_mul(v___x_1531_, v_size_1525_);
v___x_1533_ = lean_nat_dec_lt(v___x_1532_, v_size_1526_);
lean_dec(v___x_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
lean_dec(v_r_1530_);
lean_dec(v_l_1529_);
lean_dec(v_v_1528_);
lean_dec(v_k_1527_);
v___x_1534_ = lean_nat_add(v___x_1524_, v_size_1526_);
lean_dec(v_size_1526_);
v___x_1535_ = lean_nat_add(v___x_1534_, v_size_1525_);
lean_dec(v___x_1534_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 3, v_impl_1523_);
lean_ctor_set(v___x_1381_, 0, v___x_1535_);
v___x_1537_ = v___x_1381_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_impl_1523_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_r_1379_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
else
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1604_; 
v_isSharedCheck_1604_ = !lean_is_exclusive(v_impl_1523_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; 
v_unused_1605_ = lean_ctor_get(v_impl_1523_, 4);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_impl_1523_, 3);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_impl_1523_, 2);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_impl_1523_, 1);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_impl_1523_, 0);
lean_dec(v_unused_1609_);
v___x_1540_ = v_impl_1523_;
v_isShared_1541_ = v_isSharedCheck_1604_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v_impl_1523_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1604_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_size_1542_; lean_object* v_size_1543_; lean_object* v_k_1544_; lean_object* v_v_1545_; lean_object* v_l_1546_; lean_object* v_r_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_size_1542_ = lean_ctor_get(v_l_1529_, 0);
v_size_1543_ = lean_ctor_get(v_r_1530_, 0);
v_k_1544_ = lean_ctor_get(v_r_1530_, 1);
v_v_1545_ = lean_ctor_get(v_r_1530_, 2);
v_l_1546_ = lean_ctor_get(v_r_1530_, 3);
v_r_1547_ = lean_ctor_get(v_r_1530_, 4);
v___x_1548_ = lean_unsigned_to_nat(2u);
v___x_1549_ = lean_nat_mul(v___x_1548_, v_size_1542_);
v___x_1550_ = lean_nat_dec_lt(v_size_1543_, v___x_1549_);
lean_dec(v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1579_; 
lean_inc(v_r_1547_);
lean_inc(v_l_1546_);
lean_inc(v_v_1545_);
lean_inc(v_k_1544_);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_r_1530_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; lean_object* v_unused_1581_; lean_object* v_unused_1582_; lean_object* v_unused_1583_; lean_object* v_unused_1584_; 
v_unused_1580_ = lean_ctor_get(v_r_1530_, 4);
lean_dec(v_unused_1580_);
v_unused_1581_ = lean_ctor_get(v_r_1530_, 3);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_r_1530_, 2);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_r_1530_, 1);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_r_1530_, 0);
lean_dec(v_unused_1584_);
v___x_1552_ = v_r_1530_;
v_isShared_1553_ = v_isSharedCheck_1579_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v_r_1530_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1579_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___x_1567_; lean_object* v___y_1569_; 
v___x_1554_ = lean_nat_add(v___x_1524_, v_size_1526_);
lean_dec(v_size_1526_);
v___x_1555_ = lean_nat_add(v___x_1554_, v_size_1525_);
lean_dec(v___x_1554_);
v___x_1567_ = lean_nat_add(v___x_1524_, v_size_1542_);
if (lean_obj_tag(v_l_1546_) == 0)
{
lean_object* v_size_1577_; 
v_size_1577_ = lean_ctor_get(v_l_1546_, 0);
lean_inc(v_size_1577_);
v___y_1569_ = v_size_1577_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_unsigned_to_nat(0u);
v___y_1569_ = v___x_1578_;
goto v___jp_1568_;
}
v___jp_1556_:
{
lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1560_ = lean_nat_add(v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec(v___y_1558_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 4, v_r_1379_);
lean_ctor_set(v___x_1552_, 3, v_r_1547_);
lean_ctor_set(v___x_1552_, 2, v_v_1377_);
lean_ctor_set(v___x_1552_, 1, v_k_1376_);
lean_ctor_set(v___x_1552_, 0, v___x_1560_);
v___x_1562_ = v___x_1552_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v_r_1547_);
lean_ctor_set(v_reuseFailAlloc_1566_, 4, v_r_1379_);
v___x_1562_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1564_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 4, v___x_1562_);
lean_ctor_set(v___x_1540_, 3, v___y_1557_);
lean_ctor_set(v___x_1540_, 2, v_v_1545_);
lean_ctor_set(v___x_1540_, 1, v_k_1544_);
lean_ctor_set(v___x_1540_, 0, v___x_1555_);
v___x_1564_ = v___x_1540_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_k_1544_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_v_1545_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v___y_1557_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
v___jp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1570_ = lean_nat_add(v___x_1567_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec(v___x_1567_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 4, v_l_1546_);
lean_ctor_set(v___x_1381_, 3, v_l_1529_);
lean_ctor_set(v___x_1381_, 2, v_v_1528_);
lean_ctor_set(v___x_1381_, 1, v_k_1527_);
lean_ctor_set(v___x_1381_, 0, v___x_1570_);
v___x_1572_ = v___x_1381_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_k_1527_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v_v_1528_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v_l_1529_);
lean_ctor_set(v_reuseFailAlloc_1576_, 4, v_l_1546_);
v___x_1572_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_nat_add(v___x_1524_, v_size_1525_);
if (lean_obj_tag(v_r_1547_) == 0)
{
lean_object* v_size_1574_; 
v_size_1574_ = lean_ctor_get(v_r_1547_, 0);
lean_inc(v_size_1574_);
v___y_1557_ = v___x_1572_;
v___y_1558_ = v___x_1573_;
v___y_1559_ = v_size_1574_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_unsigned_to_nat(0u);
v___y_1557_ = v___x_1572_;
v___y_1558_ = v___x_1573_;
v___y_1559_ = v___x_1575_;
goto v___jp_1556_;
}
}
}
}
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
lean_del_object(v___x_1381_);
v___x_1585_ = lean_nat_add(v___x_1524_, v_size_1526_);
lean_dec(v_size_1526_);
v___x_1586_ = lean_nat_add(v___x_1585_, v_size_1525_);
lean_dec(v___x_1585_);
v___x_1587_ = lean_nat_add(v___x_1524_, v_size_1525_);
v___x_1588_ = lean_nat_add(v___x_1587_, v_size_1543_);
lean_dec(v___x_1587_);
lean_inc_ref(v_r_1379_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 4, v_r_1379_);
lean_ctor_set(v___x_1540_, 3, v_r_1530_);
lean_ctor_set(v___x_1540_, 2, v_v_1377_);
lean_ctor_set(v___x_1540_, 1, v_k_1376_);
lean_ctor_set(v___x_1540_, 0, v___x_1588_);
v___x_1590_ = v___x_1540_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_r_1530_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_r_1379_);
v___x_1590_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_isSharedCheck_1597_ = !lean_is_exclusive(v_r_1379_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; lean_object* v_unused_1602_; 
v_unused_1598_ = lean_ctor_get(v_r_1379_, 4);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_r_1379_, 3);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_r_1379_, 2);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_r_1379_, 1);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_r_1379_, 0);
lean_dec(v_unused_1602_);
v___x_1592_ = v_r_1379_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v_r_1379_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 4, v___x_1590_);
lean_ctor_set(v___x_1592_, 3, v_l_1529_);
lean_ctor_set(v___x_1592_, 2, v_v_1528_);
lean_ctor_set(v___x_1592_, 1, v_k_1527_);
lean_ctor_set(v___x_1592_, 0, v___x_1586_);
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_k_1527_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_v_1528_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_l_1529_);
lean_ctor_set(v_reuseFailAlloc_1596_, 4, v___x_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1610_; 
v_l_1610_ = lean_ctor_get(v_impl_1523_, 3);
lean_inc(v_l_1610_);
if (lean_obj_tag(v_l_1610_) == 0)
{
lean_object* v_r_1611_; lean_object* v_k_1612_; lean_object* v_v_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1624_; 
v_r_1611_ = lean_ctor_get(v_impl_1523_, 4);
v_k_1612_ = lean_ctor_get(v_impl_1523_, 1);
v_v_1613_ = lean_ctor_get(v_impl_1523_, 2);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_impl_1523_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; lean_object* v_unused_1626_; 
v_unused_1625_ = lean_ctor_get(v_impl_1523_, 3);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_impl_1523_, 0);
lean_dec(v_unused_1626_);
v___x_1615_ = v_impl_1523_;
v_isShared_1616_ = v_isSharedCheck_1624_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_r_1611_);
lean_inc(v_v_1613_);
lean_inc(v_k_1612_);
lean_dec(v_impl_1523_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1624_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1617_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1611_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 3, v_r_1611_);
lean_ctor_set(v___x_1615_, 2, v_v_1377_);
lean_ctor_set(v___x_1615_, 1, v_k_1376_);
lean_ctor_set(v___x_1615_, 0, v___x_1524_);
v___x_1619_ = v___x_1615_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_r_1611_);
lean_ctor_set(v_reuseFailAlloc_1623_, 4, v_r_1611_);
v___x_1619_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 4, v___x_1619_);
lean_ctor_set(v___x_1381_, 3, v_l_1610_);
lean_ctor_set(v___x_1381_, 2, v_v_1613_);
lean_ctor_set(v___x_1381_, 1, v_k_1612_);
lean_ctor_set(v___x_1381_, 0, v___x_1617_);
v___x_1621_ = v___x_1381_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1617_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_k_1612_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_v_1613_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v_l_1610_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_r_1627_; 
v_r_1627_ = lean_ctor_get(v_impl_1523_, 4);
lean_inc(v_r_1627_);
if (lean_obj_tag(v_r_1627_) == 0)
{
lean_object* v_k_1628_; lean_object* v_v_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1652_; 
v_k_1628_ = lean_ctor_get(v_impl_1523_, 1);
v_v_1629_ = lean_ctor_get(v_impl_1523_, 2);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_impl_1523_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; lean_object* v_unused_1654_; lean_object* v_unused_1655_; 
v_unused_1653_ = lean_ctor_get(v_impl_1523_, 4);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_impl_1523_, 3);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_impl_1523_, 0);
lean_dec(v_unused_1655_);
v___x_1631_ = v_impl_1523_;
v_isShared_1632_ = v_isSharedCheck_1652_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_v_1629_);
lean_inc(v_k_1628_);
lean_dec(v_impl_1523_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1652_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v_k_1633_; lean_object* v_v_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1648_; 
v_k_1633_ = lean_ctor_get(v_r_1627_, 1);
v_v_1634_ = lean_ctor_get(v_r_1627_, 2);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_r_1627_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; lean_object* v_unused_1650_; lean_object* v_unused_1651_; 
v_unused_1649_ = lean_ctor_get(v_r_1627_, 4);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_r_1627_, 3);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_r_1627_, 0);
lean_dec(v_unused_1651_);
v___x_1636_ = v_r_1627_;
v_isShared_1637_ = v_isSharedCheck_1648_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_v_1634_);
lean_inc(v_k_1633_);
lean_dec(v_r_1627_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1648_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1638_ = lean_unsigned_to_nat(3u);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 4, v_l_1610_);
lean_ctor_set(v___x_1636_, 3, v_l_1610_);
lean_ctor_set(v___x_1636_, 2, v_v_1629_);
lean_ctor_set(v___x_1636_, 1, v_k_1628_);
lean_ctor_set(v___x_1636_, 0, v___x_1524_);
v___x_1640_ = v___x_1636_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_k_1628_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_v_1629_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_l_1610_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_l_1610_);
v___x_1640_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1642_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 4, v_l_1610_);
lean_ctor_set(v___x_1631_, 2, v_v_1377_);
lean_ctor_set(v___x_1631_, 1, v_k_1376_);
lean_ctor_set(v___x_1631_, 0, v___x_1524_);
v___x_1642_ = v___x_1631_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_l_1610_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v_l_1610_);
v___x_1642_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1644_; 
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 4, v___x_1642_);
lean_ctor_set(v___x_1381_, 3, v___x_1640_);
lean_ctor_set(v___x_1381_, 2, v_v_1634_);
lean_ctor_set(v___x_1381_, 1, v_k_1633_);
lean_ctor_set(v___x_1381_, 0, v___x_1638_);
v___x_1644_ = v___x_1381_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_k_1633_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_v_1634_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1645_, 4, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1656_ = lean_unsigned_to_nat(2u);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 4, v_r_1627_);
lean_ctor_set(v___x_1381_, 3, v_impl_1523_);
lean_ctor_set(v___x_1381_, 0, v___x_1656_);
v___x_1658_ = v___x_1381_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1659_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1659_, 3, v_impl_1523_);
lean_ctor_set(v_reuseFailAlloc_1659_, 4, v_r_1627_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_unsigned_to_nat(1u);
v___x_1662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
lean_ctor_set(v___x_1662_, 1, v_k_1372_);
lean_ctor_set(v___x_1662_, 2, v_v_1373_);
lean_ctor_set(v___x_1662_, 3, v_t_1374_);
lean_ctor_set(v___x_1662_, 4, v_t_1374_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(lean_object* v_k_1663_, lean_object* v_x_1664_){
_start:
{
if (lean_obj_tag(v_x_1664_) == 0)
{
lean_object* v___x_1665_; 
lean_dec_ref(v_k_1663_);
v___x_1665_ = lean_box(0);
return v___x_1665_;
}
else
{
lean_object* v_val_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_val_1666_ = lean_ctor_get(v_x_1664_, 0);
lean_inc(v_val_1666_);
v___x_1667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_k_1663_);
lean_ctor_set(v___x_1667_, 1, v_val_1666_);
v___x_1668_ = lean_box(0);
v___x_1669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4___boxed(lean_object* v_k_1670_, lean_object* v_x_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v_k_1670_, v_x_1671_);
lean_dec(v_x_1671_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(size_t v_sz_1673_, size_t v_i_1674_, lean_object* v_bs_1675_){
_start:
{
uint8_t v___x_1676_; 
v___x_1676_ = lean_usize_dec_lt(v_i_1674_, v_sz_1673_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_bs_1675_);
return v___x_1677_;
}
else
{
lean_object* v_v_1678_; lean_object* v___x_1679_; 
v_v_1678_ = lean_array_uget_borrowed(v_bs_1675_, v_i_1674_);
lean_inc(v_v_1678_);
v___x_1679_ = l_Lean_Lsp_instFromJsonCallHierarchyIncomingCall_fromJson(v_v_1678_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec_ref(v_bs_1675_);
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1689_; lean_object* v_bs_x27_1690_; size_t v___x_1691_; size_t v___x_1692_; lean_object* v___x_1693_; 
v_a_1688_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1679_);
v___x_1689_ = lean_unsigned_to_nat(0u);
v_bs_x27_1690_ = lean_array_uset(v_bs_1675_, v_i_1674_, v___x_1689_);
v___x_1691_ = ((size_t)1ULL);
v___x_1692_ = lean_usize_add(v_i_1674_, v___x_1691_);
v___x_1693_ = lean_array_uset(v_bs_x27_1690_, v_i_1674_, v_a_1688_);
v_i_1674_ = v___x_1692_;
v_bs_1675_ = v___x_1693_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_sz_1695_, lean_object* v_i_1696_, lean_object* v_bs_1697_){
_start:
{
size_t v_sz_boxed_1698_; size_t v_i_boxed_1699_; lean_object* v_res_1700_; 
v_sz_boxed_1698_ = lean_unbox_usize(v_sz_1695_);
lean_dec(v_sz_1695_);
v_i_boxed_1699_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_boxed_1698_, v_i_boxed_1699_, v_bs_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(lean_object* v_x_1701_){
_start:
{
if (lean_obj_tag(v_x_1701_) == 4)
{
lean_object* v_elems_1702_; size_t v_sz_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
v_elems_1702_ = lean_ctor_get(v_x_1701_, 0);
lean_inc_ref(v_elems_1702_);
lean_dec_ref(v_x_1701_);
v_sz_1703_ = lean_array_size(v_elems_1702_);
v___x_1704_ = ((size_t)0ULL);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_1703_, v___x_1704_, v_elems_1702_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1706_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1707_ = lean_unsigned_to_nat(80u);
v___x_1708_ = l_Lean_Json_pretty(v_x_1701_, v___x_1707_);
v___x_1709_ = lean_string_append(v___x_1706_, v___x_1708_);
lean_dec_ref(v___x_1708_);
v___x_1710_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1711_ = lean_string_append(v___x_1709_, v___x_1710_);
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(lean_object* v_x_1715_){
_start:
{
if (lean_obj_tag(v_x_1715_) == 0)
{
lean_object* v___x_1716_; 
v___x_1716_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0));
return v___x_1716_;
}
else
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(v_x_1715_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
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
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
v_a_1726_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1728_ = v___x_1717_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1717_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_a_1726_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1730_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(lean_object* v_expectedID_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Lsp_Ipc_stdout(v_a_1736_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1882_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1882_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1882_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_IO_FS_Stream_readLspMessage(v_a_1739_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1873_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1873_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1873_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___y_1749_; lean_object* v___y_1750_; 
switch(lean_obj_tag(v_a_1744_))
{
case 2:
{
lean_object* v_id_1756_; lean_object* v_result_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1801_; 
v_id_1756_ = lean_ctor_get(v_a_1744_, 0);
v_result_1757_ = lean_ctor_get(v_a_1744_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_a_1744_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1759_ = v_a_1744_;
v_isShared_1760_ = v_isSharedCheck_1801_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_result_1757_);
lean_inc(v_id_1756_);
lean_dec(v_a_1744_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1801_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
uint8_t v___x_1761_; 
v___x_1761_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_1756_, v_expectedID_1735_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___y_1764_; 
lean_del_object(v___x_1759_);
lean_dec(v_result_1757_);
lean_del_object(v___x_1741_);
v___x_1762_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_1735_))
{
case 0:
{
lean_object* v_s_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_s_1775_ = lean_ctor_get(v_expectedID_1735_, 0);
lean_inc_ref(v_s_1775_);
lean_dec_ref(v_expectedID_1735_);
v___x_1776_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1777_ = lean_string_append(v___x_1776_, v_s_1775_);
lean_dec_ref(v_s_1775_);
v___x_1778_ = lean_string_append(v___x_1777_, v___x_1776_);
v___y_1764_ = v___x_1778_;
goto v___jp_1763_;
}
case 1:
{
lean_object* v_n_1779_; lean_object* v___x_1780_; 
v_n_1779_ = lean_ctor_get(v_expectedID_1735_, 0);
lean_inc_ref(v_n_1779_);
lean_dec_ref(v_expectedID_1735_);
v___x_1780_ = l_Lean_JsonNumber_toString(v_n_1779_);
v___y_1764_ = v___x_1780_;
goto v___jp_1763_;
}
default: 
{
lean_object* v___x_1781_; 
v___x_1781_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1764_ = v___x_1781_;
goto v___jp_1763_;
}
}
v___jp_1763_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1765_ = lean_string_append(v___x_1762_, v___y_1764_);
lean_dec_ref(v___y_1764_);
v___x_1766_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_1767_ = lean_string_append(v___x_1765_, v___x_1766_);
switch(lean_obj_tag(v_id_1756_))
{
case 0:
{
lean_object* v_s_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_s_1768_ = lean_ctor_get(v_id_1756_, 0);
lean_inc_ref(v_s_1768_);
lean_dec_ref(v_id_1756_);
v___x_1769_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1770_ = lean_string_append(v___x_1769_, v_s_1768_);
lean_dec_ref(v_s_1768_);
v___x_1771_ = lean_string_append(v___x_1770_, v___x_1769_);
v___y_1749_ = v___x_1767_;
v___y_1750_ = v___x_1771_;
goto v___jp_1748_;
}
case 1:
{
lean_object* v_n_1772_; lean_object* v___x_1773_; 
v_n_1772_ = lean_ctor_get(v_id_1756_, 0);
lean_inc_ref(v_n_1772_);
lean_dec_ref(v_id_1756_);
v___x_1773_ = l_Lean_JsonNumber_toString(v_n_1772_);
v___y_1749_ = v___x_1767_;
v___y_1750_ = v___x_1773_;
goto v___jp_1748_;
}
default: 
{
lean_object* v___x_1774_; 
v___x_1774_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1749_ = v___x_1767_;
v___y_1750_ = v___x_1774_;
goto v___jp_1748_;
}
}
}
}
else
{
lean_object* v___x_1782_; 
lean_dec(v_id_1756_);
lean_del_object(v___x_1746_);
lean_inc(v_result_1757_);
v___x_1782_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(v_result_1757_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
lean_del_object(v___x_1759_);
lean_dec(v_expectedID_1735_);
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_1785_ = l_Lean_Json_compress(v_result_1757_);
v___x_1786_ = lean_string_append(v___x_1784_, v___x_1785_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_1788_ = lean_string_append(v___x_1786_, v___x_1787_);
v___x_1789_ = lean_string_append(v___x_1788_, v_a_1783_);
lean_dec(v_a_1783_);
v___x_1790_ = lean_mk_io_user_error(v___x_1789_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 1);
lean_ctor_set(v___x_1741_, 0, v___x_1790_);
v___x_1792_ = v___x_1741_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; 
lean_dec(v_result_1757_);
v_a_1794_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1794_);
lean_dec_ref(v___x_1782_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set_tag(v___x_1759_, 0);
lean_ctor_set(v___x_1759_, 1, v_a_1794_);
lean_ctor_set(v___x_1759_, 0, v_expectedID_1735_);
v___x_1796_ = v___x_1759_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_expectedID_1735_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_a_1794_);
v___x_1796_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1798_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1796_);
v___x_1798_ = v___x_1741_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
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
}
}
case 3:
{
lean_object* v_id_1802_; uint8_t v_code_1803_; lean_object* v_message_1804_; lean_object* v_data_x3f_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___x_1837_; lean_object* v___y_1839_; 
lean_del_object(v___x_1746_);
lean_dec(v_expectedID_1735_);
v_id_1802_ = lean_ctor_get(v_a_1744_, 0);
lean_inc(v_id_1802_);
v_code_1803_ = lean_ctor_get_uint8(v_a_1744_, sizeof(void*)*3);
v_message_1804_ = lean_ctor_get(v_a_1744_, 1);
lean_inc_ref(v_message_1804_);
v_data_x3f_1805_ = lean_ctor_get(v_a_1744_, 2);
lean_inc(v_data_x3f_1805_);
lean_dec_ref(v_a_1744_);
v___x_1806_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_1807_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_1837_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_1802_))
{
case 0:
{
lean_object* v_s_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v_s_1855_ = lean_ctor_get(v_id_1802_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_id_1802_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v_id_1802_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_s_1855_);
lean_dec(v_id_1802_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 3);
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_s_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
v___y_1839_ = v___x_1860_;
goto v___jp_1838_;
}
}
}
case 1:
{
lean_object* v_n_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
v_n_1863_ = lean_ctor_get(v_id_1802_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_id_1802_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v_id_1802_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_n_1863_);
lean_dec(v_id_1802_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set_tag(v___x_1865_, 2);
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_n_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
v___y_1839_ = v___x_1868_;
goto v___jp_1838_;
}
}
}
default: 
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_box(0);
v___y_1839_ = v___x_1871_;
goto v___jp_1838_;
}
}
v___jp_1808_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___y_1811_);
lean_ctor_set(v___x_1813_, 1, v___y_1812_);
v___x_1814_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_1815_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_message_1804_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1813_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_1821_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_1820_, v_data_x3f_1805_);
lean_dec(v_data_x3f_1805_);
v___x_1822_ = l_List_appendTR___redArg(v___x_1819_, v___x_1821_);
v___x_1823_ = l_Lean_Json_mkObj(v___x_1822_);
lean_inc_ref(v___y_1810_);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___y_1810_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v___x_1817_);
v___x_1826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___y_1809_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1807_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = l_Lean_Json_mkObj(v___x_1827_);
v___x_1829_ = l_Lean_Json_compress(v___x_1828_);
v___x_1830_ = lean_string_append(v___x_1806_, v___x_1829_);
lean_dec_ref(v___x_1829_);
v___x_1831_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1832_ = lean_string_append(v___x_1830_, v___x_1831_);
v___x_1833_ = lean_mk_io_user_error(v___x_1832_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 1);
lean_ctor_set(v___x_1741_, 0, v___x_1833_);
v___x_1835_ = v___x_1741_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
v___jp_1838_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1837_);
lean_ctor_set(v___x_1840_, 1, v___y_1839_);
v___x_1841_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_1842_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_1803_)
{
case 0:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1843_;
goto v___jp_1808_;
}
case 1:
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1844_;
goto v___jp_1808_;
}
case 2:
{
lean_object* v___x_1845_; 
v___x_1845_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1845_;
goto v___jp_1808_;
}
case 3:
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1846_;
goto v___jp_1808_;
}
case 4:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1847_;
goto v___jp_1808_;
}
case 5:
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1848_;
goto v___jp_1808_;
}
case 6:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1849_;
goto v___jp_1808_;
}
case 7:
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1850_;
goto v___jp_1808_;
}
case 8:
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1851_;
goto v___jp_1808_;
}
case 9:
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1852_;
goto v___jp_1808_;
}
case 10:
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1853_;
goto v___jp_1808_;
}
default: 
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_1809_ = v___x_1840_;
v___y_1810_ = v___x_1841_;
v___y_1811_ = v___x_1842_;
v___y_1812_ = v___x_1854_;
goto v___jp_1808_;
}
}
}
}
default: 
{
lean_del_object(v___x_1746_);
lean_dec(v_a_1744_);
lean_del_object(v___x_1741_);
goto _start;
}
}
v___jp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v___x_1751_ = lean_string_append(v___y_1749_, v___y_1750_);
lean_dec_ref(v___y_1750_);
v___x_1752_ = lean_mk_io_user_error(v___x_1751_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set_tag(v___x_1746_, 1);
lean_ctor_set(v___x_1746_, 0, v___x_1752_);
v___x_1754_ = v___x_1746_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_del_object(v___x_1741_);
lean_dec(v_expectedID_1735_);
v_a_1874_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1743_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1743_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_expectedID_1735_);
v_a_1883_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1738_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1738_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2___boxed(lean_object* v_expectedID_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v_expectedID_1891_, v_a_1892_);
lean_dec_ref(v_a_1892_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(lean_object* v_v_1895_){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = l_Lean_Lsp_instToJsonCallHierarchyIncomingCallsParams_toJson(v_v_1895_);
v___x_1897_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(lean_object* v_h_1898_, lean_object* v_r_1899_){
_start:
{
lean_object* v_id_1901_; lean_object* v_method_1902_; lean_object* v_param_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1923_; 
v_id_1901_ = lean_ctor_get(v_r_1899_, 0);
v_method_1902_ = lean_ctor_get(v_r_1899_, 1);
v_param_1903_ = lean_ctor_get(v_r_1899_, 2);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_r_1899_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1905_ = v_r_1899_;
v_isShared_1906_ = v_isSharedCheck_1923_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_param_1903_);
lean_inc(v_method_1902_);
lean_inc(v_id_1901_);
lean_dec(v_r_1899_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1923_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___y_1908_; lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(v_param_1903_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v___x_1914_; 
lean_dec_ref(v___x_1913_);
v___x_1914_ = lean_box(0);
v___y_1908_ = v___x_1914_;
goto v___jp_1907_;
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1913_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1913_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
v___y_1908_ = v___x_1920_;
goto v___jp_1907_;
}
}
}
v___jp_1907_:
{
lean_object* v___x_1910_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 2, v___y_1908_);
v___x_1910_ = v___x_1905_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_id_1901_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_method_1902_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v___y_1908_);
v___x_1910_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_IO_FS_Stream_writeLspMessage(v_h_1898_, v___x_1910_);
return v___x_1911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1___boxed(lean_object* v_h_1924_, lean_object* v_r_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_h_1924_, v_r_1925_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(lean_object* v_r_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v___x_1931_; lean_object* v_a_1932_; lean_object* v___x_1933_; 
v___x_1931_ = l_Lean_Lsp_Ipc_stdin(v_a_1929_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
v___x_1933_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_a_1932_, v_r_1928_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1___boxed(lean_object* v_r_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v_r_1934_, v_a_1935_);
lean_dec_ref(v_a_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(lean_object* v_k_1938_, lean_object* v_t_1939_){
_start:
{
if (lean_obj_tag(v_t_1939_) == 0)
{
lean_object* v_k_1940_; lean_object* v_l_1941_; lean_object* v_r_1942_; uint8_t v___x_1943_; 
v_k_1940_ = lean_ctor_get(v_t_1939_, 1);
v_l_1941_ = lean_ctor_get(v_t_1939_, 3);
v_r_1942_ = lean_ctor_get(v_t_1939_, 4);
v___x_1943_ = lean_string_dec_lt(v_k_1938_, v_k_1940_);
if (v___x_1943_ == 0)
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_string_dec_eq(v_k_1938_, v_k_1940_);
if (v___x_1944_ == 0)
{
v_t_1939_ = v_r_1942_;
goto _start;
}
else
{
return v___x_1944_;
}
}
else
{
v_t_1939_ = v_l_1941_;
goto _start;
}
}
else
{
uint8_t v___x_1947_; 
v___x_1947_ = 0;
return v___x_1947_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg___boxed(lean_object* v_k_1948_, lean_object* v_t_1949_){
_start:
{
uint8_t v_res_1950_; lean_object* v_r_1951_; 
v_res_1950_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_1948_, v_t_1949_);
lean_dec(v_t_1949_);
lean_dec_ref(v_k_1948_);
v_r_1951_ = lean_box(v_res_1950_);
return v_r_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(lean_object* v_requestNo_1959_, lean_object* v_item_1960_, lean_object* v_fromRanges_1961_, lean_object* v_visited_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_name_1965_; uint8_t v___x_1966_; 
v_name_1965_ = lean_ctor_get(v_item_1960_, 0);
v___x_1966_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_1965_, v_visited_1962_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_inc(v_requestNo_1959_);
v___x_1967_ = l_Lean_JsonNumber_fromNat(v_requestNo_1959_);
v___x_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
v___x_1969_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_1960_);
lean_inc_ref(v___x_1968_);
v___x_1970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
lean_ctor_set(v___x_1970_, 2, v_item_1960_);
v___x_1971_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v___x_1970_, v_a_1963_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v___x_1972_; 
lean_dec_ref(v___x_1971_);
v___x_1972_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v___x_1968_, v_a_1963_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_2010_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref(v___x_1972_);
if (v___x_1966_ == 0)
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_box(0);
lean_inc_ref(v_name_1965_);
v___x_2017_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_1965_, v___x_2016_, v_visited_1962_);
v___y_2010_ = v___x_2017_;
goto v___jp_2009_;
}
else
{
v___y_2010_ = v_visited_1962_;
goto v___jp_2009_;
}
v___jp_1974_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; size_t v_sz_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1978_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___y_1975_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
v_sz_1980_ = lean_array_size(v___y_1977_);
v___x_1981_ = ((size_t)0ULL);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___y_1976_, v___y_1977_, v_sz_1980_, v___x_1981_, v___x_1979_, v_a_1963_);
lean_dec_ref(v___y_1977_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2000_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_2000_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2000_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_fst_1987_; lean_object* v_snd_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1999_; 
v_fst_1987_ = lean_ctor_get(v_a_1983_, 0);
v_snd_1988_ = lean_ctor_get(v_a_1983_, 1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_a_1983_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1990_ = v_a_1983_;
v_isShared_1991_ = v_isSharedCheck_1999_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_snd_1988_);
lean_inc(v_fst_1987_);
lean_dec(v_a_1983_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1999_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1992_, 0, v_item_1960_);
lean_ctor_set(v___x_1992_, 1, v_fromRanges_1961_);
lean_ctor_set(v___x_1992_, 2, v_snd_1988_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 1, v_fst_1987_);
lean_ctor_set(v___x_1990_, 0, v___x_1992_);
v___x_1994_ = v___x_1990_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_fst_1987_);
v___x_1994_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1996_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_1994_);
v___x_1996_ = v___x_1985_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v_fromRanges_1961_);
lean_dec_ref(v_item_1960_);
v_a_2001_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1982_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1982_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
v___jp_2009_:
{
lean_object* v_result_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_result_2011_ = lean_ctor_get(v_a_1973_, 1);
lean_inc(v_result_2011_);
lean_dec(v_a_1973_);
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = lean_nat_add(v_requestNo_1959_, v___x_2012_);
lean_dec(v_requestNo_1959_);
if (lean_obj_tag(v_result_2011_) == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2));
v___y_1975_ = v___x_2013_;
v___y_1976_ = v___y_2010_;
v___y_1977_ = v___x_2014_;
goto v___jp_1974_;
}
else
{
lean_object* v_val_2015_; 
v_val_2015_ = lean_ctor_get(v_result_2011_, 0);
lean_inc(v_val_2015_);
lean_dec_ref(v_result_2011_);
v___y_1975_ = v___x_2013_;
v___y_1976_ = v___y_2010_;
v___y_1977_ = v_val_2015_;
goto v___jp_1974_;
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_visited_1962_);
lean_dec_ref(v_fromRanges_1961_);
lean_dec_ref(v_item_1960_);
lean_dec(v_requestNo_1959_);
v_a_2018_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_1972_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_1972_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec_ref(v___x_1968_);
lean_dec(v_visited_1962_);
lean_dec_ref(v_fromRanges_1961_);
lean_dec_ref(v_item_1960_);
lean_dec(v_requestNo_1959_);
v_a_2026_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_1971_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_1971_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec(v_visited_1962_);
lean_dec_ref(v_fromRanges_1961_);
v___x_2034_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2035_, 0, v_item_1960_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
lean_ctor_set(v___x_2035_, 2, v___x_2034_);
v___x_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v_requestNo_1959_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(lean_object* v___x_2038_, lean_object* v_as_2039_, size_t v_sz_2040_, size_t v_i_2041_, lean_object* v_b_2042_, lean_object* v___y_2043_){
_start:
{
uint8_t v___x_2045_; 
v___x_2045_ = lean_usize_dec_lt(v_i_2041_, v_sz_2040_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec(v___x_2038_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_b_2042_);
return v___x_2046_;
}
else
{
lean_object* v_fst_2047_; lean_object* v_snd_2048_; lean_object* v_a_2049_; lean_object* v_from_2050_; lean_object* v_fromRanges_2051_; lean_object* v___x_2052_; 
v_fst_2047_ = lean_ctor_get(v_b_2042_, 0);
lean_inc(v_fst_2047_);
v_snd_2048_ = lean_ctor_get(v_b_2042_, 1);
lean_inc(v_snd_2048_);
lean_dec_ref(v_b_2042_);
v_a_2049_ = lean_array_uget_borrowed(v_as_2039_, v_i_2041_);
v_from_2050_ = lean_ctor_get(v_a_2049_, 0);
v_fromRanges_2051_ = lean_ctor_get(v_a_2049_, 1);
lean_inc(v___x_2038_);
lean_inc_ref(v_fromRanges_2051_);
lean_inc_ref(v_from_2050_);
v___x_2052_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2047_, v_from_2050_, v_fromRanges_2051_, v___x_2038_, v___y_2043_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v_fst_2054_; lean_object* v_snd_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2066_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2052_);
v_fst_2054_ = lean_ctor_get(v_a_2053_, 0);
v_snd_2055_ = lean_ctor_get(v_a_2053_, 1);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_a_2053_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2057_ = v_a_2053_;
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_snd_2055_);
lean_inc(v_fst_2054_);
lean_dec(v_a_2053_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2066_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = lean_array_push(v_snd_2048_, v_fst_2054_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v___x_2059_);
lean_ctor_set(v___x_2057_, 0, v_snd_2055_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_snd_2055_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
size_t v___x_2062_; size_t v___x_2063_; 
v___x_2062_ = ((size_t)1ULL);
v___x_2063_ = lean_usize_add(v_i_2041_, v___x_2062_);
v_i_2041_ = v___x_2063_;
v_b_2042_ = v___x_2061_;
goto _start;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_snd_2048_);
lean_dec(v___x_2038_);
v_a_2067_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2052_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2052_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3___boxed(lean_object* v___x_2075_, lean_object* v_as_2076_, lean_object* v_sz_2077_, lean_object* v_i_2078_, lean_object* v_b_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
size_t v_sz_boxed_2082_; size_t v_i_boxed_2083_; lean_object* v_res_2084_; 
v_sz_boxed_2082_ = lean_unbox_usize(v_sz_2077_);
lean_dec(v_sz_2077_);
v_i_boxed_2083_ = lean_unbox_usize(v_i_2078_);
lean_dec(v_i_2078_);
v_res_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___x_2075_, v_as_2076_, v_sz_boxed_2082_, v_i_boxed_2083_, v_b_2079_, v___y_2080_);
lean_dec_ref(v___y_2080_);
lean_dec_ref(v_as_2076_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___boxed(lean_object* v_requestNo_2085_, lean_object* v_item_2086_, lean_object* v_fromRanges_2087_, lean_object* v_visited_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_requestNo_2085_, v_item_2086_, v_fromRanges_2087_, v_visited_2088_, v_a_2089_);
lean_dec_ref(v_a_2089_);
return v_res_2091_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(lean_object* v_00_u03b2_2092_, lean_object* v_k_2093_, lean_object* v_t_2094_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_2093_, v_t_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___boxed(lean_object* v_00_u03b2_2096_, lean_object* v_k_2097_, lean_object* v_t_2098_){
_start:
{
uint8_t v_res_2099_; lean_object* v_r_2100_; 
v_res_2099_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(v_00_u03b2_2096_, v_k_2097_, v_t_2098_);
lean_dec(v_t_2098_);
lean_dec_ref(v_k_2097_);
v_r_2100_ = lean_box(v_res_2099_);
return v_r_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4(lean_object* v_00_u03b2_2101_, lean_object* v_k_2102_, lean_object* v_v_2103_, lean_object* v_t_2104_, lean_object* v_hl_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_2102_, v_v_2103_, v_t_2104_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2107_, size_t v_i_2108_, lean_object* v_bs_2109_){
_start:
{
uint8_t v___x_2110_; 
v___x_2110_ = lean_usize_dec_lt(v_i_2108_, v_sz_2107_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_bs_2109_);
return v___x_2111_;
}
else
{
lean_object* v_v_2112_; lean_object* v___x_2113_; 
v_v_2112_ = lean_array_uget_borrowed(v_bs_2109_, v_i_2108_);
lean_inc(v_v_2112_);
v___x_2113_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v_v_2112_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec_ref(v_bs_2109_);
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2123_; lean_object* v_bs_x27_2124_; size_t v___x_2125_; size_t v___x_2126_; lean_object* v___x_2127_; 
v_a_2122_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2122_);
lean_dec_ref(v___x_2113_);
v___x_2123_ = lean_unsigned_to_nat(0u);
v_bs_x27_2124_ = lean_array_uset(v_bs_2109_, v_i_2108_, v___x_2123_);
v___x_2125_ = ((size_t)1ULL);
v___x_2126_ = lean_usize_add(v_i_2108_, v___x_2125_);
v___x_2127_ = lean_array_uset(v_bs_x27_2124_, v_i_2108_, v_a_2122_);
v_i_2108_ = v___x_2126_;
v_bs_2109_ = v___x_2127_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2129_, lean_object* v_i_2130_, lean_object* v_bs_2131_){
_start:
{
size_t v_sz_boxed_2132_; size_t v_i_boxed_2133_; lean_object* v_res_2134_; 
v_sz_boxed_2132_ = lean_unbox_usize(v_sz_2129_);
lean_dec(v_sz_2129_);
v_i_boxed_2133_ = lean_unbox_usize(v_i_2130_);
lean_dec(v_i_2130_);
v_res_2134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2132_, v_i_boxed_2133_, v_bs_2131_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(lean_object* v_x_2135_){
_start:
{
if (lean_obj_tag(v_x_2135_) == 4)
{
lean_object* v_elems_2136_; size_t v_sz_2137_; size_t v___x_2138_; lean_object* v___x_2139_; 
v_elems_2136_ = lean_ctor_get(v_x_2135_, 0);
lean_inc_ref(v_elems_2136_);
lean_dec_ref(v_x_2135_);
v_sz_2137_ = lean_array_size(v_elems_2136_);
v___x_2138_ = ((size_t)0ULL);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_2137_, v___x_2138_, v_elems_2136_);
return v___x_2139_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2140_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2141_ = lean_unsigned_to_nat(80u);
v___x_2142_ = l_Lean_Json_pretty(v_x_2135_, v___x_2141_);
v___x_2143_ = lean_string_append(v___x_2140_, v___x_2142_);
lean_dec_ref(v___x_2142_);
v___x_2144_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2145_ = lean_string_append(v___x_2143_, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(lean_object* v_x_2149_){
_start:
{
if (lean_obj_tag(v_x_2149_) == 0)
{
lean_object* v___x_2150_; 
v___x_2150_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0));
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(v_x_2149_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2151_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2168_; 
v_a_2160_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2162_ = v___x_2151_;
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2151_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2164_, 0, v_a_2160_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2164_);
v___x_2166_ = v___x_2162_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(lean_object* v_expectedID_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Lsp_Ipc_stdout(v_a_2170_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2316_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2316_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2316_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_IO_FS_Stream_readLspMessage(v_a_2173_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2307_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2307_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2307_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___y_2183_; lean_object* v___y_2184_; 
switch(lean_obj_tag(v_a_2178_))
{
case 2:
{
lean_object* v_id_2190_; lean_object* v_result_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2235_; 
v_id_2190_ = lean_ctor_get(v_a_2178_, 0);
v_result_2191_ = lean_ctor_get(v_a_2178_, 1);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_a_2178_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2193_ = v_a_2178_;
v_isShared_2194_ = v_isSharedCheck_2235_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_result_2191_);
lean_inc(v_id_2190_);
lean_dec(v_a_2178_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2235_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
uint8_t v___x_2195_; 
v___x_2195_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2190_, v_expectedID_2169_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___y_2198_; 
lean_del_object(v___x_2193_);
lean_dec(v_result_2191_);
lean_del_object(v___x_2175_);
v___x_2196_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2169_))
{
case 0:
{
lean_object* v_s_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_s_2209_ = lean_ctor_get(v_expectedID_2169_, 0);
lean_inc_ref(v_s_2209_);
lean_dec_ref(v_expectedID_2169_);
v___x_2210_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2211_ = lean_string_append(v___x_2210_, v_s_2209_);
lean_dec_ref(v_s_2209_);
v___x_2212_ = lean_string_append(v___x_2211_, v___x_2210_);
v___y_2198_ = v___x_2212_;
goto v___jp_2197_;
}
case 1:
{
lean_object* v_n_2213_; lean_object* v___x_2214_; 
v_n_2213_ = lean_ctor_get(v_expectedID_2169_, 0);
lean_inc_ref(v_n_2213_);
lean_dec_ref(v_expectedID_2169_);
v___x_2214_ = l_Lean_JsonNumber_toString(v_n_2213_);
v___y_2198_ = v___x_2214_;
goto v___jp_2197_;
}
default: 
{
lean_object* v___x_2215_; 
v___x_2215_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2198_ = v___x_2215_;
goto v___jp_2197_;
}
}
v___jp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = lean_string_append(v___x_2196_, v___y_2198_);
lean_dec_ref(v___y_2198_);
v___x_2200_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2201_ = lean_string_append(v___x_2199_, v___x_2200_);
switch(lean_obj_tag(v_id_2190_))
{
case 0:
{
lean_object* v_s_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v_s_2202_ = lean_ctor_get(v_id_2190_, 0);
lean_inc_ref(v_s_2202_);
lean_dec_ref(v_id_2190_);
v___x_2203_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2204_ = lean_string_append(v___x_2203_, v_s_2202_);
lean_dec_ref(v_s_2202_);
v___x_2205_ = lean_string_append(v___x_2204_, v___x_2203_);
v___y_2183_ = v___x_2201_;
v___y_2184_ = v___x_2205_;
goto v___jp_2182_;
}
case 1:
{
lean_object* v_n_2206_; lean_object* v___x_2207_; 
v_n_2206_ = lean_ctor_get(v_id_2190_, 0);
lean_inc_ref(v_n_2206_);
lean_dec_ref(v_id_2190_);
v___x_2207_ = l_Lean_JsonNumber_toString(v_n_2206_);
v___y_2183_ = v___x_2201_;
v___y_2184_ = v___x_2207_;
goto v___jp_2182_;
}
default: 
{
lean_object* v___x_2208_; 
v___x_2208_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2183_ = v___x_2201_;
v___y_2184_ = v___x_2208_;
goto v___jp_2182_;
}
}
}
}
else
{
lean_object* v___x_2216_; 
lean_dec(v_id_2190_);
lean_del_object(v___x_2180_);
lean_inc(v_result_2191_);
v___x_2216_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(v_result_2191_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2226_; 
lean_del_object(v___x_2193_);
lean_dec(v_expectedID_2169_);
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref(v___x_2216_);
v___x_2218_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2219_ = l_Lean_Json_compress(v_result_2191_);
v___x_2220_ = lean_string_append(v___x_2218_, v___x_2219_);
lean_dec_ref(v___x_2219_);
v___x_2221_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2222_ = lean_string_append(v___x_2220_, v___x_2221_);
v___x_2223_ = lean_string_append(v___x_2222_, v_a_2217_);
lean_dec(v_a_2217_);
v___x_2224_ = lean_mk_io_user_error(v___x_2223_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set_tag(v___x_2175_, 1);
lean_ctor_set(v___x_2175_, 0, v___x_2224_);
v___x_2226_ = v___x_2175_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; 
lean_dec(v_result_2191_);
v_a_2228_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2228_);
lean_dec_ref(v___x_2216_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set_tag(v___x_2193_, 0);
lean_ctor_set(v___x_2193_, 1, v_a_2228_);
lean_ctor_set(v___x_2193_, 0, v_expectedID_2169_);
v___x_2230_ = v___x_2193_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_expectedID_2169_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_a_2228_);
v___x_2230_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2232_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2230_);
v___x_2232_ = v___x_2175_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2236_; uint8_t v_code_2237_; lean_object* v_message_2238_; lean_object* v_data_x3f_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___x_2271_; lean_object* v___y_2273_; 
lean_del_object(v___x_2180_);
lean_dec(v_expectedID_2169_);
v_id_2236_ = lean_ctor_get(v_a_2178_, 0);
lean_inc(v_id_2236_);
v_code_2237_ = lean_ctor_get_uint8(v_a_2178_, sizeof(void*)*3);
v_message_2238_ = lean_ctor_get(v_a_2178_, 1);
lean_inc_ref(v_message_2238_);
v_data_x3f_2239_ = lean_ctor_get(v_a_2178_, 2);
lean_inc(v_data_x3f_2239_);
lean_dec_ref(v_a_2178_);
v___x_2240_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2241_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2271_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2236_))
{
case 0:
{
lean_object* v_s_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
v_s_2289_ = lean_ctor_get(v_id_2236_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_id_2236_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v_id_2236_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_s_2289_);
lean_dec(v_id_2236_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set_tag(v___x_2291_, 3);
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_s_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
v___y_2273_ = v___x_2294_;
goto v___jp_2272_;
}
}
}
case 1:
{
lean_object* v_n_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
v_n_2297_ = lean_ctor_get(v_id_2236_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v_id_2236_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v_id_2236_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_n_2297_);
lean_dec(v_id_2236_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
lean_ctor_set_tag(v___x_2299_, 2);
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_n_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
v___y_2273_ = v___x_2302_;
goto v___jp_2272_;
}
}
}
default: 
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_box(0);
v___y_2273_ = v___x_2305_;
goto v___jp_2272_;
}
}
v___jp_2242_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
lean_inc(v___y_2246_);
lean_inc_ref(v___y_2244_);
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___y_2244_);
lean_ctor_set(v___x_2247_, 1, v___y_2246_);
v___x_2248_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_message_2238_);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2247_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2255_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2254_, v_data_x3f_2239_);
lean_dec(v_data_x3f_2239_);
v___x_2256_ = l_List_appendTR___redArg(v___x_2253_, v___x_2255_);
v___x_2257_ = l_Lean_Json_mkObj(v___x_2256_);
lean_inc_ref(v___y_2245_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___y_2245_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
lean_ctor_set(v___x_2259_, 1, v___x_2251_);
v___x_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___y_2243_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2241_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = l_Lean_Json_mkObj(v___x_2261_);
v___x_2263_ = l_Lean_Json_compress(v___x_2262_);
v___x_2264_ = lean_string_append(v___x_2240_, v___x_2263_);
lean_dec_ref(v___x_2263_);
v___x_2265_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2266_ = lean_string_append(v___x_2264_, v___x_2265_);
v___x_2267_ = lean_mk_io_user_error(v___x_2266_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set_tag(v___x_2175_, 1);
lean_ctor_set(v___x_2175_, 0, v___x_2267_);
v___x_2269_ = v___x_2175_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
v___jp_2272_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2271_);
lean_ctor_set(v___x_2274_, 1, v___y_2273_);
v___x_2275_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2276_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2237_)
{
case 0:
{
lean_object* v___x_2277_; 
v___x_2277_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2277_;
goto v___jp_2242_;
}
case 1:
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2278_;
goto v___jp_2242_;
}
case 2:
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2279_;
goto v___jp_2242_;
}
case 3:
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2280_;
goto v___jp_2242_;
}
case 4:
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2281_;
goto v___jp_2242_;
}
case 5:
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2282_;
goto v___jp_2242_;
}
case 6:
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2283_;
goto v___jp_2242_;
}
case 7:
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2284_;
goto v___jp_2242_;
}
case 8:
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2285_;
goto v___jp_2242_;
}
case 9:
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2286_;
goto v___jp_2242_;
}
case 10:
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2287_;
goto v___jp_2242_;
}
default: 
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2243_ = v___x_2274_;
v___y_2244_ = v___x_2276_;
v___y_2245_ = v___x_2275_;
v___y_2246_ = v___x_2288_;
goto v___jp_2242_;
}
}
}
}
default: 
{
lean_del_object(v___x_2180_);
lean_dec(v_a_2178_);
lean_del_object(v___x_2175_);
goto _start;
}
}
v___jp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2188_; 
v___x_2185_ = lean_string_append(v___y_2183_, v___y_2184_);
lean_dec_ref(v___y_2184_);
v___x_2186_ = lean_mk_io_user_error(v___x_2185_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set_tag(v___x_2180_, 1);
lean_ctor_set(v___x_2180_, 0, v___x_2186_);
v___x_2188_ = v___x_2180_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_del_object(v___x_2175_);
lean_dec(v_expectedID_2169_);
v_a_2308_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2177_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2177_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v_expectedID_2169_);
v_a_2317_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2172_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2172_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1___boxed(lean_object* v_expectedID_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v_expectedID_2325_, v_a_2326_);
lean_dec_ref(v_a_2326_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(lean_object* v_as_2329_, size_t v_sz_2330_, size_t v_i_2331_, lean_object* v_b_2332_, lean_object* v___y_2333_){
_start:
{
uint8_t v___x_2335_; 
v___x_2335_ = lean_usize_dec_lt(v_i_2331_, v_sz_2330_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v_b_2332_);
return v___x_2336_;
}
else
{
lean_object* v_fst_2337_; lean_object* v_snd_2338_; lean_object* v_a_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_fst_2337_ = lean_ctor_get(v_b_2332_, 0);
lean_inc(v_fst_2337_);
v_snd_2338_ = lean_ctor_get(v_b_2332_, 1);
lean_inc(v_snd_2338_);
lean_dec_ref(v_b_2332_);
v_a_2339_ = lean_array_uget_borrowed(v_as_2329_, v_i_2331_);
v___x_2340_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2341_ = lean_box(1);
lean_inc(v_a_2339_);
v___x_2342_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2337_, v_a_2339_, v___x_2340_, v___x_2341_, v___y_2333_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v_fst_2344_; lean_object* v_snd_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2356_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
v_fst_2344_ = lean_ctor_get(v_a_2343_, 0);
v_snd_2345_ = lean_ctor_get(v_a_2343_, 1);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_a_2343_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2347_ = v_a_2343_;
v_isShared_2348_ = v_isSharedCheck_2356_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_snd_2345_);
lean_inc(v_fst_2344_);
lean_dec(v_a_2343_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2356_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2349_ = lean_array_push(v_snd_2338_, v_fst_2344_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 1, v___x_2349_);
lean_ctor_set(v___x_2347_, 0, v_snd_2345_);
v___x_2351_ = v___x_2347_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_snd_2345_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
size_t v___x_2352_; size_t v___x_2353_; 
v___x_2352_ = ((size_t)1ULL);
v___x_2353_ = lean_usize_add(v_i_2331_, v___x_2352_);
v_i_2331_ = v___x_2353_;
v_b_2332_ = v___x_2351_;
goto _start;
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_snd_2338_);
v_a_2357_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2342_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2342_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2___boxed(lean_object* v_as_2365_, lean_object* v_sz_2366_, lean_object* v_i_2367_, lean_object* v_b_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
size_t v_sz_boxed_2371_; size_t v_i_boxed_2372_; lean_object* v_res_2373_; 
v_sz_boxed_2371_ = lean_unbox_usize(v_sz_2366_);
lean_dec(v_sz_2366_);
v_i_boxed_2372_ = lean_unbox_usize(v_i_2367_);
lean_dec(v_i_2367_);
v_res_2373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v_as_2365_, v_sz_boxed_2371_, v_i_boxed_2372_, v_b_2368_, v___y_2369_);
lean_dec_ref(v___y_2369_);
lean_dec_ref(v_as_2365_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(lean_object* v_v_2374_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = l_Lean_Lsp_instToJsonCallHierarchyPrepareParams_toJson(v_v_2374_);
v___x_2376_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(lean_object* v_h_2377_, lean_object* v_r_2378_){
_start:
{
lean_object* v_id_2380_; lean_object* v_method_2381_; lean_object* v_param_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2402_; 
v_id_2380_ = lean_ctor_get(v_r_2378_, 0);
v_method_2381_ = lean_ctor_get(v_r_2378_, 1);
v_param_2382_ = lean_ctor_get(v_r_2378_, 2);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_r_2378_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2384_ = v_r_2378_;
v_isShared_2385_ = v_isSharedCheck_2402_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_param_2382_);
lean_inc(v_method_2381_);
lean_inc(v_id_2380_);
lean_dec(v_r_2378_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2402_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___y_2387_; lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(v_param_2382_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v___x_2393_; 
lean_dec_ref(v___x_2392_);
v___x_2393_ = lean_box(0);
v___y_2387_ = v___x_2393_;
goto v___jp_2386_;
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
v_a_2394_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2392_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2392_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
v___y_2387_ = v___x_2399_;
goto v___jp_2386_;
}
}
}
v___jp_2386_:
{
lean_object* v___x_2389_; 
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 2, v___y_2387_);
v___x_2389_ = v___x_2384_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_id_2380_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_method_2381_);
lean_ctor_set(v_reuseFailAlloc_2391_, 2, v___y_2387_);
v___x_2389_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_IO_FS_Stream_writeLspMessage(v_h_2377_, v___x_2389_);
return v___x_2390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0___boxed(lean_object* v_h_2403_, lean_object* v_r_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_h_2403_, v_r_2404_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(lean_object* v_r_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v___x_2410_; lean_object* v_a_2411_; lean_object* v___x_2412_; 
v___x_2410_ = l_Lean_Lsp_Ipc_stdin(v_a_2408_);
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref(v___x_2410_);
v___x_2412_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_a_2411_, v_r_2407_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0___boxed(lean_object* v_r_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v_r_2413_, v_a_2414_);
lean_dec_ref(v_a_2414_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(lean_object* v_requestNo_2420_, lean_object* v_uri_2421_, lean_object* v_pos_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_inc(v_requestNo_2420_);
v___x_2425_ = l_Lean_JsonNumber_fromNat(v_requestNo_2420_);
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
v___x_2427_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v_uri_2421_);
lean_ctor_set(v___x_2428_, 1, v_pos_2422_);
lean_inc_ref(v___x_2426_);
v___x_2429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2426_);
lean_ctor_set(v___x_2429_, 1, v___x_2427_);
lean_ctor_set(v___x_2429_, 2, v___x_2428_);
v___x_2430_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2429_, v_a_2423_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v___x_2431_; 
lean_dec_ref(v___x_2430_);
v___x_2431_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2426_, v_a_2423_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v_result_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2475_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2432_);
lean_dec_ref(v___x_2431_);
v_result_2433_ = lean_ctor_get(v_a_2432_, 1);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_a_2432_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v_a_2432_, 0);
lean_dec(v_unused_2476_);
v___x_2435_ = v_a_2432_;
v_isShared_2436_ = v_isSharedCheck_2475_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_result_2433_);
lean_dec(v_a_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2475_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___y_2440_; 
v___x_2437_ = lean_unsigned_to_nat(1u);
v___x_2438_ = lean_nat_add(v_requestNo_2420_, v___x_2437_);
lean_dec(v_requestNo_2420_);
if (lean_obj_tag(v_result_2433_) == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2440_ = v___x_2473_;
goto v___jp_2439_;
}
else
{
lean_object* v_val_2474_; 
v_val_2474_ = lean_ctor_get(v_result_2433_, 0);
lean_inc(v_val_2474_);
lean_dec_ref(v_result_2433_);
v___y_2440_ = v_val_2474_;
goto v___jp_2439_;
}
v___jp_2439_:
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2441_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 1, v___x_2441_);
lean_ctor_set(v___x_2435_, 0, v___x_2438_);
v___x_2443_ = v___x_2435_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
size_t v_sz_2444_; size_t v___x_2445_; lean_object* v___x_2446_; 
v_sz_2444_ = lean_array_size(v___y_2440_);
v___x_2445_ = ((size_t)0ULL);
v___x_2446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v___y_2440_, v_sz_2444_, v___x_2445_, v___x_2443_, v_a_2423_);
lean_dec_ref(v___y_2440_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2463_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2449_ = v___x_2446_;
v_isShared_2450_ = v_isSharedCheck_2463_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2463_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v_fst_2451_; lean_object* v_snd_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2462_; 
v_fst_2451_ = lean_ctor_get(v_a_2447_, 0);
v_snd_2452_ = lean_ctor_get(v_a_2447_, 1);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_a_2447_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2454_ = v_a_2447_;
v_isShared_2455_ = v_isSharedCheck_2462_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_snd_2452_);
lean_inc(v_fst_2451_);
lean_dec(v_a_2447_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2462_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 1, v_fst_2451_);
lean_ctor_set(v___x_2454_, 0, v_snd_2452_);
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_snd_2452_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_fst_2451_);
v___x_2457_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2459_; 
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2457_);
v___x_2459_ = v___x_2449_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
v_a_2464_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2446_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2446_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_requestNo_2420_);
v_a_2477_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2431_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2431_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec_ref(v___x_2426_);
lean_dec(v_requestNo_2420_);
v_a_2485_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2430_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2430_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___boxed(lean_object* v_requestNo_2493_, lean_object* v_uri_2494_, lean_object* v_pos_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(v_requestNo_2493_, v_uri_2494_, v_pos_2495_, v_a_2496_);
lean_dec_ref(v_a_2496_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2499_, size_t v_i_2500_, lean_object* v_bs_2501_){
_start:
{
uint8_t v___x_2502_; 
v___x_2502_ = lean_usize_dec_lt(v_i_2500_, v_sz_2499_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_bs_2501_);
return v___x_2503_;
}
else
{
lean_object* v_v_2504_; lean_object* v___x_2505_; 
v_v_2504_ = lean_array_uget_borrowed(v_bs_2501_, v_i_2500_);
lean_inc(v_v_2504_);
v___x_2505_ = l_Lean_Lsp_instFromJsonCallHierarchyOutgoingCall_fromJson(v_v_2504_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec_ref(v_bs_2501_);
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2505_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2505_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2515_; lean_object* v_bs_x27_2516_; size_t v___x_2517_; size_t v___x_2518_; lean_object* v___x_2519_; 
v_a_2514_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2514_);
lean_dec_ref(v___x_2505_);
v___x_2515_ = lean_unsigned_to_nat(0u);
v_bs_x27_2516_ = lean_array_uset(v_bs_2501_, v_i_2500_, v___x_2515_);
v___x_2517_ = ((size_t)1ULL);
v___x_2518_ = lean_usize_add(v_i_2500_, v___x_2517_);
v___x_2519_ = lean_array_uset(v_bs_x27_2516_, v_i_2500_, v_a_2514_);
v_i_2500_ = v___x_2518_;
v_bs_2501_ = v___x_2519_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2521_, lean_object* v_i_2522_, lean_object* v_bs_2523_){
_start:
{
size_t v_sz_boxed_2524_; size_t v_i_boxed_2525_; lean_object* v_res_2526_; 
v_sz_boxed_2524_ = lean_unbox_usize(v_sz_2521_);
lean_dec(v_sz_2521_);
v_i_boxed_2525_ = lean_unbox_usize(v_i_2522_);
lean_dec(v_i_2522_);
v_res_2526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2524_, v_i_boxed_2525_, v_bs_2523_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(lean_object* v_x_2527_){
_start:
{
if (lean_obj_tag(v_x_2527_) == 4)
{
lean_object* v_elems_2528_; size_t v_sz_2529_; size_t v___x_2530_; lean_object* v___x_2531_; 
v_elems_2528_ = lean_ctor_get(v_x_2527_, 0);
lean_inc_ref(v_elems_2528_);
lean_dec_ref(v_x_2527_);
v_sz_2529_ = lean_array_size(v_elems_2528_);
v___x_2530_ = ((size_t)0ULL);
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_2529_, v___x_2530_, v_elems_2528_);
return v___x_2531_;
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2532_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2533_ = lean_unsigned_to_nat(80u);
v___x_2534_ = l_Lean_Json_pretty(v_x_2527_, v___x_2533_);
v___x_2535_ = lean_string_append(v___x_2532_, v___x_2534_);
lean_dec_ref(v___x_2534_);
v___x_2536_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2537_ = lean_string_append(v___x_2535_, v___x_2536_);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(lean_object* v_x_2541_){
_start:
{
if (lean_obj_tag(v_x_2541_) == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0));
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(v_x_2541_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2560_; 
v_a_2552_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2554_ = v___x_2543_;
v_isShared_2555_ = v_isSharedCheck_2560_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2543_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2560_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_a_2552_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2556_);
v___x_2558_ = v___x_2554_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(lean_object* v_expectedID_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_Lsp_Ipc_stdout(v_a_2562_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2708_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2708_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2708_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_IO_FS_Stream_readLspMessage(v_a_2565_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2699_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2699_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2699_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___y_2575_; lean_object* v___y_2576_; 
switch(lean_obj_tag(v_a_2570_))
{
case 2:
{
lean_object* v_id_2582_; lean_object* v_result_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2627_; 
v_id_2582_ = lean_ctor_get(v_a_2570_, 0);
v_result_2583_ = lean_ctor_get(v_a_2570_, 1);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_a_2570_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2585_ = v_a_2570_;
v_isShared_2586_ = v_isSharedCheck_2627_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_result_2583_);
lean_inc(v_id_2582_);
lean_dec(v_a_2570_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2627_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
uint8_t v___x_2587_; 
v___x_2587_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2582_, v_expectedID_2561_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; lean_object* v___y_2590_; 
lean_del_object(v___x_2585_);
lean_dec(v_result_2583_);
lean_del_object(v___x_2567_);
v___x_2588_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2561_))
{
case 0:
{
lean_object* v_s_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_s_2601_ = lean_ctor_get(v_expectedID_2561_, 0);
lean_inc_ref(v_s_2601_);
lean_dec_ref(v_expectedID_2561_);
v___x_2602_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2603_ = lean_string_append(v___x_2602_, v_s_2601_);
lean_dec_ref(v_s_2601_);
v___x_2604_ = lean_string_append(v___x_2603_, v___x_2602_);
v___y_2590_ = v___x_2604_;
goto v___jp_2589_;
}
case 1:
{
lean_object* v_n_2605_; lean_object* v___x_2606_; 
v_n_2605_ = lean_ctor_get(v_expectedID_2561_, 0);
lean_inc_ref(v_n_2605_);
lean_dec_ref(v_expectedID_2561_);
v___x_2606_ = l_Lean_JsonNumber_toString(v_n_2605_);
v___y_2590_ = v___x_2606_;
goto v___jp_2589_;
}
default: 
{
lean_object* v___x_2607_; 
v___x_2607_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2590_ = v___x_2607_;
goto v___jp_2589_;
}
}
v___jp_2589_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = lean_string_append(v___x_2588_, v___y_2590_);
lean_dec_ref(v___y_2590_);
v___x_2592_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2593_ = lean_string_append(v___x_2591_, v___x_2592_);
switch(lean_obj_tag(v_id_2582_))
{
case 0:
{
lean_object* v_s_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_s_2594_ = lean_ctor_get(v_id_2582_, 0);
lean_inc_ref(v_s_2594_);
lean_dec_ref(v_id_2582_);
v___x_2595_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2596_ = lean_string_append(v___x_2595_, v_s_2594_);
lean_dec_ref(v_s_2594_);
v___x_2597_ = lean_string_append(v___x_2596_, v___x_2595_);
v___y_2575_ = v___x_2593_;
v___y_2576_ = v___x_2597_;
goto v___jp_2574_;
}
case 1:
{
lean_object* v_n_2598_; lean_object* v___x_2599_; 
v_n_2598_ = lean_ctor_get(v_id_2582_, 0);
lean_inc_ref(v_n_2598_);
lean_dec_ref(v_id_2582_);
v___x_2599_ = l_Lean_JsonNumber_toString(v_n_2598_);
v___y_2575_ = v___x_2593_;
v___y_2576_ = v___x_2599_;
goto v___jp_2574_;
}
default: 
{
lean_object* v___x_2600_; 
v___x_2600_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2575_ = v___x_2593_;
v___y_2576_ = v___x_2600_;
goto v___jp_2574_;
}
}
}
}
else
{
lean_object* v___x_2608_; 
lean_dec(v_id_2582_);
lean_del_object(v___x_2572_);
lean_inc(v_result_2583_);
v___x_2608_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(v_result_2583_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_del_object(v___x_2585_);
lean_dec(v_expectedID_2561_);
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref(v___x_2608_);
v___x_2610_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2611_ = l_Lean_Json_compress(v_result_2583_);
v___x_2612_ = lean_string_append(v___x_2610_, v___x_2611_);
lean_dec_ref(v___x_2611_);
v___x_2613_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2614_ = lean_string_append(v___x_2612_, v___x_2613_);
v___x_2615_ = lean_string_append(v___x_2614_, v_a_2609_);
lean_dec(v_a_2609_);
v___x_2616_ = lean_mk_io_user_error(v___x_2615_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 1);
lean_ctor_set(v___x_2567_, 0, v___x_2616_);
v___x_2618_ = v___x_2567_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; 
lean_dec(v_result_2583_);
v_a_2620_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2620_);
lean_dec_ref(v___x_2608_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set_tag(v___x_2585_, 0);
lean_ctor_set(v___x_2585_, 1, v_a_2620_);
lean_ctor_set(v___x_2585_, 0, v_expectedID_2561_);
v___x_2622_ = v___x_2585_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_expectedID_2561_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_a_2620_);
v___x_2622_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2624_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2622_);
v___x_2624_ = v___x_2567_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2628_; uint8_t v_code_2629_; lean_object* v_message_2630_; lean_object* v_data_x3f_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v___x_2663_; lean_object* v___y_2665_; 
lean_del_object(v___x_2572_);
lean_dec(v_expectedID_2561_);
v_id_2628_ = lean_ctor_get(v_a_2570_, 0);
lean_inc(v_id_2628_);
v_code_2629_ = lean_ctor_get_uint8(v_a_2570_, sizeof(void*)*3);
v_message_2630_ = lean_ctor_get(v_a_2570_, 1);
lean_inc_ref(v_message_2630_);
v_data_x3f_2631_ = lean_ctor_get(v_a_2570_, 2);
lean_inc(v_data_x3f_2631_);
lean_dec_ref(v_a_2570_);
v___x_2632_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2633_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2663_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2628_))
{
case 0:
{
lean_object* v_s_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
v_s_2681_ = lean_ctor_get(v_id_2628_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_id_2628_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v_id_2628_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_s_2681_);
lean_dec(v_id_2628_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set_tag(v___x_2683_, 3);
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_s_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
v___y_2665_ = v___x_2686_;
goto v___jp_2664_;
}
}
}
case 1:
{
lean_object* v_n_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
v_n_2689_ = lean_ctor_get(v_id_2628_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_id_2628_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v_id_2628_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_n_2689_);
lean_dec(v_id_2628_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 2);
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_n_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
v___y_2665_ = v___x_2694_;
goto v___jp_2664_;
}
}
}
default: 
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_box(0);
v___y_2665_ = v___x_2697_;
goto v___jp_2664_;
}
}
v___jp_2634_:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
lean_inc(v___y_2638_);
lean_inc_ref(v___y_2635_);
v___x_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___y_2635_);
lean_ctor_set(v___x_2639_, 1, v___y_2638_);
v___x_2640_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2641_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2641_, 0, v_message_2630_);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = lean_box(0);
v___x_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2639_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2647_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2646_, v_data_x3f_2631_);
lean_dec(v_data_x3f_2631_);
v___x_2648_ = l_List_appendTR___redArg(v___x_2645_, v___x_2647_);
v___x_2649_ = l_Lean_Json_mkObj(v___x_2648_);
lean_inc_ref(v___y_2636_);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___y_2636_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
lean_ctor_set(v___x_2651_, 1, v___x_2643_);
v___x_2652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___y_2637_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2633_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = l_Lean_Json_mkObj(v___x_2653_);
v___x_2655_ = l_Lean_Json_compress(v___x_2654_);
v___x_2656_ = lean_string_append(v___x_2632_, v___x_2655_);
lean_dec_ref(v___x_2655_);
v___x_2657_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2658_ = lean_string_append(v___x_2656_, v___x_2657_);
v___x_2659_ = lean_mk_io_user_error(v___x_2658_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 1);
lean_ctor_set(v___x_2567_, 0, v___x_2659_);
v___x_2661_ = v___x_2567_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
v___jp_2664_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2663_);
lean_ctor_set(v___x_2666_, 1, v___y_2665_);
v___x_2667_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2668_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2629_)
{
case 0:
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2669_;
goto v___jp_2634_;
}
case 1:
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2670_;
goto v___jp_2634_;
}
case 2:
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2671_;
goto v___jp_2634_;
}
case 3:
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2672_;
goto v___jp_2634_;
}
case 4:
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2673_;
goto v___jp_2634_;
}
case 5:
{
lean_object* v___x_2674_; 
v___x_2674_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2674_;
goto v___jp_2634_;
}
case 6:
{
lean_object* v___x_2675_; 
v___x_2675_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2675_;
goto v___jp_2634_;
}
case 7:
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2676_;
goto v___jp_2634_;
}
case 8:
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2677_;
goto v___jp_2634_;
}
case 9:
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2678_;
goto v___jp_2634_;
}
case 10:
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2679_;
goto v___jp_2634_;
}
default: 
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2635_ = v___x_2668_;
v___y_2636_ = v___x_2667_;
v___y_2637_ = v___x_2666_;
v___y_2638_ = v___x_2680_;
goto v___jp_2634_;
}
}
}
}
default: 
{
lean_del_object(v___x_2572_);
lean_dec(v_a_2570_);
lean_del_object(v___x_2567_);
goto _start;
}
}
v___jp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2577_ = lean_string_append(v___y_2575_, v___y_2576_);
lean_dec_ref(v___y_2576_);
v___x_2578_ = lean_mk_io_user_error(v___x_2577_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set_tag(v___x_2572_, 1);
lean_ctor_set(v___x_2572_, 0, v___x_2578_);
v___x_2580_ = v___x_2572_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_del_object(v___x_2567_);
lean_dec(v_expectedID_2561_);
v_a_2700_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2569_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2569_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec(v_expectedID_2561_);
v_a_2709_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2564_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2564_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1___boxed(lean_object* v_expectedID_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v_expectedID_2717_, v_a_2718_);
lean_dec_ref(v_a_2718_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(lean_object* v_v_2721_){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = l_Lean_Lsp_instToJsonCallHierarchyOutgoingCallsParams_toJson(v_v_2721_);
v___x_2723_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(lean_object* v_h_2724_, lean_object* v_r_2725_){
_start:
{
lean_object* v_id_2727_; lean_object* v_method_2728_; lean_object* v_param_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2749_; 
v_id_2727_ = lean_ctor_get(v_r_2725_, 0);
v_method_2728_ = lean_ctor_get(v_r_2725_, 1);
v_param_2729_ = lean_ctor_get(v_r_2725_, 2);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_r_2725_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2731_ = v_r_2725_;
v_isShared_2732_ = v_isSharedCheck_2749_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_param_2729_);
lean_inc(v_method_2728_);
lean_inc(v_id_2727_);
lean_dec(v_r_2725_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2749_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___y_2734_; lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(v_param_2729_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v___x_2740_; 
lean_dec_ref(v___x_2739_);
v___x_2740_ = lean_box(0);
v___y_2734_ = v___x_2740_;
goto v___jp_2733_;
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
v_a_2741_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2739_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2739_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
v___y_2734_ = v___x_2746_;
goto v___jp_2733_;
}
}
}
v___jp_2733_:
{
lean_object* v___x_2736_; 
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 2, v___y_2734_);
v___x_2736_ = v___x_2731_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_id_2727_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_method_2728_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v___y_2734_);
v___x_2736_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_IO_FS_Stream_writeLspMessage(v_h_2724_, v___x_2736_);
return v___x_2737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0___boxed(lean_object* v_h_2750_, lean_object* v_r_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_h_2750_, v_r_2751_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(lean_object* v_r_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v___x_2757_; lean_object* v_a_2758_; lean_object* v___x_2759_; 
v___x_2757_ = l_Lean_Lsp_Ipc_stdin(v_a_2755_);
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref(v___x_2757_);
v___x_2759_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_a_2758_, v_r_2754_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0___boxed(lean_object* v_r_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v_r_2760_, v_a_2761_);
lean_dec_ref(v_a_2761_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(lean_object* v_requestNo_2767_, lean_object* v_item_2768_, lean_object* v_fromRanges_2769_, lean_object* v_visited_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v_name_2773_; uint8_t v___x_2774_; 
v_name_2773_ = lean_ctor_get(v_item_2768_, 0);
v___x_2774_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_2773_, v_visited_2770_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_inc(v_requestNo_2767_);
v___x_2775_ = l_Lean_JsonNumber_fromNat(v_requestNo_2767_);
v___x_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
v___x_2777_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_2768_);
lean_inc_ref(v___x_2776_);
v___x_2778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
lean_ctor_set(v___x_2778_, 2, v_item_2768_);
v___x_2779_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v___x_2778_, v_a_2771_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v___x_2780_; 
lean_dec_ref(v___x_2779_);
v___x_2780_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v___x_2776_, v_a_2771_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2818_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref(v___x_2780_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_box(0);
lean_inc_ref(v_name_2773_);
v___x_2825_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_2773_, v___x_2824_, v_visited_2770_);
v___y_2818_ = v___x_2825_;
goto v___jp_2817_;
}
else
{
v___y_2818_ = v_visited_2770_;
goto v___jp_2817_;
}
v___jp_2782_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; size_t v_sz_2788_; size_t v___x_2789_; lean_object* v___x_2790_; 
v___x_2786_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___y_2783_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v_sz_2788_ = lean_array_size(v___y_2785_);
v___x_2789_ = ((size_t)0ULL);
v___x_2790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___y_2784_, v___y_2785_, v_sz_2788_, v___x_2789_, v___x_2787_, v_a_2771_);
lean_dec_ref(v___y_2785_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2808_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2808_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2808_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_fst_2795_; lean_object* v_snd_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2807_; 
v_fst_2795_ = lean_ctor_get(v_a_2791_, 0);
v_snd_2796_ = lean_ctor_get(v_a_2791_, 1);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_a_2791_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2798_ = v_a_2791_;
v_isShared_2799_ = v_isSharedCheck_2807_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_snd_2796_);
lean_inc(v_fst_2795_);
lean_dec(v_a_2791_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2807_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2800_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2800_, 0, v_item_2768_);
lean_ctor_set(v___x_2800_, 1, v_fromRanges_2769_);
lean_ctor_set(v___x_2800_, 2, v_snd_2796_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 1, v_fst_2795_);
lean_ctor_set(v___x_2798_, 0, v___x_2800_);
v___x_2802_ = v___x_2798_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_fst_2795_);
v___x_2802_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2804_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2802_);
v___x_2804_ = v___x_2793_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec_ref(v_fromRanges_2769_);
lean_dec_ref(v_item_2768_);
v_a_2809_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2790_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2790_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
v___jp_2817_:
{
lean_object* v_result_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_result_2819_ = lean_ctor_get(v_a_2781_, 1);
lean_inc(v_result_2819_);
lean_dec(v_a_2781_);
v___x_2820_ = lean_unsigned_to_nat(1u);
v___x_2821_ = lean_nat_add(v_requestNo_2767_, v___x_2820_);
lean_dec(v_requestNo_2767_);
if (lean_obj_tag(v_result_2819_) == 0)
{
lean_object* v___x_2822_; 
v___x_2822_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1));
v___y_2783_ = v___x_2821_;
v___y_2784_ = v___y_2818_;
v___y_2785_ = v___x_2822_;
goto v___jp_2782_;
}
else
{
lean_object* v_val_2823_; 
v_val_2823_ = lean_ctor_get(v_result_2819_, 0);
lean_inc(v_val_2823_);
lean_dec_ref(v_result_2819_);
v___y_2783_ = v___x_2821_;
v___y_2784_ = v___y_2818_;
v___y_2785_ = v_val_2823_;
goto v___jp_2782_;
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_visited_2770_);
lean_dec_ref(v_fromRanges_2769_);
lean_dec_ref(v_item_2768_);
lean_dec(v_requestNo_2767_);
v_a_2826_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2780_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2780_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec_ref(v___x_2776_);
lean_dec(v_visited_2770_);
lean_dec_ref(v_fromRanges_2769_);
lean_dec_ref(v_item_2768_);
lean_dec(v_requestNo_2767_);
v_a_2834_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2779_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2779_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_dec(v_visited_2770_);
lean_dec_ref(v_fromRanges_2769_);
v___x_2842_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2843_, 0, v_item_2768_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
lean_ctor_set(v___x_2843_, 2, v___x_2842_);
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v_requestNo_2767_);
v___x_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
return v___x_2845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(lean_object* v___x_2846_, lean_object* v_as_2847_, size_t v_sz_2848_, size_t v_i_2849_, lean_object* v_b_2850_, lean_object* v___y_2851_){
_start:
{
uint8_t v___x_2853_; 
v___x_2853_ = lean_usize_dec_lt(v_i_2849_, v_sz_2848_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
lean_dec(v___x_2846_);
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v_b_2850_);
return v___x_2854_;
}
else
{
lean_object* v_fst_2855_; lean_object* v_snd_2856_; lean_object* v_a_2857_; lean_object* v_to_2858_; lean_object* v_fromRanges_2859_; lean_object* v___x_2860_; 
v_fst_2855_ = lean_ctor_get(v_b_2850_, 0);
lean_inc(v_fst_2855_);
v_snd_2856_ = lean_ctor_get(v_b_2850_, 1);
lean_inc(v_snd_2856_);
lean_dec_ref(v_b_2850_);
v_a_2857_ = lean_array_uget_borrowed(v_as_2847_, v_i_2849_);
v_to_2858_ = lean_ctor_get(v_a_2857_, 0);
v_fromRanges_2859_ = lean_ctor_get(v_a_2857_, 1);
lean_inc(v___x_2846_);
lean_inc_ref(v_fromRanges_2859_);
lean_inc_ref(v_to_2858_);
v___x_2860_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2855_, v_to_2858_, v_fromRanges_2859_, v___x_2846_, v___y_2851_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v_fst_2862_; lean_object* v_snd_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2874_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
v_fst_2862_ = lean_ctor_get(v_a_2861_, 0);
v_snd_2863_ = lean_ctor_get(v_a_2861_, 1);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_a_2861_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2865_ = v_a_2861_;
v_isShared_2866_ = v_isSharedCheck_2874_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_snd_2863_);
lean_inc(v_fst_2862_);
lean_dec(v_a_2861_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2874_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2867_ = lean_array_push(v_snd_2856_, v_fst_2862_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v___x_2867_);
lean_ctor_set(v___x_2865_, 0, v_snd_2863_);
v___x_2869_ = v___x_2865_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_snd_2863_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
size_t v___x_2870_; size_t v___x_2871_; 
v___x_2870_ = ((size_t)1ULL);
v___x_2871_ = lean_usize_add(v_i_2849_, v___x_2870_);
v_i_2849_ = v___x_2871_;
v_b_2850_ = v___x_2869_;
goto _start;
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec(v_snd_2856_);
lean_dec(v___x_2846_);
v_a_2875_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2860_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2860_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2___boxed(lean_object* v___x_2883_, lean_object* v_as_2884_, lean_object* v_sz_2885_, lean_object* v_i_2886_, lean_object* v_b_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
size_t v_sz_boxed_2890_; size_t v_i_boxed_2891_; lean_object* v_res_2892_; 
v_sz_boxed_2890_ = lean_unbox_usize(v_sz_2885_);
lean_dec(v_sz_2885_);
v_i_boxed_2891_ = lean_unbox_usize(v_i_2886_);
lean_dec(v_i_2886_);
v_res_2892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___x_2883_, v_as_2884_, v_sz_boxed_2890_, v_i_boxed_2891_, v_b_2887_, v___y_2888_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v_as_2884_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___boxed(lean_object* v_requestNo_2893_, lean_object* v_item_2894_, lean_object* v_fromRanges_2895_, lean_object* v_visited_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_requestNo_2893_, v_item_2894_, v_fromRanges_2895_, v_visited_2896_, v_a_2897_);
lean_dec_ref(v_a_2897_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(lean_object* v_as_2900_, size_t v_sz_2901_, size_t v_i_2902_, lean_object* v_b_2903_, lean_object* v___y_2904_){
_start:
{
uint8_t v___x_2906_; 
v___x_2906_ = lean_usize_dec_lt(v_i_2902_, v_sz_2901_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_b_2903_);
return v___x_2907_;
}
else
{
lean_object* v_fst_2908_; lean_object* v_snd_2909_; lean_object* v_a_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v_fst_2908_ = lean_ctor_get(v_b_2903_, 0);
lean_inc(v_fst_2908_);
v_snd_2909_ = lean_ctor_get(v_b_2903_, 1);
lean_inc(v_snd_2909_);
lean_dec_ref(v_b_2903_);
v_a_2910_ = lean_array_uget_borrowed(v_as_2900_, v_i_2902_);
v___x_2911_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2912_ = lean_box(1);
lean_inc(v_a_2910_);
v___x_2913_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2908_, v_a_2910_, v___x_2911_, v___x_2912_, v___y_2904_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v_fst_2915_; lean_object* v_snd_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2927_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref(v___x_2913_);
v_fst_2915_ = lean_ctor_get(v_a_2914_, 0);
v_snd_2916_ = lean_ctor_get(v_a_2914_, 1);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_a_2914_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2918_ = v_a_2914_;
v_isShared_2919_ = v_isSharedCheck_2927_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_snd_2916_);
lean_inc(v_fst_2915_);
lean_dec(v_a_2914_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2927_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2920_ = lean_array_push(v_snd_2909_, v_fst_2915_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 1, v___x_2920_);
lean_ctor_set(v___x_2918_, 0, v_snd_2916_);
v___x_2922_ = v___x_2918_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_snd_2916_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
size_t v___x_2923_; size_t v___x_2924_; 
v___x_2923_ = ((size_t)1ULL);
v___x_2924_ = lean_usize_add(v_i_2902_, v___x_2923_);
v_i_2902_ = v___x_2924_;
v_b_2903_ = v___x_2922_;
goto _start;
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_snd_2909_);
v_a_2928_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2913_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2913_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0___boxed(lean_object* v_as_2936_, lean_object* v_sz_2937_, lean_object* v_i_2938_, lean_object* v_b_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
size_t v_sz_boxed_2942_; size_t v_i_boxed_2943_; lean_object* v_res_2944_; 
v_sz_boxed_2942_ = lean_unbox_usize(v_sz_2937_);
lean_dec(v_sz_2937_);
v_i_boxed_2943_ = lean_unbox_usize(v_i_2938_);
lean_dec(v_i_2938_);
v_res_2944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v_as_2936_, v_sz_boxed_2942_, v_i_boxed_2943_, v_b_2939_, v___y_2940_);
lean_dec_ref(v___y_2940_);
lean_dec_ref(v_as_2936_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(lean_object* v_requestNo_2945_, lean_object* v_uri_2946_, lean_object* v_pos_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_inc(v_requestNo_2945_);
v___x_2950_ = l_Lean_JsonNumber_fromNat(v_requestNo_2945_);
v___x_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
v___x_2952_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v_uri_2946_);
lean_ctor_set(v___x_2953_, 1, v_pos_2947_);
lean_inc_ref(v___x_2951_);
v___x_2954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2951_);
lean_ctor_set(v___x_2954_, 1, v___x_2952_);
lean_ctor_set(v___x_2954_, 2, v___x_2953_);
v___x_2955_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2954_, v_a_2948_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v___x_2956_; 
lean_dec_ref(v___x_2955_);
v___x_2956_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2951_, v_a_2948_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v_result_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_3000_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref(v___x_2956_);
v_result_2958_ = lean_ctor_get(v_a_2957_, 1);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_a_2957_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v_a_2957_, 0);
lean_dec(v_unused_3001_);
v___x_2960_ = v_a_2957_;
v_isShared_2961_ = v_isSharedCheck_3000_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_result_2958_);
lean_dec(v_a_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_3000_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___y_2965_; 
v___x_2962_ = lean_unsigned_to_nat(1u);
v___x_2963_ = lean_nat_add(v_requestNo_2945_, v___x_2962_);
lean_dec(v_requestNo_2945_);
if (lean_obj_tag(v_result_2958_) == 0)
{
lean_object* v___x_2998_; 
v___x_2998_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2965_ = v___x_2998_;
goto v___jp_2964_;
}
else
{
lean_object* v_val_2999_; 
v_val_2999_ = lean_ctor_get(v_result_2958_, 0);
lean_inc(v_val_2999_);
lean_dec_ref(v_result_2958_);
v___y_2965_ = v_val_2999_;
goto v___jp_2964_;
}
v___jp_2964_:
{
lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2966_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 1, v___x_2966_);
lean_ctor_set(v___x_2960_, 0, v___x_2963_);
v___x_2968_ = v___x_2960_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
size_t v_sz_2969_; size_t v___x_2970_; lean_object* v___x_2971_; 
v_sz_2969_ = lean_array_size(v___y_2965_);
v___x_2970_ = ((size_t)0ULL);
v___x_2971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v___y_2965_, v_sz_2969_, v___x_2970_, v___x_2968_, v_a_2948_);
lean_dec_ref(v___y_2965_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2988_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2988_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2988_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v_fst_2976_; lean_object* v_snd_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2987_; 
v_fst_2976_ = lean_ctor_get(v_a_2972_, 0);
v_snd_2977_ = lean_ctor_get(v_a_2972_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_a_2972_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2979_ = v_a_2972_;
v_isShared_2980_ = v_isSharedCheck_2987_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_snd_2977_);
lean_inc(v_fst_2976_);
lean_dec(v_a_2972_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2987_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 1, v_fst_2976_);
lean_ctor_set(v___x_2979_, 0, v_snd_2977_);
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_snd_2977_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_fst_2976_);
v___x_2982_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2984_; 
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 0, v___x_2982_);
v___x_2984_ = v___x_2974_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
v_a_2989_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2971_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2971_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec(v_requestNo_2945_);
v_a_3002_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2956_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2956_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec_ref(v___x_2951_);
lean_dec(v_requestNo_2945_);
v_a_3010_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2955_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2955_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy___boxed(lean_object* v_requestNo_3018_, lean_object* v_uri_3019_, lean_object* v_pos_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(v_requestNo_3018_, v_uri_3019_, v_pos_3020_, v_a_3021_);
lean_dec_ref(v_a_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(lean_object* v_j_3024_, lean_object* v_k_3025_){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = l_Lean_Json_getObjValD(v_j_3024_, v_k_3025_);
v___x_3027_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v___x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0___boxed(lean_object* v_j_3028_, lean_object* v_k_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_j_3028_, v_k_3029_);
lean_dec_ref(v_k_3029_);
return v_res_3030_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3037_ = 1;
v___x_3038_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1));
v___x_3039_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3038_, v___x_3037_);
return v___x_3039_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_3041_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2);
v___x_3042_ = lean_string_append(v___x_3041_, v___x_3040_);
return v___x_3042_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_3044_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3045_ = lean_string_append(v___x_3044_, v___x_3043_);
return v___x_3045_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3047_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4);
v___x_3048_ = lean_string_append(v___x_3047_, v___x_3046_);
return v___x_3048_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_3050_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3051_ = lean_string_append(v___x_3050_, v___x_3049_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3053_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6);
v___x_3054_ = lean_string_append(v___x_3053_, v___x_3052_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(lean_object* v_json_3055_){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_3055_);
v___x_3057_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_json_3055_, v___x_3056_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3067_; 
lean_dec(v_json_3055_);
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3067_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3067_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3062_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5);
v___x_3063_ = lean_string_append(v___x_3062_, v_a_3058_);
lean_dec(v_a_3058_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3063_);
v___x_3065_ = v___x_3060_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
else
{
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec(v_json_3055_);
v_a_3068_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3057_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3057_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
lean_ctor_set_tag(v___x_3070_, 0);
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_a_3076_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3076_);
lean_dec_ref(v___x_3057_);
v___x_3077_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3078_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_json_3055_, v___x_3077_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v_a_3076_);
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3081_ = v___x_3078_;
v_isShared_3082_ = v_isSharedCheck_3088_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3078_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3088_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3083_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7);
v___x_3084_ = lean_string_append(v___x_3083_, v_a_3079_);
lean_dec(v_a_3079_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 0, v___x_3084_);
v___x_3086_ = v___x_3081_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
else
{
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_a_3076_);
v_a_3089_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3078_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3078_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
lean_ctor_set_tag(v___x_3091_, 0);
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3105_; 
v_a_3097_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3099_ = v___x_3078_;
v_isShared_3100_ = v_isSharedCheck_3105_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3078_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3105_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3103_; 
v___x_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3101_, 0, v_a_3076_);
lean_ctor_set(v___x_3101_, 1, v_a_3097_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3101_);
v___x_3103_ = v___x_3099_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_3106_, size_t v_i_3107_, lean_object* v_bs_3108_){
_start:
{
uint8_t v___x_3109_; 
v___x_3109_ = lean_usize_dec_lt(v_i_3107_, v_sz_3106_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; 
v___x_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3110_, 0, v_bs_3108_);
return v___x_3110_;
}
else
{
lean_object* v_v_3111_; lean_object* v___x_3112_; 
v_v_3111_ = lean_array_uget_borrowed(v_bs_3108_, v_i_3107_);
lean_inc(v_v_3111_);
v___x_3112_ = l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(v_v_3111_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec_ref(v_bs_3108_);
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3122_; lean_object* v_bs_x27_3123_; size_t v___x_3124_; size_t v___x_3125_; lean_object* v___x_3126_; 
v_a_3121_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3121_);
lean_dec_ref(v___x_3112_);
v___x_3122_ = lean_unsigned_to_nat(0u);
v_bs_x27_3123_ = lean_array_uset(v_bs_3108_, v_i_3107_, v___x_3122_);
v___x_3124_ = ((size_t)1ULL);
v___x_3125_ = lean_usize_add(v_i_3107_, v___x_3124_);
v___x_3126_ = lean_array_uset(v_bs_x27_3123_, v_i_3107_, v_a_3121_);
v_i_3107_ = v___x_3125_;
v_bs_3108_ = v___x_3126_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_3128_){
_start:
{
if (lean_obj_tag(v_x_3128_) == 4)
{
lean_object* v_elems_3129_; size_t v_sz_3130_; size_t v___x_3131_; lean_object* v___x_3132_; 
v_elems_3129_ = lean_ctor_get(v_x_3128_, 0);
lean_inc_ref(v_elems_3129_);
lean_dec_ref(v_x_3128_);
v_sz_3130_ = lean_array_size(v_elems_3129_);
v___x_3131_ = ((size_t)0ULL);
v___x_3132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_3130_, v___x_3131_, v_elems_3129_);
return v___x_3132_;
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3133_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3134_ = lean_unsigned_to_nat(80u);
v___x_3135_ = l_Lean_Json_pretty(v_x_3128_, v___x_3134_);
v___x_3136_ = lean_string_append(v___x_3133_, v___x_3135_);
lean_dec_ref(v___x_3135_);
v___x_3137_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3138_ = lean_string_append(v___x_3136_, v___x_3137_);
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
return v___x_3139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(lean_object* v_j_3140_, lean_object* v_k_3141_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = l_Lean_Json_getObjValD(v_j_3140_, v_k_3141_);
v___x_3143_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(v___x_3142_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1___boxed(lean_object* v_j_3144_, lean_object* v_k_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_j_3144_, v_k_3145_);
lean_dec_ref(v_k_3145_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_3147_, lean_object* v_i_3148_, lean_object* v_bs_3149_){
_start:
{
size_t v_sz_boxed_3150_; size_t v_i_boxed_3151_; lean_object* v_res_3152_; 
v_sz_boxed_3150_ = lean_unbox_usize(v_sz_3147_);
lean_dec(v_sz_3147_);
v_i_boxed_3151_ = lean_unbox_usize(v_i_3148_);
lean_dec(v_i_3148_);
v_res_3152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_3150_, v_i_boxed_3151_, v_bs_3149_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(lean_object* v_x_3155_){
_start:
{
lean_object* v_item_3156_; lean_object* v_children_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3177_; 
v_item_3156_ = lean_ctor_get(v_x_3155_, 0);
v_children_3157_ = lean_ctor_get(v_x_3155_, 1);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_x_3155_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3159_ = v_x_3155_;
v_isShared_3160_ = v_isSharedCheck_3177_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_children_3157_);
lean_inc(v_item_3156_);
lean_dec(v_x_3155_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3177_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3161_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_3162_ = l_Lean_Lsp_instToJsonLeanImport_toJson(v_item_3156_);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 1, v___x_3162_);
lean_ctor_set(v___x_3159_, 0, v___x_3161_);
v___x_3164_ = v___x_3159_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3161_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3165_ = lean_box(0);
v___x_3166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3164_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3168_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(v_children_3157_);
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3167_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3165_);
v___x_3171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v___x_3165_);
v___x_3172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3166_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_3174_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_3172_, v___x_3173_);
v___x_3175_ = l_Lean_Json_mkObj(v___x_3174_);
return v___x_3175_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(size_t v_sz_3178_, size_t v_i_3179_, lean_object* v_bs_3180_){
_start:
{
uint8_t v___x_3181_; 
v___x_3181_ = lean_usize_dec_lt(v_i_3179_, v_sz_3178_);
if (v___x_3181_ == 0)
{
return v_bs_3180_;
}
else
{
lean_object* v_v_3182_; lean_object* v___x_3183_; lean_object* v_bs_x27_3184_; lean_object* v___x_3185_; size_t v___x_3186_; size_t v___x_3187_; lean_object* v___x_3188_; 
v_v_3182_ = lean_array_uget(v_bs_3180_, v_i_3179_);
v___x_3183_ = lean_unsigned_to_nat(0u);
v_bs_x27_3184_ = lean_array_uset(v_bs_3180_, v_i_3179_, v___x_3183_);
v___x_3185_ = l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(v_v_3182_);
v___x_3186_ = ((size_t)1ULL);
v___x_3187_ = lean_usize_add(v_i_3179_, v___x_3186_);
v___x_3188_ = lean_array_uset(v_bs_x27_3184_, v_i_3179_, v___x_3185_);
v_i_3179_ = v___x_3187_;
v_bs_3180_ = v___x_3188_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(lean_object* v_a_3190_){
_start:
{
size_t v_sz_3191_; size_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_sz_3191_ = lean_array_size(v_a_3190_);
v___x_3192_ = ((size_t)0ULL);
v___x_3193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_3191_, v___x_3192_, v_a_3190_);
v___x_3194_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3195_, lean_object* v_i_3196_, lean_object* v_bs_3197_){
_start:
{
size_t v_sz_boxed_3198_; size_t v_i_boxed_3199_; lean_object* v_res_3200_; 
v_sz_boxed_3198_ = lean_unbox_usize(v_sz_3195_);
lean_dec(v_sz_3195_);
v_i_boxed_3199_ = lean_unbox_usize(v_i_3196_);
lean_dec(v_i_3196_);
v_res_3200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_boxed_3198_, v_i_boxed_3199_, v_bs_3197_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(size_t v_sz_3203_, size_t v_i_3204_, lean_object* v_bs_3205_){
_start:
{
uint8_t v___x_3206_; 
v___x_3206_ = lean_usize_dec_lt(v_i_3204_, v_sz_3203_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v_bs_3205_);
return v___x_3207_;
}
else
{
lean_object* v_v_3208_; lean_object* v___x_3209_; 
v_v_3208_ = lean_array_uget_borrowed(v_bs_3205_, v_i_3204_);
lean_inc(v_v_3208_);
v___x_3209_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v_v_3208_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec_ref(v_bs_3205_);
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3209_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3219_; lean_object* v_bs_x27_3220_; size_t v___x_3221_; size_t v___x_3222_; lean_object* v___x_3223_; 
v_a_3218_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3218_);
lean_dec_ref(v___x_3209_);
v___x_3219_ = lean_unsigned_to_nat(0u);
v_bs_x27_3220_ = lean_array_uset(v_bs_3205_, v_i_3204_, v___x_3219_);
v___x_3221_ = ((size_t)1ULL);
v___x_3222_ = lean_usize_add(v_i_3204_, v___x_3221_);
v___x_3223_ = lean_array_uset(v_bs_x27_3220_, v_i_3204_, v_a_3218_);
v_i_3204_ = v___x_3222_;
v_bs_3205_ = v___x_3223_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_3225_, lean_object* v_i_3226_, lean_object* v_bs_3227_){
_start:
{
size_t v_sz_boxed_3228_; size_t v_i_boxed_3229_; lean_object* v_res_3230_; 
v_sz_boxed_3228_ = lean_unbox_usize(v_sz_3225_);
lean_dec(v_sz_3225_);
v_i_boxed_3229_ = lean_unbox_usize(v_i_3226_);
lean_dec(v_i_3226_);
v_res_3230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_boxed_3228_, v_i_boxed_3229_, v_bs_3227_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(lean_object* v_x_3231_){
_start:
{
if (lean_obj_tag(v_x_3231_) == 4)
{
lean_object* v_elems_3232_; size_t v_sz_3233_; size_t v___x_3234_; lean_object* v___x_3235_; 
v_elems_3232_ = lean_ctor_get(v_x_3231_, 0);
lean_inc_ref(v_elems_3232_);
lean_dec_ref(v_x_3231_);
v_sz_3233_ = lean_array_size(v_elems_3232_);
v___x_3234_ = ((size_t)0ULL);
v___x_3235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_3233_, v___x_3234_, v_elems_3232_);
return v___x_3235_;
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3236_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3237_ = lean_unsigned_to_nat(80u);
v___x_3238_ = l_Lean_Json_pretty(v_x_3231_, v___x_3237_);
v___x_3239_ = lean_string_append(v___x_3236_, v___x_3238_);
lean_dec_ref(v___x_3238_);
v___x_3240_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3241_ = lean_string_append(v___x_3239_, v___x_3240_);
v___x_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(lean_object* v_expectedID_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_Lsp_Ipc_stdout(v_a_3244_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3390_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3390_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3390_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_IO_FS_Stream_readLspMessage(v_a_3247_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3381_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3381_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3381_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___y_3257_; lean_object* v___y_3258_; 
switch(lean_obj_tag(v_a_3252_))
{
case 2:
{
lean_object* v_id_3264_; lean_object* v_result_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3309_; 
v_id_3264_ = lean_ctor_get(v_a_3252_, 0);
v_result_3265_ = lean_ctor_get(v_a_3252_, 1);
v_isSharedCheck_3309_ = !lean_is_exclusive(v_a_3252_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3267_ = v_a_3252_;
v_isShared_3268_ = v_isSharedCheck_3309_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_result_3265_);
lean_inc(v_id_3264_);
lean_dec(v_a_3252_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3309_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
uint8_t v___x_3269_; 
v___x_3269_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3264_, v_expectedID_3243_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v___y_3272_; 
lean_del_object(v___x_3267_);
lean_dec(v_result_3265_);
lean_del_object(v___x_3249_);
v___x_3270_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3243_))
{
case 0:
{
lean_object* v_s_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_s_3283_ = lean_ctor_get(v_expectedID_3243_, 0);
lean_inc_ref(v_s_3283_);
lean_dec_ref(v_expectedID_3243_);
v___x_3284_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3285_ = lean_string_append(v___x_3284_, v_s_3283_);
lean_dec_ref(v_s_3283_);
v___x_3286_ = lean_string_append(v___x_3285_, v___x_3284_);
v___y_3272_ = v___x_3286_;
goto v___jp_3271_;
}
case 1:
{
lean_object* v_n_3287_; lean_object* v___x_3288_; 
v_n_3287_ = lean_ctor_get(v_expectedID_3243_, 0);
lean_inc_ref(v_n_3287_);
lean_dec_ref(v_expectedID_3243_);
v___x_3288_ = l_Lean_JsonNumber_toString(v_n_3287_);
v___y_3272_ = v___x_3288_;
goto v___jp_3271_;
}
default: 
{
lean_object* v___x_3289_; 
v___x_3289_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3272_ = v___x_3289_;
goto v___jp_3271_;
}
}
v___jp_3271_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = lean_string_append(v___x_3270_, v___y_3272_);
lean_dec_ref(v___y_3272_);
v___x_3274_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3275_ = lean_string_append(v___x_3273_, v___x_3274_);
switch(lean_obj_tag(v_id_3264_))
{
case 0:
{
lean_object* v_s_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v_s_3276_ = lean_ctor_get(v_id_3264_, 0);
lean_inc_ref(v_s_3276_);
lean_dec_ref(v_id_3264_);
v___x_3277_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3278_ = lean_string_append(v___x_3277_, v_s_3276_);
lean_dec_ref(v_s_3276_);
v___x_3279_ = lean_string_append(v___x_3278_, v___x_3277_);
v___y_3257_ = v___x_3275_;
v___y_3258_ = v___x_3279_;
goto v___jp_3256_;
}
case 1:
{
lean_object* v_n_3280_; lean_object* v___x_3281_; 
v_n_3280_ = lean_ctor_get(v_id_3264_, 0);
lean_inc_ref(v_n_3280_);
lean_dec_ref(v_id_3264_);
v___x_3281_ = l_Lean_JsonNumber_toString(v_n_3280_);
v___y_3257_ = v___x_3275_;
v___y_3258_ = v___x_3281_;
goto v___jp_3256_;
}
default: 
{
lean_object* v___x_3282_; 
v___x_3282_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3257_ = v___x_3275_;
v___y_3258_ = v___x_3282_;
goto v___jp_3256_;
}
}
}
}
else
{
lean_object* v___x_3290_; 
lean_dec(v_id_3264_);
lean_del_object(v___x_3254_);
lean_inc(v_result_3265_);
v___x_3290_ = l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(v_result_3265_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
lean_del_object(v___x_3267_);
lean_dec(v_expectedID_3243_);
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref(v___x_3290_);
v___x_3292_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3293_ = l_Lean_Json_compress(v_result_3265_);
v___x_3294_ = lean_string_append(v___x_3292_, v___x_3293_);
lean_dec_ref(v___x_3293_);
v___x_3295_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3296_ = lean_string_append(v___x_3294_, v___x_3295_);
v___x_3297_ = lean_string_append(v___x_3296_, v_a_3291_);
lean_dec(v_a_3291_);
v___x_3298_ = lean_mk_io_user_error(v___x_3297_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set_tag(v___x_3249_, 1);
lean_ctor_set(v___x_3249_, 0, v___x_3298_);
v___x_3300_ = v___x_3249_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; 
lean_dec(v_result_3265_);
v_a_3302_ = lean_ctor_get(v___x_3290_, 0);
lean_inc(v_a_3302_);
lean_dec_ref(v___x_3290_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 0);
lean_ctor_set(v___x_3267_, 1, v_a_3302_);
lean_ctor_set(v___x_3267_, 0, v_expectedID_3243_);
v___x_3304_ = v___x_3267_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_expectedID_3243_);
lean_ctor_set(v_reuseFailAlloc_3308_, 1, v_a_3302_);
v___x_3304_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
lean_object* v___x_3306_; 
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3304_);
v___x_3306_ = v___x_3249_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3304_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3310_; uint8_t v_code_3311_; lean_object* v_message_3312_; lean_object* v_data_x3f_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___x_3345_; lean_object* v___y_3347_; 
lean_del_object(v___x_3254_);
lean_dec(v_expectedID_3243_);
v_id_3310_ = lean_ctor_get(v_a_3252_, 0);
lean_inc(v_id_3310_);
v_code_3311_ = lean_ctor_get_uint8(v_a_3252_, sizeof(void*)*3);
v_message_3312_ = lean_ctor_get(v_a_3252_, 1);
lean_inc_ref(v_message_3312_);
v_data_x3f_3313_ = lean_ctor_get(v_a_3252_, 2);
lean_inc(v_data_x3f_3313_);
lean_dec_ref(v_a_3252_);
v___x_3314_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3315_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3345_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3310_))
{
case 0:
{
lean_object* v_s_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
v_s_3363_ = lean_ctor_get(v_id_3310_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_id_3310_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v_id_3310_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_s_3363_);
lean_dec(v_id_3310_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
lean_ctor_set_tag(v___x_3365_, 3);
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_s_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
v___y_3347_ = v___x_3368_;
goto v___jp_3346_;
}
}
}
case 1:
{
lean_object* v_n_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
v_n_3371_ = lean_ctor_get(v_id_3310_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v_id_3310_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v_id_3310_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_n_3371_);
lean_dec(v_id_3310_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
lean_ctor_set_tag(v___x_3373_, 2);
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_n_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
v___y_3347_ = v___x_3376_;
goto v___jp_3346_;
}
}
}
default: 
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_box(0);
v___y_3347_ = v___x_3379_;
goto v___jp_3346_;
}
}
v___jp_3316_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3343_; 
lean_inc(v___y_3320_);
lean_inc_ref(v___y_3319_);
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___y_3319_);
lean_ctor_set(v___x_3321_, 1, v___y_3320_);
v___x_3322_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3323_, 0, v_message_3312_);
v___x_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = lean_box(0);
v___x_3326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3324_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3321_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3329_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3328_, v_data_x3f_3313_);
lean_dec(v_data_x3f_3313_);
v___x_3330_ = l_List_appendTR___redArg(v___x_3327_, v___x_3329_);
v___x_3331_ = l_Lean_Json_mkObj(v___x_3330_);
lean_inc_ref(v___y_3317_);
v___x_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___y_3317_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
lean_ctor_set(v___x_3333_, 1, v___x_3325_);
v___x_3334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___y_3318_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3315_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = l_Lean_Json_mkObj(v___x_3335_);
v___x_3337_ = l_Lean_Json_compress(v___x_3336_);
v___x_3338_ = lean_string_append(v___x_3314_, v___x_3337_);
lean_dec_ref(v___x_3337_);
v___x_3339_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3340_ = lean_string_append(v___x_3338_, v___x_3339_);
v___x_3341_ = lean_mk_io_user_error(v___x_3340_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set_tag(v___x_3249_, 1);
lean_ctor_set(v___x_3249_, 0, v___x_3341_);
v___x_3343_ = v___x_3249_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
v___jp_3346_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3345_);
lean_ctor_set(v___x_3348_, 1, v___y_3347_);
v___x_3349_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3350_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3311_)
{
case 0:
{
lean_object* v___x_3351_; 
v___x_3351_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3351_;
goto v___jp_3316_;
}
case 1:
{
lean_object* v___x_3352_; 
v___x_3352_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3352_;
goto v___jp_3316_;
}
case 2:
{
lean_object* v___x_3353_; 
v___x_3353_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3353_;
goto v___jp_3316_;
}
case 3:
{
lean_object* v___x_3354_; 
v___x_3354_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3354_;
goto v___jp_3316_;
}
case 4:
{
lean_object* v___x_3355_; 
v___x_3355_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3355_;
goto v___jp_3316_;
}
case 5:
{
lean_object* v___x_3356_; 
v___x_3356_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3356_;
goto v___jp_3316_;
}
case 6:
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3357_;
goto v___jp_3316_;
}
case 7:
{
lean_object* v___x_3358_; 
v___x_3358_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3358_;
goto v___jp_3316_;
}
case 8:
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3359_;
goto v___jp_3316_;
}
case 9:
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3360_;
goto v___jp_3316_;
}
case 10:
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3361_;
goto v___jp_3316_;
}
default: 
{
lean_object* v___x_3362_; 
v___x_3362_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3317_ = v___x_3349_;
v___y_3318_ = v___x_3348_;
v___y_3319_ = v___x_3350_;
v___y_3320_ = v___x_3362_;
goto v___jp_3316_;
}
}
}
}
default: 
{
lean_del_object(v___x_3254_);
lean_dec(v_a_3252_);
lean_del_object(v___x_3249_);
goto _start;
}
}
v___jp_3256_:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3259_ = lean_string_append(v___y_3257_, v___y_3258_);
lean_dec_ref(v___y_3258_);
v___x_3260_ = lean_mk_io_user_error(v___x_3259_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set_tag(v___x_3254_, 1);
lean_ctor_set(v___x_3254_, 0, v___x_3260_);
v___x_3262_ = v___x_3254_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_del_object(v___x_3249_);
lean_dec(v_expectedID_3243_);
v_a_3382_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3251_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3251_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec(v_expectedID_3243_);
v_a_3391_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3246_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3246_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1___boxed(lean_object* v_expectedID_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v_expectedID_3399_, v_a_3400_);
lean_dec_ref(v_a_3400_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(lean_object* v_v_3403_){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_v_3403_);
v___x_3405_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_v_3406_);
lean_dec_ref(v_v_3406_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(lean_object* v_h_3408_, lean_object* v_r_3409_){
_start:
{
lean_object* v_id_3411_; lean_object* v_method_3412_; lean_object* v_param_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3433_; 
v_id_3411_ = lean_ctor_get(v_r_3409_, 0);
v_method_3412_ = lean_ctor_get(v_r_3409_, 1);
v_param_3413_ = lean_ctor_get(v_r_3409_, 2);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_r_3409_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3415_ = v_r_3409_;
v_isShared_3416_ = v_isSharedCheck_3433_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_param_3413_);
lean_inc(v_method_3412_);
lean_inc(v_id_3411_);
lean_dec(v_r_3409_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3433_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___y_3418_; lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_param_3413_);
lean_dec(v_param_3413_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v___x_3424_; 
lean_dec_ref(v___x_3423_);
v___x_3424_ = lean_box(0);
v___y_3418_ = v___x_3424_;
goto v___jp_3417_;
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
v_a_3425_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3423_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3423_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
v___y_3418_ = v___x_3430_;
goto v___jp_3417_;
}
}
}
v___jp_3417_:
{
lean_object* v___x_3420_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 2, v___y_3418_);
v___x_3420_ = v___x_3415_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_id_3411_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_method_3412_);
lean_ctor_set(v_reuseFailAlloc_3422_, 2, v___y_3418_);
v___x_3420_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_IO_FS_Stream_writeLspMessage(v_h_3408_, v___x_3420_);
return v___x_3421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0___boxed(lean_object* v_h_3434_, lean_object* v_r_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_h_3434_, v_r_3435_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(lean_object* v_r_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v___x_3441_; lean_object* v_a_3442_; lean_object* v___x_3443_; 
v___x_3441_ = l_Lean_Lsp_Ipc_stdin(v_a_3439_);
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref(v___x_3441_);
v___x_3443_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_a_3442_, v_r_3438_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0___boxed(lean_object* v_r_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v_r_3444_, v_a_3445_);
lean_dec_ref(v_a_3445_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(lean_object* v_requestNo_3451_, lean_object* v_item_3452_, lean_object* v_visited_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v_module_3456_; lean_object* v_name_3457_; uint8_t v___x_3458_; 
v_module_3456_ = lean_ctor_get(v_item_3452_, 0);
v_name_3457_ = lean_ctor_get(v_module_3456_, 0);
v___x_3458_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3457_, v_visited_3453_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
lean_inc(v_requestNo_3451_);
v___x_3459_ = l_Lean_JsonNumber_fromNat(v_requestNo_3451_);
v___x_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
v___x_3461_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0));
lean_inc_ref(v_module_3456_);
lean_inc_ref(v___x_3460_);
v___x_3462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
lean_ctor_set(v___x_3462_, 2, v_module_3456_);
v___x_3463_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v___x_3462_, v_a_3454_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v___x_3464_; 
lean_dec_ref(v___x_3463_);
v___x_3464_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3460_, v_a_3454_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___y_3467_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref(v___x_3464_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = lean_box(0);
lean_inc_ref(v_name_3457_);
v___x_3510_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3457_, v___x_3509_, v_visited_3453_);
v___y_3467_ = v___x_3510_;
goto v___jp_3466_;
}
else
{
v___y_3467_ = v_visited_3453_;
goto v___jp_3466_;
}
v___jp_3466_:
{
lean_object* v_result_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3507_; 
v_result_3468_ = lean_ctor_get(v_a_3465_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_a_3465_);
if (v_isSharedCheck_3507_ == 0)
{
lean_object* v_unused_3508_; 
v_unused_3508_ = lean_ctor_get(v_a_3465_, 0);
lean_dec(v_unused_3508_);
v___x_3470_ = v_a_3465_;
v_isShared_3471_ = v_isSharedCheck_3507_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_result_3468_);
lean_dec(v_a_3465_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3507_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
v___x_3472_ = lean_unsigned_to_nat(1u);
v___x_3473_ = lean_nat_add(v_requestNo_3451_, v___x_3472_);
lean_dec(v_requestNo_3451_);
v___x_3474_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 1, v___x_3474_);
lean_ctor_set(v___x_3470_, 0, v___x_3473_);
v___x_3476_ = v___x_3470_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
size_t v_sz_3477_; size_t v___x_3478_; lean_object* v___x_3479_; 
v_sz_3477_ = lean_array_size(v_result_3468_);
v___x_3478_ = ((size_t)0ULL);
v___x_3479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___y_3467_, v_result_3468_, v_sz_3477_, v___x_3478_, v___x_3476_, v_a_3454_);
lean_dec(v_result_3468_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3497_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3482_ = v___x_3479_;
v_isShared_3483_ = v_isSharedCheck_3497_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3479_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3497_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v_fst_3484_; lean_object* v_snd_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3496_; 
v_fst_3484_ = lean_ctor_get(v_a_3480_, 0);
v_snd_3485_ = lean_ctor_get(v_a_3480_, 1);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_a_3480_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3487_ = v_a_3480_;
v_isShared_3488_ = v_isSharedCheck_3496_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_snd_3485_);
lean_inc(v_fst_3484_);
lean_dec(v_a_3480_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3496_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3489_, 0, v_item_3452_);
lean_ctor_set(v___x_3489_, 1, v_snd_3485_);
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 1, v_fst_3484_);
lean_ctor_set(v___x_3487_, 0, v___x_3489_);
v___x_3491_ = v___x_3487_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_fst_3484_);
v___x_3491_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3493_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v___x_3491_);
v___x_3493_ = v___x_3482_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v_item_3452_);
v_a_3498_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3479_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3479_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec(v_visited_3453_);
lean_dec_ref(v_item_3452_);
lean_dec(v_requestNo_3451_);
v_a_3511_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3464_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3464_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec_ref(v___x_3460_);
lean_dec(v_visited_3453_);
lean_dec_ref(v_item_3452_);
lean_dec(v_requestNo_3451_);
v_a_3519_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3463_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3463_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec(v_visited_3453_);
v___x_3527_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3528_, 0, v_item_3452_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v_requestNo_3451_);
v___x_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
return v___x_3530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(lean_object* v___x_3531_, lean_object* v_as_3532_, size_t v_sz_3533_, size_t v_i_3534_, lean_object* v_b_3535_, lean_object* v___y_3536_){
_start:
{
uint8_t v___x_3538_; 
v___x_3538_ = lean_usize_dec_lt(v_i_3534_, v_sz_3533_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; 
lean_dec(v___x_3531_);
v___x_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3539_, 0, v_b_3535_);
return v___x_3539_;
}
else
{
lean_object* v_fst_3540_; lean_object* v_snd_3541_; lean_object* v_a_3542_; lean_object* v___x_3543_; 
v_fst_3540_ = lean_ctor_get(v_b_3535_, 0);
lean_inc(v_fst_3540_);
v_snd_3541_ = lean_ctor_get(v_b_3535_, 1);
lean_inc(v_snd_3541_);
lean_dec_ref(v_b_3535_);
v_a_3542_ = lean_array_uget_borrowed(v_as_3532_, v_i_3534_);
lean_inc(v___x_3531_);
lean_inc(v_a_3542_);
v___x_3543_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_fst_3540_, v_a_3542_, v___x_3531_, v___y_3536_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v_fst_3545_; lean_object* v_snd_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3557_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref(v___x_3543_);
v_fst_3545_ = lean_ctor_get(v_a_3544_, 0);
v_snd_3546_ = lean_ctor_get(v_a_3544_, 1);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_a_3544_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3548_ = v_a_3544_;
v_isShared_3549_ = v_isSharedCheck_3557_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_snd_3546_);
lean_inc(v_fst_3545_);
lean_dec(v_a_3544_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3557_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3550_; lean_object* v___x_3552_; 
v___x_3550_ = lean_array_push(v_snd_3541_, v_fst_3545_);
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 1, v___x_3550_);
lean_ctor_set(v___x_3548_, 0, v_snd_3546_);
v___x_3552_ = v___x_3548_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_snd_3546_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
size_t v___x_3553_; size_t v___x_3554_; 
v___x_3553_ = ((size_t)1ULL);
v___x_3554_ = lean_usize_add(v_i_3534_, v___x_3553_);
v_i_3534_ = v___x_3554_;
v_b_3535_ = v___x_3552_;
goto _start;
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec(v_snd_3541_);
lean_dec(v___x_3531_);
v_a_3558_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3543_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3543_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2___boxed(lean_object* v___x_3566_, lean_object* v_as_3567_, lean_object* v_sz_3568_, lean_object* v_i_3569_, lean_object* v_b_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
size_t v_sz_boxed_3573_; size_t v_i_boxed_3574_; lean_object* v_res_3575_; 
v_sz_boxed_3573_ = lean_unbox_usize(v_sz_3568_);
lean_dec(v_sz_3568_);
v_i_boxed_3574_ = lean_unbox_usize(v_i_3569_);
lean_dec(v_i_3569_);
v_res_3575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___x_3566_, v_as_3567_, v_sz_boxed_3573_, v_i_boxed_3574_, v_b_3570_, v___y_3571_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v_as_3567_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___boxed(lean_object* v_requestNo_3576_, lean_object* v_item_3577_, lean_object* v_visited_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_requestNo_3576_, v_item_3577_, v_visited_3578_, v_a_3579_);
lean_dec_ref(v_a_3579_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(lean_object* v_v_3582_){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(v_v_3582_);
v___x_3584_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(lean_object* v_h_3585_, lean_object* v_r_3586_){
_start:
{
lean_object* v_id_3588_; lean_object* v_method_3589_; lean_object* v_param_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3610_; 
v_id_3588_ = lean_ctor_get(v_r_3586_, 0);
v_method_3589_ = lean_ctor_get(v_r_3586_, 1);
v_param_3590_ = lean_ctor_get(v_r_3586_, 2);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_r_3586_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3592_ = v_r_3586_;
v_isShared_3593_ = v_isSharedCheck_3610_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_param_3590_);
lean_inc(v_method_3589_);
lean_inc(v_id_3588_);
lean_dec(v_r_3586_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3610_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___y_3595_; lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(v_param_3590_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v___x_3601_; 
lean_dec_ref(v___x_3600_);
v___x_3601_ = lean_box(0);
v___y_3595_ = v___x_3601_;
goto v___jp_3594_;
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
v_a_3602_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3600_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3600_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
v___y_3595_ = v___x_3607_;
goto v___jp_3594_;
}
}
}
v___jp_3594_:
{
lean_object* v___x_3597_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 2, v___y_3595_);
v___x_3597_ = v___x_3592_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_id_3588_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_method_3589_);
lean_ctor_set(v_reuseFailAlloc_3599_, 2, v___y_3595_);
v___x_3597_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_IO_FS_Stream_writeLspMessage(v_h_3585_, v___x_3597_);
return v___x_3598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0___boxed(lean_object* v_h_3611_, lean_object* v_r_3612_, lean_object* v_a_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_h_3611_, v_r_3612_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(lean_object* v_r_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v_a_3619_; lean_object* v___x_3620_; 
v___x_3618_ = l_Lean_Lsp_Ipc_stdin(v_a_3616_);
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref(v___x_3618_);
v___x_3620_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_a_3619_, v_r_3615_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0___boxed(lean_object* v_r_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v_r_3621_, v_a_3622_);
lean_dec_ref(v_a_3622_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(lean_object* v_x_3627_){
_start:
{
if (lean_obj_tag(v_x_3627_) == 0)
{
lean_object* v___x_3628_; 
v___x_3628_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0));
return v___x_3628_;
}
else
{
lean_object* v___x_3629_; 
v___x_3629_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v_x_3627_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3629_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3629_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3646_; 
v_a_3638_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3640_ = v___x_3629_;
v_isShared_3641_ = v_isSharedCheck_3646_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3629_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3646_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3642_; lean_object* v___x_3644_; 
v___x_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3642_, 0, v_a_3638_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3642_);
v___x_3644_ = v___x_3640_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(lean_object* v_expectedID_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l_Lean_Lsp_Ipc_stdout(v_a_3648_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3794_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3653_ = v___x_3650_;
v_isShared_3654_ = v_isSharedCheck_3794_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3650_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3794_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3655_; 
v___x_3655_ = l_IO_FS_Stream_readLspMessage(v_a_3651_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3785_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3785_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3655_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3785_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___y_3661_; lean_object* v___y_3662_; 
switch(lean_obj_tag(v_a_3656_))
{
case 2:
{
lean_object* v_id_3668_; lean_object* v_result_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3713_; 
v_id_3668_ = lean_ctor_get(v_a_3656_, 0);
v_result_3669_ = lean_ctor_get(v_a_3656_, 1);
v_isSharedCheck_3713_ = !lean_is_exclusive(v_a_3656_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3671_ = v_a_3656_;
v_isShared_3672_ = v_isSharedCheck_3713_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_result_3669_);
lean_inc(v_id_3668_);
lean_dec(v_a_3656_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3713_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
uint8_t v___x_3673_; 
v___x_3673_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3668_, v_expectedID_3647_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3674_; lean_object* v___y_3676_; 
lean_del_object(v___x_3671_);
lean_dec(v_result_3669_);
lean_del_object(v___x_3653_);
v___x_3674_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3647_))
{
case 0:
{
lean_object* v_s_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v_s_3687_ = lean_ctor_get(v_expectedID_3647_, 0);
lean_inc_ref(v_s_3687_);
lean_dec_ref(v_expectedID_3647_);
v___x_3688_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3689_ = lean_string_append(v___x_3688_, v_s_3687_);
lean_dec_ref(v_s_3687_);
v___x_3690_ = lean_string_append(v___x_3689_, v___x_3688_);
v___y_3676_ = v___x_3690_;
goto v___jp_3675_;
}
case 1:
{
lean_object* v_n_3691_; lean_object* v___x_3692_; 
v_n_3691_ = lean_ctor_get(v_expectedID_3647_, 0);
lean_inc_ref(v_n_3691_);
lean_dec_ref(v_expectedID_3647_);
v___x_3692_ = l_Lean_JsonNumber_toString(v_n_3691_);
v___y_3676_ = v___x_3692_;
goto v___jp_3675_;
}
default: 
{
lean_object* v___x_3693_; 
v___x_3693_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3676_ = v___x_3693_;
goto v___jp_3675_;
}
}
v___jp_3675_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = lean_string_append(v___x_3674_, v___y_3676_);
lean_dec_ref(v___y_3676_);
v___x_3678_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3679_ = lean_string_append(v___x_3677_, v___x_3678_);
switch(lean_obj_tag(v_id_3668_))
{
case 0:
{
lean_object* v_s_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v_s_3680_ = lean_ctor_get(v_id_3668_, 0);
lean_inc_ref(v_s_3680_);
lean_dec_ref(v_id_3668_);
v___x_3681_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3682_ = lean_string_append(v___x_3681_, v_s_3680_);
lean_dec_ref(v_s_3680_);
v___x_3683_ = lean_string_append(v___x_3682_, v___x_3681_);
v___y_3661_ = v___x_3679_;
v___y_3662_ = v___x_3683_;
goto v___jp_3660_;
}
case 1:
{
lean_object* v_n_3684_; lean_object* v___x_3685_; 
v_n_3684_ = lean_ctor_get(v_id_3668_, 0);
lean_inc_ref(v_n_3684_);
lean_dec_ref(v_id_3668_);
v___x_3685_ = l_Lean_JsonNumber_toString(v_n_3684_);
v___y_3661_ = v___x_3679_;
v___y_3662_ = v___x_3685_;
goto v___jp_3660_;
}
default: 
{
lean_object* v___x_3686_; 
v___x_3686_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3661_ = v___x_3679_;
v___y_3662_ = v___x_3686_;
goto v___jp_3660_;
}
}
}
}
else
{
lean_object* v___x_3694_; 
lean_dec(v_id_3668_);
lean_del_object(v___x_3658_);
lean_inc(v_result_3669_);
v___x_3694_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(v_result_3669_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
lean_del_object(v___x_3671_);
lean_dec(v_expectedID_3647_);
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref(v___x_3694_);
v___x_3696_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3697_ = l_Lean_Json_compress(v_result_3669_);
v___x_3698_ = lean_string_append(v___x_3696_, v___x_3697_);
lean_dec_ref(v___x_3697_);
v___x_3699_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3700_ = lean_string_append(v___x_3698_, v___x_3699_);
v___x_3701_ = lean_string_append(v___x_3700_, v_a_3695_);
lean_dec(v_a_3695_);
v___x_3702_ = lean_mk_io_user_error(v___x_3701_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set_tag(v___x_3653_, 1);
lean_ctor_set(v___x_3653_, 0, v___x_3702_);
v___x_3704_ = v___x_3653_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; 
lean_dec(v_result_3669_);
v_a_3706_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3706_);
lean_dec_ref(v___x_3694_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set_tag(v___x_3671_, 0);
lean_ctor_set(v___x_3671_, 1, v_a_3706_);
lean_ctor_set(v___x_3671_, 0, v_expectedID_3647_);
v___x_3708_ = v___x_3671_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_expectedID_3647_);
lean_ctor_set(v_reuseFailAlloc_3712_, 1, v_a_3706_);
v___x_3708_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3710_; 
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3708_);
v___x_3710_ = v___x_3653_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3714_; uint8_t v_code_3715_; lean_object* v_message_3716_; lean_object* v_data_x3f_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___x_3749_; lean_object* v___y_3751_; 
lean_del_object(v___x_3658_);
lean_dec(v_expectedID_3647_);
v_id_3714_ = lean_ctor_get(v_a_3656_, 0);
lean_inc(v_id_3714_);
v_code_3715_ = lean_ctor_get_uint8(v_a_3656_, sizeof(void*)*3);
v_message_3716_ = lean_ctor_get(v_a_3656_, 1);
lean_inc_ref(v_message_3716_);
v_data_x3f_3717_ = lean_ctor_get(v_a_3656_, 2);
lean_inc(v_data_x3f_3717_);
lean_dec_ref(v_a_3656_);
v___x_3718_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3719_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3749_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3714_))
{
case 0:
{
lean_object* v_s_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
v_s_3767_ = lean_ctor_get(v_id_3714_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_id_3714_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v_id_3714_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_s_3767_);
lean_dec(v_id_3714_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
lean_ctor_set_tag(v___x_3769_, 3);
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_s_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
v___y_3751_ = v___x_3772_;
goto v___jp_3750_;
}
}
}
case 1:
{
lean_object* v_n_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
v_n_3775_ = lean_ctor_get(v_id_3714_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_id_3714_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v_id_3714_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_n_3775_);
lean_dec(v_id_3714_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
lean_ctor_set_tag(v___x_3777_, 2);
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_n_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
v___y_3751_ = v___x_3780_;
goto v___jp_3750_;
}
}
}
default: 
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_box(0);
v___y_3751_ = v___x_3783_;
goto v___jp_3750_;
}
}
v___jp_3720_:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_inc(v___y_3724_);
lean_inc_ref(v___y_3721_);
v___x_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___y_3721_);
lean_ctor_set(v___x_3725_, 1, v___y_3724_);
v___x_3726_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3727_, 0, v_message_3716_);
v___x_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3726_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = lean_box(0);
v___x_3730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3725_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3733_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3732_, v_data_x3f_3717_);
lean_dec(v_data_x3f_3717_);
v___x_3734_ = l_List_appendTR___redArg(v___x_3731_, v___x_3733_);
v___x_3735_ = l_Lean_Json_mkObj(v___x_3734_);
lean_inc_ref(v___y_3723_);
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___y_3723_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v___x_3729_);
v___x_3738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___y_3722_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3719_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = l_Lean_Json_mkObj(v___x_3739_);
v___x_3741_ = l_Lean_Json_compress(v___x_3740_);
v___x_3742_ = lean_string_append(v___x_3718_, v___x_3741_);
lean_dec_ref(v___x_3741_);
v___x_3743_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3744_ = lean_string_append(v___x_3742_, v___x_3743_);
v___x_3745_ = lean_mk_io_user_error(v___x_3744_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set_tag(v___x_3653_, 1);
lean_ctor_set(v___x_3653_, 0, v___x_3745_);
v___x_3747_ = v___x_3653_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
v___jp_3750_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3749_);
lean_ctor_set(v___x_3752_, 1, v___y_3751_);
v___x_3753_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3754_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3715_)
{
case 0:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3755_;
goto v___jp_3720_;
}
case 1:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3756_;
goto v___jp_3720_;
}
case 2:
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3757_;
goto v___jp_3720_;
}
case 3:
{
lean_object* v___x_3758_; 
v___x_3758_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3758_;
goto v___jp_3720_;
}
case 4:
{
lean_object* v___x_3759_; 
v___x_3759_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3759_;
goto v___jp_3720_;
}
case 5:
{
lean_object* v___x_3760_; 
v___x_3760_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3760_;
goto v___jp_3720_;
}
case 6:
{
lean_object* v___x_3761_; 
v___x_3761_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3761_;
goto v___jp_3720_;
}
case 7:
{
lean_object* v___x_3762_; 
v___x_3762_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3762_;
goto v___jp_3720_;
}
case 8:
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3763_;
goto v___jp_3720_;
}
case 9:
{
lean_object* v___x_3764_; 
v___x_3764_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3764_;
goto v___jp_3720_;
}
case 10:
{
lean_object* v___x_3765_; 
v___x_3765_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3765_;
goto v___jp_3720_;
}
default: 
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3721_ = v___x_3754_;
v___y_3722_ = v___x_3752_;
v___y_3723_ = v___x_3753_;
v___y_3724_ = v___x_3766_;
goto v___jp_3720_;
}
}
}
}
default: 
{
lean_del_object(v___x_3658_);
lean_dec(v_a_3656_);
lean_del_object(v___x_3653_);
goto _start;
}
}
v___jp_3660_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3663_ = lean_string_append(v___y_3661_, v___y_3662_);
lean_dec_ref(v___y_3662_);
v___x_3664_ = lean_mk_io_user_error(v___x_3663_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set_tag(v___x_3658_, 1);
lean_ctor_set(v___x_3658_, 0, v___x_3664_);
v___x_3666_ = v___x_3658_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_del_object(v___x_3653_);
lean_dec(v_expectedID_3647_);
v_a_3786_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3655_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3655_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_dec(v_expectedID_3647_);
v_a_3795_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3650_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3650_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1___boxed(lean_object* v_expectedID_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v_expectedID_3803_, v_a_3804_);
lean_dec_ref(v_a_3804_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports(lean_object* v_requestNo_3811_, lean_object* v_uri_3812_, lean_object* v_a_3813_){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_inc(v_requestNo_3811_);
v___x_3815_ = l_Lean_JsonNumber_fromNat(v_requestNo_3811_);
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
v___x_3817_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_3816_);
v___x_3818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
lean_ctor_set(v___x_3818_, 2, v_uri_3812_);
v___x_3819_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_3818_, v_a_3813_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v___x_3820_; 
lean_dec_ref(v___x_3819_);
v___x_3820_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_3816_, v_a_3813_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3879_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3823_ = v___x_3820_;
v_isShared_3824_ = v_isSharedCheck_3879_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3820_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3879_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v_result_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3877_; 
v_result_3825_ = lean_ctor_get(v_a_3821_, 1);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_a_3821_);
if (v_isSharedCheck_3877_ == 0)
{
lean_object* v_unused_3878_; 
v_unused_3878_ = lean_ctor_get(v_a_3821_, 0);
lean_dec(v_unused_3878_);
v___x_3827_ = v_a_3821_;
v_isShared_3828_ = v_isSharedCheck_3877_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_result_3825_);
lean_dec(v_a_3821_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3877_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = lean_unsigned_to_nat(1u);
v___x_3830_ = lean_nat_add(v_requestNo_3811_, v___x_3829_);
lean_dec(v_requestNo_3811_);
if (lean_obj_tag(v_result_3825_) == 1)
{
lean_object* v_val_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3869_; 
lean_del_object(v___x_3823_);
v_val_3831_ = lean_ctor_get(v_result_3825_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_result_3825_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3833_ = v_result_3825_;
v_isShared_3834_ = v_isSharedCheck_3869_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_val_3831_);
lean_dec(v_result_3825_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3869_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3835_; lean_object* v___x_3837_; 
v___x_3835_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 1, v___x_3835_);
lean_ctor_set(v___x_3827_, 0, v_val_3831_);
v___x_3837_ = v___x_3827_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_val_3831_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3838_ = lean_box(1);
v___x_3839_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v___x_3830_, v___x_3837_, v___x_3838_, v_a_3813_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3859_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3842_ = v___x_3839_;
v_isShared_3843_ = v_isSharedCheck_3859_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3859_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v_fst_3844_; lean_object* v_snd_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3858_; 
v_fst_3844_ = lean_ctor_get(v_a_3840_, 0);
v_snd_3845_ = lean_ctor_get(v_a_3840_, 1);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_a_3840_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3847_ = v_a_3840_;
v_isShared_3848_ = v_isSharedCheck_3858_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_snd_3845_);
lean_inc(v_fst_3844_);
lean_dec(v_a_3840_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3858_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v_fst_3844_);
v___x_3850_ = v___x_3833_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_fst_3844_);
v___x_3850_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
lean_object* v___x_3852_; 
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v___x_3850_);
v___x_3852_ = v___x_3847_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_snd_3845_);
v___x_3852_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3854_; 
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3852_);
v___x_3854_ = v___x_3842_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_del_object(v___x_3833_);
v_a_3860_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3839_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3839_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
}
}
else
{
lean_object* v___x_3870_; lean_object* v___x_3872_; 
lean_dec(v_result_3825_);
v___x_3870_ = lean_box(0);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 1, v___x_3830_);
lean_ctor_set(v___x_3827_, 0, v___x_3870_);
v___x_3872_ = v___x_3827_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v___x_3830_);
v___x_3872_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3874_; 
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 0, v___x_3872_);
v___x_3874_ = v___x_3823_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec(v_requestNo_3811_);
v_a_3880_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3820_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3820_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec_ref(v___x_3816_);
lean_dec(v_requestNo_3811_);
v_a_3888_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3819_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3819_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___boxed(lean_object* v_requestNo_3896_, lean_object* v_uri_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImports(v_requestNo_3896_, v_uri_3897_, v_a_3898_);
lean_dec_ref(v_a_3898_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(lean_object* v_v_3901_){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_v_3901_);
v___x_3903_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3902_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_v_3904_);
lean_dec_ref(v_v_3904_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(lean_object* v_h_3906_, lean_object* v_r_3907_){
_start:
{
lean_object* v_id_3909_; lean_object* v_method_3910_; lean_object* v_param_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3931_; 
v_id_3909_ = lean_ctor_get(v_r_3907_, 0);
v_method_3910_ = lean_ctor_get(v_r_3907_, 1);
v_param_3911_ = lean_ctor_get(v_r_3907_, 2);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_r_3907_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3913_ = v_r_3907_;
v_isShared_3914_ = v_isSharedCheck_3931_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_param_3911_);
lean_inc(v_method_3910_);
lean_inc(v_id_3909_);
lean_dec(v_r_3907_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3931_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___y_3916_; lean_object* v___x_3921_; 
v___x_3921_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_param_3911_);
lean_dec(v_param_3911_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v___x_3922_; 
lean_dec_ref(v___x_3921_);
v___x_3922_ = lean_box(0);
v___y_3916_ = v___x_3922_;
goto v___jp_3915_;
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
v_a_3923_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3921_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3921_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
v___y_3916_ = v___x_3928_;
goto v___jp_3915_;
}
}
}
v___jp_3915_:
{
lean_object* v___x_3918_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 2, v___y_3916_);
v___x_3918_ = v___x_3913_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_id_3909_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_method_3910_);
lean_ctor_set(v_reuseFailAlloc_3920_, 2, v___y_3916_);
v___x_3918_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3919_; 
v___x_3919_ = l_IO_FS_Stream_writeLspMessage(v_h_3906_, v___x_3918_);
return v___x_3919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0___boxed(lean_object* v_h_3932_, lean_object* v_r_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_h_3932_, v_r_3933_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(lean_object* v_r_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v___x_3939_; lean_object* v_a_3940_; lean_object* v___x_3941_; 
v___x_3939_ = l_Lean_Lsp_Ipc_stdin(v_a_3937_);
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref(v___x_3939_);
v___x_3941_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_a_3940_, v_r_3936_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0___boxed(lean_object* v_r_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v_r_3942_, v_a_3943_);
lean_dec_ref(v_a_3943_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(lean_object* v_requestNo_3947_, lean_object* v_item_3948_, lean_object* v_visited_3949_, lean_object* v_a_3950_){
_start:
{
lean_object* v_module_3952_; lean_object* v_name_3953_; uint8_t v___x_3954_; 
v_module_3952_ = lean_ctor_get(v_item_3948_, 0);
v_name_3953_ = lean_ctor_get(v_module_3952_, 0);
v___x_3954_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3953_, v_visited_3949_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
lean_inc(v_requestNo_3947_);
v___x_3955_ = l_Lean_JsonNumber_fromNat(v_requestNo_3947_);
v___x_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
v___x_3957_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0));
lean_inc_ref(v_module_3952_);
lean_inc_ref(v___x_3956_);
v___x_3958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3956_);
lean_ctor_set(v___x_3958_, 1, v___x_3957_);
lean_ctor_set(v___x_3958_, 2, v_module_3952_);
v___x_3959_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v___x_3958_, v_a_3950_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v___x_3960_; 
lean_dec_ref(v___x_3959_);
v___x_3960_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3956_, v_a_3950_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___y_3963_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref(v___x_3960_);
if (v___x_3954_ == 0)
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = lean_box(0);
lean_inc_ref(v_name_3953_);
v___x_4006_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3953_, v___x_4005_, v_visited_3949_);
v___y_3963_ = v___x_4006_;
goto v___jp_3962_;
}
else
{
v___y_3963_ = v_visited_3949_;
goto v___jp_3962_;
}
v___jp_3962_:
{
lean_object* v_result_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_4003_; 
v_result_3964_ = lean_ctor_get(v_a_3961_, 1);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_a_3961_);
if (v_isSharedCheck_4003_ == 0)
{
lean_object* v_unused_4004_; 
v_unused_4004_ = lean_ctor_get(v_a_3961_, 0);
lean_dec(v_unused_4004_);
v___x_3966_ = v_a_3961_;
v_isShared_3967_ = v_isSharedCheck_4003_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_result_3964_);
lean_dec(v_a_3961_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_4003_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3972_; 
v___x_3968_ = lean_unsigned_to_nat(1u);
v___x_3969_ = lean_nat_add(v_requestNo_3947_, v___x_3968_);
lean_dec(v_requestNo_3947_);
v___x_3970_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 1, v___x_3970_);
lean_ctor_set(v___x_3966_, 0, v___x_3969_);
v___x_3972_ = v___x_3966_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3969_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v___x_3970_);
v___x_3972_ = v_reuseFailAlloc_4002_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
size_t v_sz_3973_; size_t v___x_3974_; lean_object* v___x_3975_; 
v_sz_3973_ = lean_array_size(v_result_3964_);
v___x_3974_ = ((size_t)0ULL);
v___x_3975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___y_3963_, v_result_3964_, v_sz_3973_, v___x_3974_, v___x_3972_, v_a_3950_);
lean_dec(v_result_3964_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3993_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3978_ = v___x_3975_;
v_isShared_3979_ = v_isSharedCheck_3993_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3975_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3993_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v_fst_3980_; lean_object* v_snd_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3992_; 
v_fst_3980_ = lean_ctor_get(v_a_3976_, 0);
v_snd_3981_ = lean_ctor_get(v_a_3976_, 1);
v_isSharedCheck_3992_ = !lean_is_exclusive(v_a_3976_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3983_ = v_a_3976_;
v_isShared_3984_ = v_isSharedCheck_3992_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_snd_3981_);
lean_inc(v_fst_3980_);
lean_dec(v_a_3976_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3992_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3987_; 
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v_item_3948_);
lean_ctor_set(v___x_3985_, 1, v_snd_3981_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 1, v_fst_3980_);
lean_ctor_set(v___x_3983_, 0, v___x_3985_);
v___x_3987_ = v___x_3983_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3985_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v_fst_3980_);
v___x_3987_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3989_; 
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 0, v___x_3987_);
v___x_3989_ = v___x_3978_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec_ref(v_item_3948_);
v_a_3994_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3975_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3975_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec(v_visited_3949_);
lean_dec_ref(v_item_3948_);
lean_dec(v_requestNo_3947_);
v_a_4007_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3960_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3960_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec_ref(v___x_3956_);
lean_dec(v_visited_3949_);
lean_dec_ref(v_item_3948_);
lean_dec(v_requestNo_3947_);
v_a_4015_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_3959_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_3959_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
else
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
lean_dec(v_visited_3949_);
v___x_4023_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_4024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4024_, 0, v_item_3948_);
lean_ctor_set(v___x_4024_, 1, v___x_4023_);
v___x_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
lean_ctor_set(v___x_4025_, 1, v_requestNo_3947_);
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4025_);
return v___x_4026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(lean_object* v___x_4027_, lean_object* v_as_4028_, size_t v_sz_4029_, size_t v_i_4030_, lean_object* v_b_4031_, lean_object* v___y_4032_){
_start:
{
uint8_t v___x_4034_; 
v___x_4034_ = lean_usize_dec_lt(v_i_4030_, v_sz_4029_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4035_; 
lean_dec(v___x_4027_);
v___x_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4035_, 0, v_b_4031_);
return v___x_4035_;
}
else
{
lean_object* v_fst_4036_; lean_object* v_snd_4037_; lean_object* v_a_4038_; lean_object* v___x_4039_; 
v_fst_4036_ = lean_ctor_get(v_b_4031_, 0);
lean_inc(v_fst_4036_);
v_snd_4037_ = lean_ctor_get(v_b_4031_, 1);
lean_inc(v_snd_4037_);
lean_dec_ref(v_b_4031_);
v_a_4038_ = lean_array_uget_borrowed(v_as_4028_, v_i_4030_);
lean_inc(v___x_4027_);
lean_inc(v_a_4038_);
v___x_4039_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_fst_4036_, v_a_4038_, v___x_4027_, v___y_4032_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v_fst_4041_; lean_object* v_snd_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4053_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref(v___x_4039_);
v_fst_4041_ = lean_ctor_get(v_a_4040_, 0);
v_snd_4042_ = lean_ctor_get(v_a_4040_, 1);
v_isSharedCheck_4053_ = !lean_is_exclusive(v_a_4040_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4044_ = v_a_4040_;
v_isShared_4045_ = v_isSharedCheck_4053_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_snd_4042_);
lean_inc(v_fst_4041_);
lean_dec(v_a_4040_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4053_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4046_; lean_object* v___x_4048_; 
v___x_4046_ = lean_array_push(v_snd_4037_, v_fst_4041_);
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 1, v___x_4046_);
lean_ctor_set(v___x_4044_, 0, v_snd_4042_);
v___x_4048_ = v___x_4044_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_snd_4042_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v___x_4046_);
v___x_4048_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
size_t v___x_4049_; size_t v___x_4050_; 
v___x_4049_ = ((size_t)1ULL);
v___x_4050_ = lean_usize_add(v_i_4030_, v___x_4049_);
v_i_4030_ = v___x_4050_;
v_b_4031_ = v___x_4048_;
goto _start;
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec(v_snd_4037_);
lean_dec(v___x_4027_);
v_a_4054_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4039_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4039_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1___boxed(lean_object* v___x_4062_, lean_object* v_as_4063_, lean_object* v_sz_4064_, lean_object* v_i_4065_, lean_object* v_b_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
size_t v_sz_boxed_4069_; size_t v_i_boxed_4070_; lean_object* v_res_4071_; 
v_sz_boxed_4069_ = lean_unbox_usize(v_sz_4064_);
lean_dec(v_sz_4064_);
v_i_boxed_4070_ = lean_unbox_usize(v_i_4065_);
lean_dec(v_i_4065_);
v_res_4071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___x_4062_, v_as_4063_, v_sz_boxed_4069_, v_i_boxed_4070_, v_b_4066_, v___y_4067_);
lean_dec_ref(v___y_4067_);
lean_dec_ref(v_as_4063_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___boxed(lean_object* v_requestNo_4072_, lean_object* v_item_4073_, lean_object* v_visited_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_requestNo_4072_, v_item_4073_, v_visited_4074_, v_a_4075_);
lean_dec_ref(v_a_4075_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(lean_object* v_requestNo_4078_, lean_object* v_uri_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
lean_inc(v_requestNo_4078_);
v___x_4082_ = l_Lean_JsonNumber_fromNat(v_requestNo_4078_);
v___x_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
v___x_4084_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_4083_);
v___x_4085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4083_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
lean_ctor_set(v___x_4085_, 2, v_uri_4079_);
v___x_4086_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_4085_, v_a_4080_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v___x_4087_; 
lean_dec_ref(v___x_4086_);
v___x_4087_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_4083_, v_a_4080_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4146_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4146_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4146_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v_result_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4144_; 
v_result_4092_ = lean_ctor_get(v_a_4088_, 1);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_a_4088_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v_a_4088_, 0);
lean_dec(v_unused_4145_);
v___x_4094_ = v_a_4088_;
v_isShared_4095_ = v_isSharedCheck_4144_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_result_4092_);
lean_dec(v_a_4088_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4144_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4096_ = lean_unsigned_to_nat(1u);
v___x_4097_ = lean_nat_add(v_requestNo_4078_, v___x_4096_);
lean_dec(v_requestNo_4078_);
if (lean_obj_tag(v_result_4092_) == 1)
{
lean_object* v_val_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4136_; 
lean_del_object(v___x_4090_);
v_val_4098_ = lean_ctor_get(v_result_4092_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_result_4092_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4100_ = v_result_4092_;
v_isShared_4101_ = v_isSharedCheck_4136_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_val_4098_);
lean_dec(v_result_4092_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4136_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4102_; lean_object* v___x_4104_; 
v___x_4102_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 1, v___x_4102_);
lean_ctor_set(v___x_4094_, 0, v_val_4098_);
v___x_4104_ = v___x_4094_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_val_4098_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v___x_4102_);
v___x_4104_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = lean_box(1);
v___x_4106_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v___x_4097_, v___x_4104_, v___x_4105_, v_a_4080_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4126_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4109_ = v___x_4106_;
v_isShared_4110_ = v_isSharedCheck_4126_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4106_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4126_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v_fst_4111_; lean_object* v_snd_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4125_; 
v_fst_4111_ = lean_ctor_get(v_a_4107_, 0);
v_snd_4112_ = lean_ctor_get(v_a_4107_, 1);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_a_4107_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4114_ = v_a_4107_;
v_isShared_4115_ = v_isSharedCheck_4125_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_snd_4112_);
lean_inc(v_fst_4111_);
lean_dec(v_a_4107_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4125_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v_fst_4111_);
v___x_4117_ = v___x_4100_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_fst_4111_);
v___x_4117_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
lean_object* v___x_4119_; 
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 0, v___x_4117_);
v___x_4119_ = v___x_4114_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4117_);
lean_ctor_set(v_reuseFailAlloc_4123_, 1, v_snd_4112_);
v___x_4119_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
lean_object* v___x_4121_; 
if (v_isShared_4110_ == 0)
{
lean_ctor_set(v___x_4109_, 0, v___x_4119_);
v___x_4121_ = v___x_4109_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v___x_4119_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_del_object(v___x_4100_);
v_a_4127_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4106_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4106_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
}
else
{
lean_object* v___x_4137_; lean_object* v___x_4139_; 
lean_dec(v_result_4092_);
v___x_4137_ = lean_box(0);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 1, v___x_4097_);
lean_ctor_set(v___x_4094_, 0, v___x_4137_);
v___x_4139_ = v___x_4094_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4137_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v___x_4097_);
v___x_4139_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
lean_object* v___x_4141_; 
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4139_);
v___x_4141_ = v___x_4090_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec(v_requestNo_4078_);
v_a_4147_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4087_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4087_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec_ref(v___x_4083_);
lean_dec(v_requestNo_4078_);
v_a_4155_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4086_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4086_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy___boxed(lean_object* v_requestNo_4163_, lean_object* v_uri_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(v_requestNo_4163_, v_uri_4164_, v_a_4165_);
lean_dec_ref(v_a_4165_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object* v_lean_4170_, lean_object* v_args_4171_, lean_object* v_test_4172_){
_start:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; uint8_t v___x_4177_; uint8_t v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4174_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_4175_ = lean_box(0);
v___x_4176_ = ((lean_object*)(l_Lean_Lsp_Ipc_runWith___redArg___closed__0));
v___x_4177_ = 1;
v___x_4178_ = 0;
v___x_4179_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4179_, 0, v___x_4174_);
lean_ctor_set(v___x_4179_, 1, v_lean_4170_);
lean_ctor_set(v___x_4179_, 2, v_args_4171_);
lean_ctor_set(v___x_4179_, 3, v___x_4175_);
lean_ctor_set(v___x_4179_, 4, v___x_4176_);
lean_ctor_set_uint8(v___x_4179_, sizeof(void*)*5, v___x_4177_);
lean_ctor_set_uint8(v___x_4179_, sizeof(void*)*5 + 1, v___x_4178_);
v___x_4180_ = lean_io_process_spawn(v___x_4179_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v___x_4182_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref(v___x_4180_);
v___x_4182_ = lean_apply_2(v_test_4172_, v_a_4181_, lean_box(0));
return v___x_4182_;
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
lean_dec_ref(v_test_4172_);
v_a_4183_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4180_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4180_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg___boxed(lean_object* v_lean_4191_, lean_object* v_args_4192_, lean_object* v_test_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4191_, v_args_4192_, v_test_4193_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object* v_00_u03b1_4196_, lean_object* v_lean_4197_, lean_object* v_args_4198_, lean_object* v_test_4199_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4197_, v_args_4198_, v_test_4199_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___boxed(lean_object* v_00_u03b1_4202_, lean_object* v_lean_4203_, lean_object* v_args_4204_, lean_object* v_test_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Lsp_Ipc_runWith(v_00_u03b1_4202_, v_lean_4203_, v_args_4204_, v_test_4205_);
return v_res_4207_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Communication(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Ipc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp_Communication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Ipc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Ipc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Communication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Ipc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Ipc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Ipc(builtin);
}
#ifdef __cplusplus
}
#endif
