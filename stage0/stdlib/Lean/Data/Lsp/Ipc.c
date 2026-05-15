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
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Data.Lsp.Ipc"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Lsp.Ipc.shutdown"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: result.isNull\n      "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "exit"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Expected id "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", got id "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_shutdown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "shutdown"};
static const lean_object* l_Lean_Lsp_Ipc_shutdown___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_shutdown___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "textDocument/publishDiagnostics"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Waiting for diagnostics failed: "};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1_value;
static const lean_string_object l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Cannot decode publishDiagnostics parameters\n"};
static const lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2 = (const lean_object*)&l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Waiting for ILeans failed: "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_waitForILeans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "$/lean/waitForILeans"};
static const lean_object* l_Lean_Lsp_Ipc_waitForILeans___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_waitForILeans___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_74_; lean_object* v___f_75_; lean_object* v___x_3697__overap_76_; lean_object* v___x_77_; 
v___x_74_ = lean_obj_once(&l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0, &l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0_once, _init_l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0);
v___f_75_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_75_, 0, v___x_74_);
v___x_3697__overap_76_ = lean_panic_fn_borrowed(v___f_75_, v_msg_71_);
lean_dec_ref(v___f_75_);
lean_inc_ref(v___y_72_);
v___x_77_ = lean_apply_2(v___x_3697__overap_76_, v___y_72_, lean_box(0));
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
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_114_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2));
v___x_115_ = lean_unsigned_to_nat(6u);
v___x_116_ = lean_unsigned_to_nat(56u);
v___x_117_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1));
v___x_118_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0));
v___x_119_ = l_mkPanicMessageWithDecl(v___x_118_, v___x_117_, v___x_116_, v___x_115_, v___x_114_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v___x_130_, lean_object* v_requestNo_131_, lean_object* v___y_132_){
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
v___x_142_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3, &l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3);
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
v___x_175_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_176_ = l_Nat_reprFast(v_requestNo_131_);
v___x_177_ = lean_string_append(v___x_175_, v___x_176_);
lean_dec_ref(v___x_176_);
v___x_178_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_179_ = lean_string_append(v___x_177_, v___x_178_);
switch(lean_obj_tag(v_id_139_))
{
case 0:
{
lean_object* v_s_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_s_187_ = lean_ctor_get(v_id_139_, 0);
lean_inc_ref(v_s_187_);
lean_dec_ref(v_id_139_);
v___x_188_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
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
v___x_193_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
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
v___x_164_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5));
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___boxed(lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v___x_206_, lean_object* v_requestNo_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_204_, v_a_205_, v___x_206_, v_requestNo_207_, v___y_208_);
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
v___x_259_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_246_, v_a_248_, v___x_254_, v_requestNo_242_, v_a_243_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v___x_279_, lean_object* v_requestNo_280_, lean_object* v_inst_281_, lean_object* v_a_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_277_, v_a_278_, v___x_279_, v_requestNo_280_, v___y_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___boxed(lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v___x_288_, lean_object* v_requestNo_289_, lean_object* v_inst_290_, lean_object* v_a_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(v_a_286_, v_a_287_, v___x_288_, v_requestNo_289_, v_inst_290_, v_a_291_, v___y_292_);
lean_dec_ref(v___y_292_);
lean_dec(v___x_288_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_a_298_; lean_object* v___x_299_; 
v___x_297_ = l_Lean_Lsp_Ipc_stdout(v_a_295_);
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref(v___x_297_);
v___x_299_ = l_IO_FS_Stream_readLspMessage(v_a_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage___boxed(lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Lsp_Ipc_readMessage(v_a_300_);
lean_dec_ref(v_a_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg(lean_object* v_expectedMethod_303_, lean_object* v_inst_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_a_308_; lean_object* v___x_309_; 
v___x_307_ = l_Lean_Lsp_Ipc_stdout(v_a_305_);
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref(v___x_307_);
v___x_309_ = l_IO_FS_Stream_readLspRequestAs___redArg(v_a_308_, v_expectedMethod_303_, v_inst_304_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg___boxed(lean_object* v_expectedMethod_310_, lean_object* v_inst_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Lsp_Ipc_readRequestAs___redArg(v_expectedMethod_310_, v_inst_311_, v_a_312_);
lean_dec_ref(v_a_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object* v_expectedMethod_315_, lean_object* v_00_u03b1_316_, lean_object* v_inst_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Lsp_Ipc_readRequestAs___redArg(v_expectedMethod_315_, v_inst_317_, v_a_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___boxed(lean_object* v_expectedMethod_321_, lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Lsp_Ipc_readRequestAs(v_expectedMethod_321_, v_00_u03b1_322_, v_inst_323_, v_a_324_);
lean_dec_ref(v_a_324_);
return v_res_326_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(32700u);
v___x_345_ = lean_nat_to_int(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14);
v___x_347_ = lean_int_neg(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15);
v___x_349_ = l_Lean_JsonNumber_fromInt(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16);
v___x_351_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(32600u);
v___x_353_ = lean_nat_to_int(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18);
v___x_355_ = lean_int_neg(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19);
v___x_357_ = l_Lean_JsonNumber_fromInt(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20);
v___x_359_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(32601u);
v___x_361_ = lean_nat_to_int(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22);
v___x_363_ = lean_int_neg(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23);
v___x_365_ = l_Lean_JsonNumber_fromInt(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24);
v___x_367_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(32602u);
v___x_369_ = lean_nat_to_int(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26);
v___x_371_ = lean_int_neg(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27);
v___x_373_ = l_Lean_JsonNumber_fromInt(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28);
v___x_375_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(32603u);
v___x_377_ = lean_nat_to_int(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30);
v___x_379_ = lean_int_neg(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31);
v___x_381_ = l_Lean_JsonNumber_fromInt(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32);
v___x_383_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(32002u);
v___x_385_ = lean_nat_to_int(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34);
v___x_387_ = lean_int_neg(v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35);
v___x_389_ = l_Lean_JsonNumber_fromInt(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36);
v___x_391_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(32001u);
v___x_393_ = lean_nat_to_int(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38);
v___x_395_ = lean_int_neg(v___x_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39);
v___x_397_ = l_Lean_JsonNumber_fromInt(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40);
v___x_399_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_unsigned_to_nat(32801u);
v___x_401_ = lean_nat_to_int(v___x_400_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42);
v___x_403_ = lean_int_neg(v___x_402_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43);
v___x_405_ = l_Lean_JsonNumber_fromInt(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44);
v___x_407_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(32800u);
v___x_409_ = lean_nat_to_int(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46);
v___x_411_ = lean_int_neg(v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47);
v___x_413_ = l_Lean_JsonNumber_fromInt(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48);
v___x_415_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_unsigned_to_nat(32900u);
v___x_417_ = lean_nat_to_int(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50);
v___x_419_ = lean_int_neg(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51);
v___x_421_ = l_Lean_JsonNumber_fromInt(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52);
v___x_423_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(32901u);
v___x_425_ = lean_nat_to_int(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54);
v___x_427_ = lean_int_neg(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55);
v___x_429_ = l_Lean_JsonNumber_fromInt(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56);
v___x_431_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(32902u);
v___x_433_ = lean_nat_to_int(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58);
v___x_435_ = lean_int_neg(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59);
v___x_437_ = l_Lean_JsonNumber_fromInt(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60);
v___x_439_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg(lean_object* v_expectedID_440_, lean_object* v_inst_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Lsp_Ipc_stdout(v_a_442_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_589_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_589_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_589_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_589_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; 
v___x_449_ = l_IO_FS_Stream_readLspMessage(v_a_445_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_580_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_580_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_580_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_580_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___y_455_; lean_object* v___y_456_; 
switch(lean_obj_tag(v_a_450_))
{
case 2:
{
lean_object* v_id_462_; lean_object* v_result_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_507_; 
v_id_462_ = lean_ctor_get(v_a_450_, 0);
v_result_463_ = lean_ctor_get(v_a_450_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_507_ == 0)
{
v___x_465_ = v_a_450_;
v_isShared_466_ = v_isSharedCheck_507_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_result_463_);
lean_inc(v_id_462_);
lean_dec(v_a_450_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_507_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
uint8_t v___x_467_; 
v___x_467_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_462_, v_expectedID_440_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___y_470_; 
lean_del_object(v___x_465_);
lean_dec(v_result_463_);
lean_del_object(v___x_447_);
lean_dec_ref(v_inst_441_);
v___x_468_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_440_))
{
case 0:
{
lean_object* v_s_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_s_481_ = lean_ctor_get(v_expectedID_440_, 0);
lean_inc_ref(v_s_481_);
lean_dec_ref(v_expectedID_440_);
v___x_482_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_483_ = lean_string_append(v___x_482_, v_s_481_);
lean_dec_ref(v_s_481_);
v___x_484_ = lean_string_append(v___x_483_, v___x_482_);
v___y_470_ = v___x_484_;
goto v___jp_469_;
}
case 1:
{
lean_object* v_n_485_; lean_object* v___x_486_; 
v_n_485_ = lean_ctor_get(v_expectedID_440_, 0);
lean_inc_ref(v_n_485_);
lean_dec_ref(v_expectedID_440_);
v___x_486_ = l_Lean_JsonNumber_toString(v_n_485_);
v___y_470_ = v___x_486_;
goto v___jp_469_;
}
default: 
{
lean_object* v___x_487_; 
v___x_487_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_470_ = v___x_487_;
goto v___jp_469_;
}
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_string_append(v___x_468_, v___y_470_);
lean_dec_ref(v___y_470_);
v___x_472_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_473_ = lean_string_append(v___x_471_, v___x_472_);
switch(lean_obj_tag(v_id_462_))
{
case 0:
{
lean_object* v_s_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_s_474_ = lean_ctor_get(v_id_462_, 0);
lean_inc_ref(v_s_474_);
lean_dec_ref(v_id_462_);
v___x_475_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_476_ = lean_string_append(v___x_475_, v_s_474_);
lean_dec_ref(v_s_474_);
v___x_477_ = lean_string_append(v___x_476_, v___x_475_);
v___y_455_ = v___x_473_;
v___y_456_ = v___x_477_;
goto v___jp_454_;
}
case 1:
{
lean_object* v_n_478_; lean_object* v___x_479_; 
v_n_478_ = lean_ctor_get(v_id_462_, 0);
lean_inc_ref(v_n_478_);
lean_dec_ref(v_id_462_);
v___x_479_ = l_Lean_JsonNumber_toString(v_n_478_);
v___y_455_ = v___x_473_;
v___y_456_ = v___x_479_;
goto v___jp_454_;
}
default: 
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_455_ = v___x_473_;
v___y_456_ = v___x_480_;
goto v___jp_454_;
}
}
}
}
else
{
lean_object* v___x_488_; 
lean_dec(v_id_462_);
lean_del_object(v___x_452_);
lean_inc(v_result_463_);
v___x_488_ = lean_apply_1(v_inst_441_, v_result_463_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
lean_del_object(v___x_465_);
lean_dec(v_expectedID_440_);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
v___x_490_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_491_ = l_Lean_Json_compress(v_result_463_);
v___x_492_ = lean_string_append(v___x_490_, v___x_491_);
lean_dec_ref(v___x_491_);
v___x_493_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_494_ = lean_string_append(v___x_492_, v___x_493_);
v___x_495_ = lean_string_append(v___x_494_, v_a_489_);
lean_dec(v_a_489_);
v___x_496_ = lean_mk_io_user_error(v___x_495_);
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 1);
lean_ctor_set(v___x_447_, 0, v___x_496_);
v___x_498_ = v___x_447_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; 
lean_dec(v_result_463_);
v_a_500_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_500_);
lean_dec_ref(v___x_488_);
if (v_isShared_466_ == 0)
{
lean_ctor_set_tag(v___x_465_, 0);
lean_ctor_set(v___x_465_, 1, v_a_500_);
lean_ctor_set(v___x_465_, 0, v_expectedID_440_);
v___x_502_ = v___x_465_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_expectedID_440_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_a_500_);
v___x_502_ = v_reuseFailAlloc_506_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_504_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_502_);
v___x_504_ = v___x_447_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_508_; uint8_t v_code_509_; lean_object* v_message_510_; lean_object* v_data_x3f_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___x_544_; lean_object* v___y_546_; 
lean_del_object(v___x_452_);
lean_dec_ref(v_inst_441_);
lean_dec(v_expectedID_440_);
v_id_508_ = lean_ctor_get(v_a_450_, 0);
lean_inc(v_id_508_);
v_code_509_ = lean_ctor_get_uint8(v_a_450_, sizeof(void*)*3);
v_message_510_ = lean_ctor_get(v_a_450_, 1);
lean_inc_ref(v_message_510_);
v_data_x3f_511_ = lean_ctor_get(v_a_450_, 2);
lean_inc(v_data_x3f_511_);
lean_dec_ref(v_a_450_);
v___x_512_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_513_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3));
v___x_514_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_544_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_508_))
{
case 0:
{
lean_object* v_s_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
v_s_562_ = lean_ctor_get(v_id_508_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v_id_508_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v_id_508_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_s_562_);
lean_dec(v_id_508_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 3);
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_s_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
v___y_546_ = v___x_567_;
goto v___jp_545_;
}
}
}
case 1:
{
lean_object* v_n_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
v_n_570_ = lean_ctor_get(v_id_508_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_id_508_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v_id_508_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_n_570_);
lean_dec(v_id_508_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set_tag(v___x_572_, 2);
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_n_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
v___y_546_ = v___x_575_;
goto v___jp_545_;
}
}
}
default: 
{
lean_object* v___x_578_; 
v___x_578_ = lean_box(0);
v___y_546_ = v___x_578_;
goto v___jp_545_;
}
}
v___jp_515_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___y_518_);
lean_ctor_set(v___x_520_, 1, v___y_519_);
v___x_521_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_522_, 0, v_message_510_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_box(0);
v___x_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_520_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_528_ = l_Lean_Json_opt___redArg(v___x_513_, v___x_527_, v_data_x3f_511_);
v___x_529_ = l_List_appendTR___redArg(v___x_526_, v___x_528_);
v___x_530_ = l_Lean_Json_mkObj(v___x_529_);
lean_dec(v___x_529_);
lean_inc_ref(v___y_517_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___y_517_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v___x_524_);
v___x_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_516_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_514_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = l_Lean_Json_mkObj(v___x_534_);
lean_dec_ref(v___x_534_);
v___x_536_ = l_Lean_Json_compress(v___x_535_);
v___x_537_ = lean_string_append(v___x_512_, v___x_536_);
lean_dec_ref(v___x_536_);
v___x_538_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_539_ = lean_string_append(v___x_537_, v___x_538_);
v___x_540_ = lean_mk_io_user_error(v___x_539_);
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 1);
lean_ctor_set(v___x_447_, 0, v___x_540_);
v___x_542_ = v___x_447_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_544_);
lean_ctor_set(v___x_547_, 1, v___y_546_);
v___x_548_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_549_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_509_)
{
case 0:
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_550_;
goto v___jp_515_;
}
case 1:
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_551_;
goto v___jp_515_;
}
case 2:
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_552_;
goto v___jp_515_;
}
case 3:
{
lean_object* v___x_553_; 
v___x_553_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_553_;
goto v___jp_515_;
}
case 4:
{
lean_object* v___x_554_; 
v___x_554_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_554_;
goto v___jp_515_;
}
case 5:
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_555_;
goto v___jp_515_;
}
case 6:
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_556_;
goto v___jp_515_;
}
case 7:
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_557_;
goto v___jp_515_;
}
case 8:
{
lean_object* v___x_558_; 
v___x_558_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_558_;
goto v___jp_515_;
}
case 9:
{
lean_object* v___x_559_; 
v___x_559_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_559_;
goto v___jp_515_;
}
case 10:
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_560_;
goto v___jp_515_;
}
default: 
{
lean_object* v___x_561_; 
v___x_561_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
v___y_519_ = v___x_561_;
goto v___jp_515_;
}
}
}
}
default: 
{
lean_del_object(v___x_452_);
lean_dec(v_a_450_);
lean_del_object(v___x_447_);
goto _start;
}
}
v___jp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_457_ = lean_string_append(v___y_455_, v___y_456_);
lean_dec_ref(v___y_456_);
v___x_458_ = lean_mk_io_user_error(v___x_457_);
if (v_isShared_453_ == 0)
{
lean_ctor_set_tag(v___x_452_, 1);
lean_ctor_set(v___x_452_, 0, v___x_458_);
v___x_460_ = v___x_452_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_del_object(v___x_447_);
lean_dec_ref(v_inst_441_);
lean_dec(v_expectedID_440_);
v_a_581_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_449_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_449_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v_inst_441_);
lean_dec(v_expectedID_440_);
v_a_590_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_444_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_444_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___boxed(lean_object* v_expectedID_598_, lean_object* v_inst_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Lsp_Ipc_readResponseAs___redArg(v_expectedID_598_, v_inst_599_, v_a_600_);
lean_dec_ref(v_a_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object* v_expectedID_603_, lean_object* v_00_u03b1_604_, lean_object* v_inst_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Lsp_Ipc_readResponseAs___redArg(v_expectedID_603_, v_inst_605_, v_a_606_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___boxed(lean_object* v_expectedID_609_, lean_object* v_00_u03b1_610_, lean_object* v_inst_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Lsp_Ipc_readResponseAs(v_expectedID_609_, v_00_u03b1_610_, v_inst_611_, v_a_612_);
lean_dec_ref(v_a_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object* v_a_615_){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_618_ = lean_io_process_child_wait(v___x_617_, v_a_615_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Lsp_Ipc_waitForExit(v_a_619_);
lean_dec_ref(v_a_619_);
return v_res_621_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(lean_object* v_d1_622_, lean_object* v_d2_623_){
_start:
{
uint8_t v___y_625_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_628_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d1_622_);
v___x_629_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d2_623_);
v___x_630_ = l_Lean_Lsp_instOrdRange_ord(v___x_628_, v___x_629_);
lean_dec_ref(v___x_629_);
lean_dec_ref(v___x_628_);
if (v___x_630_ == 1)
{
lean_object* v_message_631_; lean_object* v_message_632_; uint8_t v___x_633_; 
v_message_631_ = lean_ctor_get(v_d1_622_, 6);
v_message_632_ = lean_ctor_get(v_d2_623_, 6);
v___x_633_ = lean_string_dec_lt(v_message_631_, v_message_632_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; 
v___x_634_ = lean_string_dec_eq(v_message_631_, v_message_632_);
if (v___x_634_ == 0)
{
return v___x_634_;
}
else
{
v___y_625_ = v___x_630_;
goto v___jp_624_;
}
}
else
{
return v___x_633_;
}
}
else
{
v___y_625_ = v___x_630_;
goto v___jp_624_;
}
v___jp_624_:
{
if (v___y_625_ == 2)
{
uint8_t v___x_626_; 
v___x_626_ = 0;
return v___x_626_;
}
else
{
uint8_t v___x_627_; 
v___x_627_ = 1;
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed(lean_object* v_d1_635_, lean_object* v_d2_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(v_d1_635_, v_d2_636_);
lean_dec_ref(v_d2_636_);
lean_dec_ref(v_d1_635_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(lean_object* v_p_640_){
_start:
{
lean_object* v_uri_641_; lean_object* v_version_x3f_642_; lean_object* v_isIncremental_x3f_643_; lean_object* v_diagnostics_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_655_; 
v_uri_641_ = lean_ctor_get(v_p_640_, 0);
v_version_x3f_642_ = lean_ctor_get(v_p_640_, 1);
v_isIncremental_x3f_643_ = lean_ctor_get(v_p_640_, 2);
v_diagnostics_644_ = lean_ctor_get(v_p_640_, 3);
v_isSharedCheck_655_ = !lean_is_exclusive(v_p_640_);
if (v_isSharedCheck_655_ == 0)
{
v___x_646_ = v_p_640_;
v_isShared_647_ = v_isSharedCheck_655_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_diagnostics_644_);
lean_inc(v_isIncremental_x3f_643_);
lean_inc(v_version_x3f_642_);
lean_inc(v_uri_641_);
lean_dec(v_p_640_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_655_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___f_648_; lean_object* v___x_649_; lean_object* v_sorted_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v___f_648_ = ((lean_object*)(l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0));
v___x_649_ = lean_array_to_list(v_diagnostics_644_);
v_sorted_650_ = l_List_mergeSort___redArg(v___x_649_, v___f_648_);
v___x_651_ = lean_array_mk(v_sorted_650_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 3, v___x_651_);
v___x_653_ = v___x_646_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_uri_641_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_version_x3f_642_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_isIncremental_x3f_643_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(lean_object* v_prev_x3f_659_, lean_object* v_next_660_){
_start:
{
lean_object* v_uri_661_; lean_object* v_version_x3f_662_; lean_object* v_isIncremental_x3f_663_; lean_object* v_diagnostics_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_687_; 
v_uri_661_ = lean_ctor_get(v_next_660_, 0);
v_version_x3f_662_ = lean_ctor_get(v_next_660_, 1);
v_isIncremental_x3f_663_ = lean_ctor_get(v_next_660_, 2);
v_diagnostics_664_ = lean_ctor_get(v_next_660_, 3);
v_isSharedCheck_687_ = !lean_is_exclusive(v_next_660_);
if (v_isSharedCheck_687_ == 0)
{
v___x_666_ = v_next_660_;
v_isShared_667_ = v_isSharedCheck_687_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_diagnostics_664_);
lean_inc(v_isIncremental_x3f_663_);
lean_inc(v_version_x3f_662_);
lean_inc(v_uri_661_);
lean_dec(v_next_660_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_687_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v_replace_670_; 
v___x_668_ = ((lean_object*)(l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams___closed__0));
lean_inc_ref(v_diagnostics_664_);
lean_inc(v_version_x3f_662_);
lean_inc_ref(v_uri_661_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 2, v___x_668_);
v_replace_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_uri_661_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_version_x3f_662_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_diagnostics_664_);
v_replace_670_ = v_reuseFailAlloc_686_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
if (lean_obj_tag(v_prev_x3f_659_) == 1)
{
if (lean_obj_tag(v_isIncremental_x3f_663_) == 0)
{
lean_dec_ref(v_prev_x3f_659_);
lean_dec_ref(v_diagnostics_664_);
lean_dec(v_version_x3f_662_);
lean_dec_ref(v_uri_661_);
return v_replace_670_;
}
else
{
lean_object* v_val_671_; uint8_t v___x_672_; 
v_val_671_ = lean_ctor_get(v_isIncremental_x3f_663_, 0);
lean_inc(v_val_671_);
lean_dec_ref(v_isIncremental_x3f_663_);
v___x_672_ = lean_unbox(v_val_671_);
lean_dec(v_val_671_);
if (v___x_672_ == 0)
{
lean_dec_ref(v_prev_x3f_659_);
lean_dec_ref(v_diagnostics_664_);
lean_dec(v_version_x3f_662_);
lean_dec_ref(v_uri_661_);
return v_replace_670_;
}
else
{
lean_object* v_val_673_; lean_object* v_diagnostics_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v_replace_670_);
v_val_673_ = lean_ctor_get(v_prev_x3f_659_, 0);
lean_inc(v_val_673_);
lean_dec_ref(v_prev_x3f_659_);
v_diagnostics_674_ = lean_ctor_get(v_val_673_, 3);
v_isSharedCheck_682_ = !lean_is_exclusive(v_val_673_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; lean_object* v_unused_684_; lean_object* v_unused_685_; 
v_unused_683_ = lean_ctor_get(v_val_673_, 2);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_val_673_, 1);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_val_673_, 0);
lean_dec(v_unused_685_);
v___x_676_ = v_val_673_;
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_diagnostics_674_);
lean_dec(v_val_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = l_Array_append___redArg(v_diagnostics_674_, v_diagnostics_664_);
lean_dec_ref(v_diagnostics_664_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 3, v___x_678_);
lean_ctor_set(v___x_676_, 2, v___x_668_);
lean_ctor_set(v___x_676_, 1, v_version_x3f_662_);
lean_ctor_set(v___x_676_, 0, v_uri_661_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_uri_661_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_version_x3f_662_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
else
{
lean_dec_ref(v_diagnostics_664_);
lean_dec(v_isIncremental_x3f_663_);
lean_dec(v_version_x3f_662_);
lean_dec_ref(v_uri_661_);
lean_dec(v_prev_x3f_659_);
return v_replace_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object* v_waitForDiagnosticsId_691_, lean_object* v_accumulated_x3f_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Lsp_Ipc_readMessage(v_a_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_765_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_765_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_765_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_765_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
switch(lean_obj_tag(v_a_696_))
{
case 2:
{
lean_object* v_id_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_726_; 
v_id_700_ = lean_ctor_get(v_a_696_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v_a_696_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_a_696_, 1);
lean_dec(v_unused_727_);
v___x_702_ = v_a_696_;
v_isShared_703_ = v_isSharedCheck_726_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_id_700_);
lean_dec(v_a_696_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_726_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_700_, v_waitForDiagnosticsId_691_);
lean_dec(v_id_700_);
if (v___x_704_ == 0)
{
lean_del_object(v___x_702_);
lean_del_object(v___x_698_);
goto _start;
}
else
{
if (lean_obj_tag(v_accumulated_x3f_692_) == 0)
{
lean_object* v___x_706_; lean_object* v___x_708_; 
lean_del_object(v___x_702_);
v___x_706_ = lean_box(0);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_706_);
v___x_708_ = v___x_698_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
else
{
lean_object* v_val_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_725_; 
v_val_710_ = lean_ctor_get(v_accumulated_x3f_692_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_accumulated_x3f_692_);
if (v_isSharedCheck_725_ == 0)
{
v___x_712_ = v_accumulated_x3f_692_;
v_isShared_713_ = v_isSharedCheck_725_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_val_710_);
lean_dec(v_accumulated_x3f_692_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_725_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_715_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(v_val_710_);
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 0);
lean_ctor_set(v___x_702_, 1, v___x_715_);
lean_ctor_set(v___x_702_, 0, v___x_714_);
v___x_717_ = v___x_702_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_724_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_717_);
v___x_719_ = v___x_712_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_719_);
v___x_721_ = v___x_698_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
}
}
case 3:
{
lean_object* v_id_728_; lean_object* v_message_729_; uint8_t v___x_730_; 
v_id_728_ = lean_ctor_get(v_a_696_, 0);
lean_inc(v_id_728_);
v_message_729_ = lean_ctor_get(v_a_696_, 1);
lean_inc_ref(v_message_729_);
lean_dec_ref(v_a_696_);
v___x_730_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_728_, v_waitForDiagnosticsId_691_);
lean_dec(v_id_728_);
if (v___x_730_ == 0)
{
lean_dec_ref(v_message_729_);
lean_del_object(v___x_698_);
goto _start;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
lean_dec(v_accumulated_x3f_692_);
v___x_732_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1));
v___x_733_ = lean_string_append(v___x_732_, v_message_729_);
lean_dec_ref(v_message_729_);
v___x_734_ = lean_mk_io_user_error(v___x_733_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 1);
lean_ctor_set(v___x_698_, 0, v___x_734_);
v___x_736_ = v___x_698_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
case 1:
{
lean_object* v_method_738_; lean_object* v_params_x3f_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_method_738_ = lean_ctor_get(v_a_696_, 0);
lean_inc_ref(v_method_738_);
v_params_x3f_739_ = lean_ctor_get(v_a_696_, 1);
lean_inc(v_params_x3f_739_);
lean_dec_ref(v_a_696_);
v___x_740_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_741_ = lean_string_dec_eq(v_method_738_, v___x_740_);
lean_dec_ref(v_method_738_);
if (v___x_741_ == 0)
{
lean_dec(v_params_x3f_739_);
lean_del_object(v___x_698_);
goto _start;
}
else
{
if (lean_obj_tag(v_params_x3f_739_) == 1)
{
lean_object* v_val_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_762_; 
v_val_743_ = lean_ctor_get(v_params_x3f_739_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v_params_x3f_739_);
if (v_isSharedCheck_762_ == 0)
{
v___x_745_ = v_params_x3f_739_;
v_isShared_746_ = v_isSharedCheck_762_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_val_743_);
lean_dec(v_params_x3f_739_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_762_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = l_Lean_Json_Structured_toJson(v_val_743_);
v___x_748_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(v___x_747_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
lean_del_object(v___x_745_);
lean_dec(v_accumulated_x3f_692_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v___x_748_);
v___x_750_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2));
v___x_751_ = lean_string_append(v___x_750_, v_a_749_);
lean_dec(v_a_749_);
v___x_752_ = lean_mk_io_user_error(v___x_751_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 1);
lean_ctor_set(v___x_698_, 0, v___x_752_);
v___x_754_ = v___x_698_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
lean_del_object(v___x_698_);
v_a_756_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_756_);
lean_dec_ref(v___x_748_);
v___x_757_ = l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(v_accumulated_x3f_692_, v_a_756_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_757_);
v___x_759_ = v___x_745_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_761_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
v_accumulated_x3f_692_ = v___x_759_;
goto _start;
}
}
}
}
else
{
lean_dec(v_params_x3f_739_);
lean_del_object(v___x_698_);
goto _start;
}
}
}
default: 
{
lean_del_object(v___x_698_);
lean_dec(v_a_696_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_accumulated_x3f_692_);
v_a_766_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_695_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_695_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object* v_waitForDiagnosticsId_774_, lean_object* v_accumulated_x3f_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_774_, v_accumulated_x3f_775_, v_a_776_);
lean_dec_ref(v_a_776_);
lean_dec(v_waitForDiagnosticsId_774_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(lean_object* v_v_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(v_v_779_);
v___x_781_ = l_Lean_Json_Structured_fromJson_x3f(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object* v_h_782_, lean_object* v_r_783_){
_start:
{
lean_object* v_id_785_; lean_object* v_method_786_; lean_object* v_param_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_807_; 
v_id_785_ = lean_ctor_get(v_r_783_, 0);
v_method_786_ = lean_ctor_get(v_r_783_, 1);
v_param_787_ = lean_ctor_get(v_r_783_, 2);
v_isSharedCheck_807_ = !lean_is_exclusive(v_r_783_);
if (v_isSharedCheck_807_ == 0)
{
v___x_789_ = v_r_783_;
v_isShared_790_ = v_isSharedCheck_807_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_param_787_);
lean_inc(v_method_786_);
lean_inc(v_id_785_);
lean_dec(v_r_783_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_807_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___y_792_; lean_object* v___x_797_; 
v___x_797_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(v_param_787_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v___x_798_; 
lean_dec_ref(v___x_797_);
v___x_798_ = lean_box(0);
v___y_792_ = v___x_798_;
goto v___jp_791_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_a_799_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_797_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_797_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
v___y_792_ = v___x_804_;
goto v___jp_791_;
}
}
}
v___jp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 2, v___y_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_id_785_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_method_786_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v___y_792_);
v___x_794_ = v_reuseFailAlloc_796_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; 
v___x_795_ = l_IO_FS_Stream_writeLspMessage(v_h_782_, v___x_794_);
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0___boxed(lean_object* v_h_808_, lean_object* v_r_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_h_808_, v_r_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object* v_r_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_815_; lean_object* v_a_816_; lean_object* v___x_817_; 
v___x_815_ = l_Lean_Lsp_Ipc_stdin(v_a_813_);
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref(v___x_815_);
v___x_817_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_a_816_, v_r_812_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0___boxed(lean_object* v_r_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v_r_818_, v_a_819_);
lean_dec_ref(v_a_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object* v_waitForDiagnosticsId_823_, lean_object* v_target_824_, lean_object* v_version_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_828_ = ((lean_object*)(l_Lean_Lsp_Ipc_collectDiagnostics___closed__0));
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v_target_824_);
lean_ctor_set(v___x_829_, 1, v_version_825_);
lean_inc(v_waitForDiagnosticsId_823_);
v___x_830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_830_, 0, v_waitForDiagnosticsId_823_);
lean_ctor_set(v___x_830_, 1, v___x_828_);
lean_ctor_set(v___x_830_, 2, v___x_829_);
v___x_831_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v___x_830_, v_a_826_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec_ref(v___x_831_);
v___x_832_ = lean_box(0);
v___x_833_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_823_, v___x_832_, v_a_826_);
lean_dec(v_waitForDiagnosticsId_823_);
return v___x_833_;
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_waitForDiagnosticsId_823_);
v_a_834_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_831_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_831_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
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
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
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
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___boxed(lean_object* v_waitForDiagnosticsId_842_, lean_object* v_target_843_, lean_object* v_version_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Lsp_Ipc_collectDiagnostics(v_waitForDiagnosticsId_842_, v_target_843_, v_version_844_, v_a_845_);
lean_dec_ref(v_a_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(lean_object* v_v_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(v_v_848_);
v___x_850_ = l_Lean_Json_Structured_fromJson_x3f(v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object* v_h_851_, lean_object* v_r_852_){
_start:
{
lean_object* v_id_854_; lean_object* v_method_855_; lean_object* v_param_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_876_; 
v_id_854_ = lean_ctor_get(v_r_852_, 0);
v_method_855_ = lean_ctor_get(v_r_852_, 1);
v_param_856_ = lean_ctor_get(v_r_852_, 2);
v_isSharedCheck_876_ = !lean_is_exclusive(v_r_852_);
if (v_isSharedCheck_876_ == 0)
{
v___x_858_ = v_r_852_;
v_isShared_859_ = v_isSharedCheck_876_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_param_856_);
lean_inc(v_method_855_);
lean_inc(v_id_854_);
lean_dec(v_r_852_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_876_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___y_861_; lean_object* v___x_866_; 
v___x_866_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(v_param_856_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v___x_867_; 
lean_dec_ref(v___x_866_);
v___x_867_ = lean_box(0);
v___y_861_ = v___x_867_;
goto v___jp_860_;
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_866_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_866_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
v___y_861_ = v___x_873_;
goto v___jp_860_;
}
}
}
v___jp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 2, v___y_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_id_854_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_method_855_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v___y_861_);
v___x_863_ = v_reuseFailAlloc_865_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; 
v___x_864_ = l_IO_FS_Stream_writeLspMessage(v_h_851_, v___x_863_);
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0___boxed(lean_object* v_h_877_, lean_object* v_r_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_h_877_, v_r_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object* v_r_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; lean_object* v_a_885_; lean_object* v___x_886_; 
v___x_884_ = l_Lean_Lsp_Ipc_stdin(v_a_882_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref(v___x_884_);
v___x_886_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_a_885_, v_r_881_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0___boxed(lean_object* v_r_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v_r_887_, v_a_888_);
lean_dec_ref(v_a_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(lean_object* v_waitForILeansId_897_, lean_object* v___y_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Lsp_Ipc_readMessage(v___y_898_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_923_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_923_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_923_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_923_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
switch(lean_obj_tag(v_a_901_))
{
case 2:
{
lean_object* v_id_905_; uint8_t v___x_906_; 
v_id_905_ = lean_ctor_get(v_a_901_, 0);
lean_inc(v_id_905_);
lean_dec_ref(v_a_901_);
v___x_906_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_905_, v_waitForILeansId_897_);
lean_dec(v_id_905_);
if (v___x_906_ == 0)
{
lean_del_object(v___x_903_);
goto _start;
}
else
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1));
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_908_);
v___x_910_ = v___x_903_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
case 3:
{
lean_object* v_id_912_; lean_object* v_message_913_; uint8_t v___x_914_; 
v_id_912_ = lean_ctor_get(v_a_901_, 0);
lean_inc(v_id_912_);
v_message_913_ = lean_ctor_get(v_a_901_, 1);
lean_inc_ref(v_message_913_);
lean_dec_ref(v_a_901_);
v___x_914_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_912_, v_waitForILeansId_897_);
lean_dec(v_id_912_);
if (v___x_914_ == 0)
{
lean_dec_ref(v_message_913_);
lean_del_object(v___x_903_);
goto _start;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_916_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2));
v___x_917_ = lean_string_append(v___x_916_, v_message_913_);
lean_dec_ref(v_message_913_);
v___x_918_ = lean_mk_io_user_error(v___x_917_);
if (v_isShared_904_ == 0)
{
lean_ctor_set_tag(v___x_903_, 1);
lean_ctor_set(v___x_903_, 0, v___x_918_);
v___x_920_ = v___x_903_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
default: 
{
lean_del_object(v___x_903_);
lean_dec(v_a_901_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_900_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_900_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___boxed(lean_object* v_waitForILeansId_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_932_, v___y_933_);
lean_dec_ref(v___y_933_);
lean_dec(v_waitForILeansId_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object* v_waitForILeansId_937_, lean_object* v_target_938_, lean_object* v_version_939_, lean_object* v_a_940_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_942_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v_target_938_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_version_939_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
lean_inc(v_waitForILeansId_937_);
v___x_946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_946_, 0, v_waitForILeansId_937_);
lean_ctor_set(v___x_946_, 1, v___x_942_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
v___x_947_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_946_, v_a_940_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v___x_948_; 
lean_dec_ref(v___x_947_);
v___x_948_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_937_, v_a_940_);
lean_dec(v_waitForILeansId_937_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_962_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_962_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_962_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_962_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_fst_953_; 
v_fst_953_ = lean_ctor_get(v_a_949_, 0);
lean_inc(v_fst_953_);
lean_dec(v_a_949_);
if (lean_obj_tag(v_fst_953_) == 0)
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_box(0);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_954_);
v___x_956_ = v___x_951_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
else
{
lean_object* v_val_958_; lean_object* v___x_960_; 
v_val_958_ = lean_ctor_get(v_fst_953_, 0);
lean_inc(v_val_958_);
lean_dec_ref(v_fst_953_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v_val_958_);
v___x_960_ = v___x_951_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_val_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
else
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_a_963_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_970_ == 0)
{
v___x_965_ = v___x_948_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_948_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_963_);
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
else
{
lean_dec(v_waitForILeansId_937_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans___boxed(lean_object* v_waitForILeansId_971_, lean_object* v_target_972_, lean_object* v_version_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Lsp_Ipc_waitForILeans(v_waitForILeansId_971_, v_target_972_, v_version_973_, v_a_974_);
lean_dec_ref(v_a_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(lean_object* v_waitForILeansId_977_, lean_object* v_inst_978_, lean_object* v_a_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_977_, v___y_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___boxed(lean_object* v_waitForILeansId_983_, lean_object* v_inst_984_, lean_object* v_a_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(v_waitForILeansId_983_, v_inst_984_, v_a_985_, v___y_986_);
lean_dec_ref(v___y_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_waitForILeansId_983_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans(lean_object* v_waitForILeansId_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_994_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_995_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0));
lean_inc(v_waitForILeansId_991_);
v___x_996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_996_, 0, v_waitForILeansId_991_);
lean_ctor_set(v___x_996_, 1, v___x_994_);
lean_ctor_set(v___x_996_, 2, v___x_995_);
v___x_997_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_996_, v_a_992_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; 
lean_dec_ref(v___x_997_);
v___x_998_ = l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_991_, v_a_992_);
lean_dec(v_waitForILeansId_991_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1012_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1012_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_fst_1003_; 
v_fst_1003_ = lean_ctor_get(v_a_999_, 0);
lean_inc(v_fst_1003_);
lean_dec(v_a_999_);
if (lean_obj_tag(v_fst_1003_) == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_box(0);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1004_);
v___x_1006_ = v___x_1001_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
else
{
lean_object* v_val_1008_; lean_object* v___x_1010_; 
v_val_1008_ = lean_ctor_get(v_fst_1003_, 0);
lean_inc(v_val_1008_);
lean_dec_ref(v_fst_1003_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_val_1008_);
v___x_1010_ = v___x_1001_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_val_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_a_1013_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_998_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_998_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_dec(v_waitForILeansId_991_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___boxed(lean_object* v_waitForILeansId_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Lsp_Ipc_waitForWatchdogILeans(v_waitForILeansId_1021_, v_a_1022_);
lean_dec_ref(v_a_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(lean_object* v_j_1025_, lean_object* v_k_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = l_Lean_Json_getObjValD(v_j_1025_, v_k_1026_);
v___x_1028_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0___boxed(lean_object* v_j_1029_, lean_object* v_k_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_j_1029_, v_k_1030_);
lean_dec_ref(v_k_1030_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_1032_, size_t v_i_1033_, lean_object* v_bs_1034_){
_start:
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_usize_dec_lt(v_i_1033_, v_sz_1032_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1036_, 0, v_bs_1034_);
return v___x_1036_;
}
else
{
lean_object* v_v_1037_; lean_object* v___x_1038_; 
v_v_1037_ = lean_array_uget_borrowed(v_bs_1034_, v_i_1033_);
lean_inc(v_v_1037_);
v___x_1038_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_v_1037_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v_bs_1034_);
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
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
lean_object* v_a_1047_; lean_object* v___x_1048_; lean_object* v_bs_x27_1049_; size_t v___x_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
v_a_1047_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1047_);
lean_dec_ref(v___x_1038_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v_bs_x27_1049_ = lean_array_uset(v_bs_1034_, v_i_1033_, v___x_1048_);
v___x_1050_ = ((size_t)1ULL);
v___x_1051_ = lean_usize_add(v_i_1033_, v___x_1050_);
v___x_1052_ = lean_array_uset(v_bs_x27_1049_, v_i_1033_, v_a_1047_);
v_i_1033_ = v___x_1051_;
v_bs_1034_ = v___x_1052_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1054_, lean_object* v_i_1055_, lean_object* v_bs_1056_){
_start:
{
size_t v_sz_boxed_1057_; size_t v_i_boxed_1058_; lean_object* v_res_1059_; 
v_sz_boxed_1057_ = lean_unbox_usize(v_sz_1054_);
lean_dec(v_sz_1054_);
v_i_boxed_1058_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_res_1059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_1057_, v_i_boxed_1058_, v_bs_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_1061_){
_start:
{
if (lean_obj_tag(v_x_1061_) == 4)
{
lean_object* v_elems_1062_; size_t v_sz_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
v_elems_1062_ = lean_ctor_get(v_x_1061_, 0);
lean_inc_ref(v_elems_1062_);
lean_dec_ref(v_x_1061_);
v_sz_1063_ = lean_array_size(v_elems_1062_);
v___x_1064_ = ((size_t)0ULL);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_1063_, v___x_1064_, v_elems_1062_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1066_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1067_ = lean_unsigned_to_nat(80u);
v___x_1068_ = l_Lean_Json_pretty(v_x_1061_, v___x_1067_);
v___x_1069_ = lean_string_append(v___x_1066_, v___x_1068_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1071_ = lean_string_append(v___x_1069_, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(lean_object* v_j_1073_, lean_object* v_k_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = l_Lean_Json_getObjValD(v_j_1073_, v_k_1074_);
v___x_1076_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1___boxed(lean_object* v_j_1077_, lean_object* v_k_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_j_1077_, v_k_1078_);
lean_dec_ref(v_k_1078_);
return v_res_1079_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = 1;
v___x_1085_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9));
v___x_1086_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1085_, v___x_1084_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = 1;
v___x_1098_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5));
v___x_1099_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1098_, v___x_1097_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_1101_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6);
v___x_1102_ = lean_string_append(v___x_1101_, v___x_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_1104_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1105_ = lean_string_append(v___x_1104_, v___x_1103_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1107_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11);
v___x_1108_ = lean_string_append(v___x_1107_, v___x_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = 1;
v___x_1113_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15));
v___x_1114_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1113_, v___x_1112_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16);
v___x_1116_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1117_ = lean_string_append(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1119_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17);
v___x_1120_ = lean_string_append(v___x_1119_, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = 1;
v___x_1125_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20));
v___x_1126_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1125_, v___x_1124_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_1128_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1129_ = lean_string_append(v___x_1128_, v___x_1127_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1130_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1131_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22);
v___x_1132_ = lean_string_append(v___x_1131_, v___x_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(lean_object* v_json_1133_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_1133_);
v___x_1135_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_json_1133_, v___x_1134_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v_json_1133_);
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1140_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13);
v___x_1141_ = lean_string_append(v___x_1140_, v_a_1136_);
lean_dec(v_a_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1141_);
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_json_1133_);
v_a_1146_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1135_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1135_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 0);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_a_1154_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1154_);
lean_dec_ref(v___x_1135_);
v___x_1155_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
lean_inc(v_json_1133_);
v___x_1156_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_json_1133_, v___x_1155_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v_a_1154_);
lean_dec(v_json_1133_);
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1166_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1166_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1161_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18);
v___x_1162_ = lean_string_append(v___x_1161_, v_a_1157_);
lean_dec(v_a_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1162_);
v___x_1164_ = v___x_1159_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_a_1154_);
lean_dec(v_json_1133_);
v_a_1167_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1156_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1156_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 0);
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_a_1175_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___x_1156_);
v___x_1176_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1177_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_json_1133_, v___x_1176_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_a_1175_);
lean_dec(v_a_1154_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1187_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1187_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1182_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23);
v___x_1183_ = lean_string_append(v___x_1182_, v_a_1178_);
lean_dec(v_a_1178_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1183_);
v___x_1185_ = v___x_1180_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
else
{
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_a_1175_);
lean_dec(v_a_1154_);
v_a_1188_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1177_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1177_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set_tag(v___x_1190_, 0);
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
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
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1204_; 
v_a_1196_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1198_ = v___x_1177_;
v_isShared_1199_ = v_isSharedCheck_1204_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1177_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1204_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1200_, 0, v_a_1154_);
lean_ctor_set(v___x_1200_, 1, v_a_1175_);
lean_ctor_set(v___x_1200_, 2, v_a_1196_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1200_);
v___x_1202_ = v___x_1198_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(size_t v_sz_1205_, size_t v_i_1206_, lean_object* v_bs_1207_){
_start:
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_usize_dec_lt(v_i_1206_, v_sz_1205_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_bs_1207_);
return v___x_1209_;
}
else
{
lean_object* v_v_1210_; lean_object* v___x_1211_; 
v_v_1210_ = lean_array_uget_borrowed(v_bs_1207_, v_i_1206_);
lean_inc(v_v_1210_);
v___x_1211_ = l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(v_v_1210_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_bs_1207_);
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1221_; lean_object* v_bs_x27_1222_; size_t v___x_1223_; size_t v___x_1224_; lean_object* v___x_1225_; 
v_a_1220_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1220_);
lean_dec_ref(v___x_1211_);
v___x_1221_ = lean_unsigned_to_nat(0u);
v_bs_x27_1222_ = lean_array_uset(v_bs_1207_, v_i_1206_, v___x_1221_);
v___x_1223_ = ((size_t)1ULL);
v___x_1224_ = lean_usize_add(v_i_1206_, v___x_1223_);
v___x_1225_ = lean_array_uset(v_bs_x27_1222_, v_i_1206_, v_a_1220_);
v_i_1206_ = v___x_1224_;
v_bs_1207_ = v___x_1225_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(lean_object* v_x_1227_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 4)
{
lean_object* v_elems_1228_; size_t v_sz_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v_elems_1228_ = lean_ctor_get(v_x_1227_, 0);
lean_inc_ref(v_elems_1228_);
lean_dec_ref(v_x_1227_);
v_sz_1229_ = lean_array_size(v_elems_1228_);
v___x_1230_ = ((size_t)0ULL);
v___x_1231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_1229_, v___x_1230_, v_elems_1228_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1232_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1233_ = lean_unsigned_to_nat(80u);
v___x_1234_ = l_Lean_Json_pretty(v_x_1227_, v___x_1233_);
v___x_1235_ = lean_string_append(v___x_1232_, v___x_1234_);
lean_dec_ref(v___x_1234_);
v___x_1236_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1237_ = lean_string_append(v___x_1235_, v___x_1236_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(lean_object* v_j_1239_, lean_object* v_k_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = l_Lean_Json_getObjValD(v_j_1239_, v_k_1240_);
v___x_1242_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2___boxed(lean_object* v_j_1243_, lean_object* v_k_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_j_1243_, v_k_1244_);
lean_dec_ref(v_k_1244_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1246_, lean_object* v_i_1247_, lean_object* v_bs_1248_){
_start:
{
size_t v_sz_boxed_1249_; size_t v_i_boxed_1250_; lean_object* v_res_1251_; 
v_sz_boxed_1249_ = lean_unbox_usize(v_sz_1246_);
lean_dec(v_sz_1246_);
v_i_boxed_1250_ = lean_unbox_usize(v_i_1247_);
lean_dec(v_i_1247_);
v_res_1251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_boxed_1249_, v_i_boxed_1250_, v_bs_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
if (lean_obj_tag(v_a_1254_) == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_array_to_list(v_a_1255_);
return v___x_1256_;
}
else
{
lean_object* v_head_1257_; lean_object* v_tail_1258_; lean_object* v___x_1259_; 
v_head_1257_ = lean_ctor_get(v_a_1254_, 0);
lean_inc(v_head_1257_);
v_tail_1258_ = lean_ctor_get(v_a_1254_, 1);
lean_inc(v_tail_1258_);
lean_dec_ref(v_a_1254_);
v___x_1259_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1255_, v_head_1257_);
v_a_1254_ = v_tail_1258_;
v_a_1255_ = v___x_1259_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(size_t v_sz_1261_, size_t v_i_1262_, lean_object* v_bs_1263_){
_start:
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_usize_dec_lt(v_i_1262_, v_sz_1261_);
if (v___x_1264_ == 0)
{
return v_bs_1263_;
}
else
{
lean_object* v_v_1265_; lean_object* v___x_1266_; lean_object* v_bs_x27_1267_; lean_object* v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; 
v_v_1265_ = lean_array_uget(v_bs_1263_, v_i_1262_);
v___x_1266_ = lean_unsigned_to_nat(0u);
v_bs_x27_1267_ = lean_array_uset(v_bs_1263_, v_i_1262_, v___x_1266_);
v___x_1268_ = l_Lean_Lsp_instToJsonRange_toJson(v_v_1265_);
v___x_1269_ = ((size_t)1ULL);
v___x_1270_ = lean_usize_add(v_i_1262_, v___x_1269_);
v___x_1271_ = lean_array_uset(v_bs_x27_1267_, v_i_1262_, v___x_1268_);
v_i_1262_ = v___x_1270_;
v_bs_1263_ = v___x_1271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1273_, lean_object* v_i_1274_, lean_object* v_bs_1275_){
_start:
{
size_t v_sz_boxed_1276_; size_t v_i_boxed_1277_; lean_object* v_res_1278_; 
v_sz_boxed_1276_ = lean_unbox_usize(v_sz_1273_);
lean_dec(v_sz_1273_);
v_i_boxed_1277_ = lean_unbox_usize(v_i_1274_);
lean_dec(v_i_1274_);
v_res_1278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_boxed_1276_, v_i_boxed_1277_, v_bs_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(lean_object* v_a_1279_){
_start:
{
size_t v_sz_1280_; size_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_sz_1280_ = lean_array_size(v_a_1279_);
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_1280_, v___x_1281_, v_a_1279_);
v___x_1283_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(lean_object* v_x_1286_){
_start:
{
lean_object* v_item_1287_; lean_object* v_fromRanges_1288_; lean_object* v_children_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_item_1287_ = lean_ctor_get(v_x_1286_, 0);
lean_inc_ref(v_item_1287_);
v_fromRanges_1288_ = lean_ctor_get(v_x_1286_, 1);
lean_inc_ref(v_fromRanges_1288_);
v_children_1289_ = lean_ctor_get(v_x_1286_, 2);
lean_inc_ref(v_children_1289_);
lean_dec_ref(v_x_1286_);
v___x_1290_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_1291_ = l_Lean_Lsp_instToJsonCallHierarchyItem_toJson(v_item_1287_);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = lean_box(0);
v___x_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
v___x_1296_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(v_fromRanges_1288_);
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1295_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
v___x_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v___x_1293_);
v___x_1299_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1300_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(v_children_1289_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1293_);
v___x_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v___x_1293_);
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1298_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1294_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_1307_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_1305_, v___x_1306_);
v___x_1308_ = l_Lean_Json_mkObj(v___x_1307_);
lean_dec(v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(size_t v_sz_1309_, size_t v_i_1310_, lean_object* v_bs_1311_){
_start:
{
uint8_t v___x_1312_; 
v___x_1312_ = lean_usize_dec_lt(v_i_1310_, v_sz_1309_);
if (v___x_1312_ == 0)
{
return v_bs_1311_;
}
else
{
lean_object* v_v_1313_; lean_object* v___x_1314_; lean_object* v_bs_x27_1315_; lean_object* v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; lean_object* v___x_1319_; 
v_v_1313_ = lean_array_uget(v_bs_1311_, v_i_1310_);
v___x_1314_ = lean_unsigned_to_nat(0u);
v_bs_x27_1315_ = lean_array_uset(v_bs_1311_, v_i_1310_, v___x_1314_);
v___x_1316_ = l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(v_v_1313_);
v___x_1317_ = ((size_t)1ULL);
v___x_1318_ = lean_usize_add(v_i_1310_, v___x_1317_);
v___x_1319_ = lean_array_uset(v_bs_x27_1315_, v_i_1310_, v___x_1316_);
v_i_1310_ = v___x_1318_;
v_bs_1311_ = v___x_1319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(lean_object* v_a_1321_){
_start:
{
size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_sz_1322_ = lean_array_size(v_a_1321_);
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_1322_, v___x_1323_, v_a_1321_);
v___x_1325_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2___boxed(lean_object* v_sz_1326_, lean_object* v_i_1327_, lean_object* v_bs_1328_){
_start:
{
size_t v_sz_boxed_1329_; size_t v_i_boxed_1330_; lean_object* v_res_1331_; 
v_sz_boxed_1329_ = lean_unbox_usize(v_sz_1326_);
lean_dec(v_sz_1326_);
v_i_boxed_1330_ = lean_unbox_usize(v_i_1327_);
lean_dec(v_i_1327_);
v_res_1331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_boxed_1329_, v_i_boxed_1330_, v_bs_1328_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(lean_object* v_k_1334_, lean_object* v_v_1335_, lean_object* v_t_1336_){
_start:
{
if (lean_obj_tag(v_t_1336_) == 0)
{
lean_object* v_size_1337_; lean_object* v_k_1338_; lean_object* v_v_1339_; lean_object* v_l_1340_; lean_object* v_r_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1622_; 
v_size_1337_ = lean_ctor_get(v_t_1336_, 0);
v_k_1338_ = lean_ctor_get(v_t_1336_, 1);
v_v_1339_ = lean_ctor_get(v_t_1336_, 2);
v_l_1340_ = lean_ctor_get(v_t_1336_, 3);
v_r_1341_ = lean_ctor_get(v_t_1336_, 4);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_t_1336_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1343_ = v_t_1336_;
v_isShared_1344_ = v_isSharedCheck_1622_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_r_1341_);
lean_inc(v_l_1340_);
lean_inc(v_v_1339_);
lean_inc(v_k_1338_);
lean_inc(v_size_1337_);
lean_dec(v_t_1336_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1622_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
uint8_t v___x_1345_; 
v___x_1345_ = lean_string_dec_lt(v_k_1334_, v_k_1338_);
if (v___x_1345_ == 0)
{
uint8_t v___x_1346_; 
v___x_1346_ = lean_string_dec_eq(v_k_1334_, v_k_1338_);
if (v___x_1346_ == 0)
{
lean_object* v_impl_1347_; lean_object* v___x_1348_; 
lean_dec(v_size_1337_);
v_impl_1347_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1334_, v_v_1335_, v_r_1341_);
v___x_1348_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1340_) == 0)
{
lean_object* v_size_1349_; lean_object* v_size_1350_; lean_object* v_k_1351_; lean_object* v_v_1352_; lean_object* v_l_1353_; lean_object* v_r_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_size_1349_ = lean_ctor_get(v_l_1340_, 0);
v_size_1350_ = lean_ctor_get(v_impl_1347_, 0);
lean_inc(v_size_1350_);
v_k_1351_ = lean_ctor_get(v_impl_1347_, 1);
lean_inc(v_k_1351_);
v_v_1352_ = lean_ctor_get(v_impl_1347_, 2);
lean_inc(v_v_1352_);
v_l_1353_ = lean_ctor_get(v_impl_1347_, 3);
lean_inc(v_l_1353_);
v_r_1354_ = lean_ctor_get(v_impl_1347_, 4);
lean_inc(v_r_1354_);
v___x_1355_ = lean_unsigned_to_nat(3u);
v___x_1356_ = lean_nat_mul(v___x_1355_, v_size_1349_);
v___x_1357_ = lean_nat_dec_lt(v___x_1356_, v_size_1350_);
lean_dec(v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
lean_dec(v_r_1354_);
lean_dec(v_l_1353_);
lean_dec(v_v_1352_);
lean_dec(v_k_1351_);
v___x_1358_ = lean_nat_add(v___x_1348_, v_size_1349_);
v___x_1359_ = lean_nat_add(v___x_1358_, v_size_1350_);
lean_dec(v_size_1350_);
lean_dec(v___x_1358_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v_impl_1347_);
lean_ctor_set(v___x_1343_, 0, v___x_1359_);
v___x_1361_ = v___x_1343_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_l_1340_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_impl_1347_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
else
{
lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1426_; 
v_isSharedCheck_1426_ = !lean_is_exclusive(v_impl_1347_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; lean_object* v_unused_1428_; lean_object* v_unused_1429_; lean_object* v_unused_1430_; lean_object* v_unused_1431_; 
v_unused_1427_ = lean_ctor_get(v_impl_1347_, 4);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_impl_1347_, 3);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_impl_1347_, 2);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_impl_1347_, 1);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_impl_1347_, 0);
lean_dec(v_unused_1431_);
v___x_1364_ = v_impl_1347_;
v_isShared_1365_ = v_isSharedCheck_1426_;
goto v_resetjp_1363_;
}
else
{
lean_dec(v_impl_1347_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1426_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_size_1366_; lean_object* v_k_1367_; lean_object* v_v_1368_; lean_object* v_l_1369_; lean_object* v_r_1370_; lean_object* v_size_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v_size_1366_ = lean_ctor_get(v_l_1353_, 0);
v_k_1367_ = lean_ctor_get(v_l_1353_, 1);
v_v_1368_ = lean_ctor_get(v_l_1353_, 2);
v_l_1369_ = lean_ctor_get(v_l_1353_, 3);
v_r_1370_ = lean_ctor_get(v_l_1353_, 4);
v_size_1371_ = lean_ctor_get(v_r_1354_, 0);
v___x_1372_ = lean_unsigned_to_nat(2u);
v___x_1373_ = lean_nat_mul(v___x_1372_, v_size_1371_);
v___x_1374_ = lean_nat_dec_lt(v_size_1366_, v___x_1373_);
lean_dec(v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1402_; 
lean_inc(v_r_1370_);
lean_inc(v_l_1369_);
lean_inc(v_v_1368_);
lean_inc(v_k_1367_);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_l_1353_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; lean_object* v_unused_1404_; lean_object* v_unused_1405_; lean_object* v_unused_1406_; lean_object* v_unused_1407_; 
v_unused_1403_ = lean_ctor_get(v_l_1353_, 4);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_l_1353_, 3);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_l_1353_, 2);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_l_1353_, 1);
lean_dec(v_unused_1406_);
v_unused_1407_ = lean_ctor_get(v_l_1353_, 0);
lean_dec(v_unused_1407_);
v___x_1376_ = v_l_1353_;
v_isShared_1377_ = v_isSharedCheck_1402_;
goto v_resetjp_1375_;
}
else
{
lean_dec(v_l_1353_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1402_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1392_; 
v___x_1378_ = lean_nat_add(v___x_1348_, v_size_1349_);
v___x_1379_ = lean_nat_add(v___x_1378_, v_size_1350_);
lean_dec(v_size_1350_);
if (lean_obj_tag(v_l_1369_) == 0)
{
lean_object* v_size_1400_; 
v_size_1400_ = lean_ctor_get(v_l_1369_, 0);
lean_inc(v_size_1400_);
v___y_1392_ = v_size_1400_;
goto v___jp_1391_;
}
else
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_unsigned_to_nat(0u);
v___y_1392_ = v___x_1401_;
goto v___jp_1391_;
}
v___jp_1380_:
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1384_ = lean_nat_add(v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec(v___y_1382_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_r_1354_);
lean_ctor_set(v___x_1376_, 3, v_r_1370_);
lean_ctor_set(v___x_1376_, 2, v_v_1352_);
lean_ctor_set(v___x_1376_, 1, v_k_1351_);
lean_ctor_set(v___x_1376_, 0, v___x_1384_);
v___x_1386_ = v___x_1376_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_k_1351_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_v_1352_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_r_1370_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_r_1354_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1388_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v___x_1386_);
lean_ctor_set(v___x_1364_, 3, v___y_1381_);
lean_ctor_set(v___x_1364_, 2, v_v_1368_);
lean_ctor_set(v___x_1364_, 1, v_k_1367_);
lean_ctor_set(v___x_1364_, 0, v___x_1379_);
v___x_1388_ = v___x_1364_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_k_1367_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_v_1368_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v___y_1381_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
v___jp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = lean_nat_add(v___x_1378_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec(v___x_1378_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v_l_1369_);
lean_ctor_set(v___x_1343_, 0, v___x_1393_);
v___x_1395_ = v___x_1343_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_l_1340_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_l_1369_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_nat_add(v___x_1348_, v_size_1371_);
if (lean_obj_tag(v_r_1370_) == 0)
{
lean_object* v_size_1397_; 
v_size_1397_ = lean_ctor_get(v_r_1370_, 0);
lean_inc(v_size_1397_);
v___y_1381_ = v___x_1395_;
v___y_1382_ = v___x_1396_;
v___y_1383_ = v_size_1397_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_unsigned_to_nat(0u);
v___y_1381_ = v___x_1395_;
v___y_1382_ = v___x_1396_;
v___y_1383_ = v___x_1398_;
goto v___jp_1380_;
}
}
}
}
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_del_object(v___x_1343_);
v___x_1408_ = lean_nat_add(v___x_1348_, v_size_1349_);
v___x_1409_ = lean_nat_add(v___x_1408_, v_size_1350_);
lean_dec(v_size_1350_);
v___x_1410_ = lean_nat_add(v___x_1408_, v_size_1366_);
lean_dec(v___x_1408_);
lean_inc_ref(v_l_1340_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v_l_1353_);
lean_ctor_set(v___x_1364_, 3, v_l_1340_);
lean_ctor_set(v___x_1364_, 2, v_v_1339_);
lean_ctor_set(v___x_1364_, 1, v_k_1338_);
lean_ctor_set(v___x_1364_, 0, v___x_1410_);
v___x_1412_ = v___x_1364_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_l_1340_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_l_1353_);
v___x_1412_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_isSharedCheck_1419_ = !lean_is_exclusive(v_l_1340_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; lean_object* v_unused_1421_; lean_object* v_unused_1422_; lean_object* v_unused_1423_; lean_object* v_unused_1424_; 
v_unused_1420_ = lean_ctor_get(v_l_1340_, 4);
lean_dec(v_unused_1420_);
v_unused_1421_ = lean_ctor_get(v_l_1340_, 3);
lean_dec(v_unused_1421_);
v_unused_1422_ = lean_ctor_get(v_l_1340_, 2);
lean_dec(v_unused_1422_);
v_unused_1423_ = lean_ctor_get(v_l_1340_, 1);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v_l_1340_, 0);
lean_dec(v_unused_1424_);
v___x_1414_ = v_l_1340_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v_l_1340_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 4, v_r_1354_);
lean_ctor_set(v___x_1414_, 3, v___x_1412_);
lean_ctor_set(v___x_1414_, 2, v_v_1352_);
lean_ctor_set(v___x_1414_, 1, v_k_1351_);
lean_ctor_set(v___x_1414_, 0, v___x_1409_);
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_k_1351_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_v_1352_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v_r_1354_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1432_; 
v_l_1432_ = lean_ctor_get(v_impl_1347_, 3);
lean_inc(v_l_1432_);
if (lean_obj_tag(v_l_1432_) == 0)
{
lean_object* v_r_1433_; lean_object* v_k_1434_; lean_object* v_v_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1458_; 
v_r_1433_ = lean_ctor_get(v_impl_1347_, 4);
v_k_1434_ = lean_ctor_get(v_impl_1347_, 1);
v_v_1435_ = lean_ctor_get(v_impl_1347_, 2);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_impl_1347_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; lean_object* v_unused_1460_; 
v_unused_1459_ = lean_ctor_get(v_impl_1347_, 3);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_impl_1347_, 0);
lean_dec(v_unused_1460_);
v___x_1437_ = v_impl_1347_;
v_isShared_1438_ = v_isSharedCheck_1458_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_r_1433_);
lean_inc(v_v_1435_);
lean_inc(v_k_1434_);
lean_dec(v_impl_1347_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1458_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v_k_1439_; lean_object* v_v_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1454_; 
v_k_1439_ = lean_ctor_get(v_l_1432_, 1);
v_v_1440_ = lean_ctor_get(v_l_1432_, 2);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_l_1432_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; lean_object* v_unused_1456_; lean_object* v_unused_1457_; 
v_unused_1455_ = lean_ctor_get(v_l_1432_, 4);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_l_1432_, 3);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_l_1432_, 0);
lean_dec(v_unused_1457_);
v___x_1442_ = v_l_1432_;
v_isShared_1443_ = v_isSharedCheck_1454_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_v_1440_);
lean_inc(v_k_1439_);
lean_dec(v_l_1432_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1454_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1433_, 2);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 4, v_r_1433_);
lean_ctor_set(v___x_1442_, 3, v_r_1433_);
lean_ctor_set(v___x_1442_, 2, v_v_1339_);
lean_ctor_set(v___x_1442_, 1, v_k_1338_);
lean_ctor_set(v___x_1442_, 0, v___x_1348_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_r_1433_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_r_1433_);
v___x_1446_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1448_; 
lean_inc(v_r_1433_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 3, v_r_1433_);
lean_ctor_set(v___x_1437_, 0, v___x_1348_);
v___x_1448_ = v___x_1437_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_r_1433_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_r_1433_);
v___x_1448_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1450_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v___x_1448_);
lean_ctor_set(v___x_1343_, 3, v___x_1446_);
lean_ctor_set(v___x_1343_, 2, v_v_1440_);
lean_ctor_set(v___x_1343_, 1, v_k_1439_);
lean_ctor_set(v___x_1343_, 0, v___x_1444_);
v___x_1450_ = v___x_1343_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_k_1439_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_v_1440_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
else
{
lean_object* v_r_1461_; 
v_r_1461_ = lean_ctor_get(v_impl_1347_, 4);
lean_inc(v_r_1461_);
if (lean_obj_tag(v_r_1461_) == 0)
{
lean_object* v_k_1462_; lean_object* v_v_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1474_; 
v_k_1462_ = lean_ctor_get(v_impl_1347_, 1);
v_v_1463_ = lean_ctor_get(v_impl_1347_, 2);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_impl_1347_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; 
v_unused_1475_ = lean_ctor_get(v_impl_1347_, 4);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_impl_1347_, 3);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_impl_1347_, 0);
lean_dec(v_unused_1477_);
v___x_1465_ = v_impl_1347_;
v_isShared_1466_ = v_isSharedCheck_1474_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_v_1463_);
lean_inc(v_k_1462_);
lean_dec(v_impl_1347_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1474_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1467_; lean_object* v___x_1469_; 
v___x_1467_ = lean_unsigned_to_nat(3u);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 4, v_l_1432_);
lean_ctor_set(v___x_1465_, 2, v_v_1339_);
lean_ctor_set(v___x_1465_, 1, v_k_1338_);
lean_ctor_set(v___x_1465_, 0, v___x_1348_);
v___x_1469_ = v___x_1465_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1473_, 3, v_l_1432_);
lean_ctor_set(v_reuseFailAlloc_1473_, 4, v_l_1432_);
v___x_1469_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1471_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v_r_1461_);
lean_ctor_set(v___x_1343_, 3, v___x_1469_);
lean_ctor_set(v___x_1343_, 2, v_v_1463_);
lean_ctor_set(v___x_1343_, 1, v_k_1462_);
lean_ctor_set(v___x_1343_, 0, v___x_1467_);
v___x_1471_ = v___x_1343_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_k_1462_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_v_1463_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v_r_1461_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1478_ = lean_unsigned_to_nat(2u);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v_impl_1347_);
lean_ctor_set(v___x_1343_, 3, v_r_1461_);
lean_ctor_set(v___x_1343_, 0, v___x_1478_);
v___x_1480_ = v___x_1343_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_r_1461_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_impl_1347_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
else
{
lean_object* v___x_1483_; 
lean_dec(v_v_1339_);
lean_dec(v_k_1338_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 2, v_v_1335_);
lean_ctor_set(v___x_1343_, 1, v_k_1334_);
v___x_1483_ = v___x_1343_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_size_1337_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1334_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1335_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_l_1340_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_r_1341_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
else
{
lean_object* v_impl_1485_; lean_object* v___x_1486_; 
lean_dec(v_size_1337_);
v_impl_1485_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1334_, v_v_1335_, v_l_1340_);
v___x_1486_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1341_) == 0)
{
lean_object* v_size_1487_; lean_object* v_size_1488_; lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v_l_1491_; lean_object* v_r_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v_size_1487_ = lean_ctor_get(v_r_1341_, 0);
v_size_1488_ = lean_ctor_get(v_impl_1485_, 0);
lean_inc(v_size_1488_);
v_k_1489_ = lean_ctor_get(v_impl_1485_, 1);
lean_inc(v_k_1489_);
v_v_1490_ = lean_ctor_get(v_impl_1485_, 2);
lean_inc(v_v_1490_);
v_l_1491_ = lean_ctor_get(v_impl_1485_, 3);
lean_inc(v_l_1491_);
v_r_1492_ = lean_ctor_get(v_impl_1485_, 4);
lean_inc(v_r_1492_);
v___x_1493_ = lean_unsigned_to_nat(3u);
v___x_1494_ = lean_nat_mul(v___x_1493_, v_size_1487_);
v___x_1495_ = lean_nat_dec_lt(v___x_1494_, v_size_1488_);
lean_dec(v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
lean_dec(v_r_1492_);
lean_dec(v_l_1491_);
lean_dec(v_v_1490_);
lean_dec(v_k_1489_);
v___x_1496_ = lean_nat_add(v___x_1486_, v_size_1488_);
lean_dec(v_size_1488_);
v___x_1497_ = lean_nat_add(v___x_1496_, v_size_1487_);
lean_dec(v___x_1496_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 3, v_impl_1485_);
lean_ctor_set(v___x_1343_, 0, v___x_1497_);
v___x_1499_ = v___x_1343_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_impl_1485_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_r_1341_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
else
{
lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1566_; 
v_isSharedCheck_1566_ = !lean_is_exclusive(v_impl_1485_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; lean_object* v_unused_1568_; lean_object* v_unused_1569_; lean_object* v_unused_1570_; lean_object* v_unused_1571_; 
v_unused_1567_ = lean_ctor_get(v_impl_1485_, 4);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v_impl_1485_, 3);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_impl_1485_, 2);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_impl_1485_, 1);
lean_dec(v_unused_1570_);
v_unused_1571_ = lean_ctor_get(v_impl_1485_, 0);
lean_dec(v_unused_1571_);
v___x_1502_ = v_impl_1485_;
v_isShared_1503_ = v_isSharedCheck_1566_;
goto v_resetjp_1501_;
}
else
{
lean_dec(v_impl_1485_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1566_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_size_1504_; lean_object* v_size_1505_; lean_object* v_k_1506_; lean_object* v_v_1507_; lean_object* v_l_1508_; lean_object* v_r_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v_size_1504_ = lean_ctor_get(v_l_1491_, 0);
v_size_1505_ = lean_ctor_get(v_r_1492_, 0);
v_k_1506_ = lean_ctor_get(v_r_1492_, 1);
v_v_1507_ = lean_ctor_get(v_r_1492_, 2);
v_l_1508_ = lean_ctor_get(v_r_1492_, 3);
v_r_1509_ = lean_ctor_get(v_r_1492_, 4);
v___x_1510_ = lean_unsigned_to_nat(2u);
v___x_1511_ = lean_nat_mul(v___x_1510_, v_size_1504_);
v___x_1512_ = lean_nat_dec_lt(v_size_1505_, v___x_1511_);
lean_dec(v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1541_; 
lean_inc(v_r_1509_);
lean_inc(v_l_1508_);
lean_inc(v_v_1507_);
lean_inc(v_k_1506_);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_r_1492_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; lean_object* v_unused_1543_; lean_object* v_unused_1544_; lean_object* v_unused_1545_; lean_object* v_unused_1546_; 
v_unused_1542_ = lean_ctor_get(v_r_1492_, 4);
lean_dec(v_unused_1542_);
v_unused_1543_ = lean_ctor_get(v_r_1492_, 3);
lean_dec(v_unused_1543_);
v_unused_1544_ = lean_ctor_get(v_r_1492_, 2);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v_r_1492_, 1);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_r_1492_, 0);
lean_dec(v_unused_1546_);
v___x_1514_ = v_r_1492_;
v_isShared_1515_ = v_isSharedCheck_1541_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v_r_1492_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1541_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___x_1529_; lean_object* v___y_1531_; 
v___x_1516_ = lean_nat_add(v___x_1486_, v_size_1488_);
lean_dec(v_size_1488_);
v___x_1517_ = lean_nat_add(v___x_1516_, v_size_1487_);
lean_dec(v___x_1516_);
v___x_1529_ = lean_nat_add(v___x_1486_, v_size_1504_);
if (lean_obj_tag(v_l_1508_) == 0)
{
lean_object* v_size_1539_; 
v_size_1539_ = lean_ctor_get(v_l_1508_, 0);
lean_inc(v_size_1539_);
v___y_1531_ = v_size_1539_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_unsigned_to_nat(0u);
v___y_1531_ = v___x_1540_;
goto v___jp_1530_;
}
v___jp_1518_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1522_ = lean_nat_add(v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec(v___y_1520_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 4, v_r_1341_);
lean_ctor_set(v___x_1514_, 3, v_r_1509_);
lean_ctor_set(v___x_1514_, 2, v_v_1339_);
lean_ctor_set(v___x_1514_, 1, v_k_1338_);
lean_ctor_set(v___x_1514_, 0, v___x_1522_);
v___x_1524_ = v___x_1514_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_r_1509_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_r_1341_);
v___x_1524_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1526_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 4, v___x_1524_);
lean_ctor_set(v___x_1502_, 3, v___y_1519_);
lean_ctor_set(v___x_1502_, 2, v_v_1507_);
lean_ctor_set(v___x_1502_, 1, v_k_1506_);
lean_ctor_set(v___x_1502_, 0, v___x_1517_);
v___x_1526_ = v___x_1502_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_k_1506_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_v_1507_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v___y_1519_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
v___jp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1532_ = lean_nat_add(v___x_1529_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec(v___x_1529_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v_l_1508_);
lean_ctor_set(v___x_1343_, 3, v_l_1491_);
lean_ctor_set(v___x_1343_, 2, v_v_1490_);
lean_ctor_set(v___x_1343_, 1, v_k_1489_);
lean_ctor_set(v___x_1343_, 0, v___x_1532_);
v___x_1534_ = v___x_1343_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_l_1491_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_l_1508_);
v___x_1534_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_nat_add(v___x_1486_, v_size_1487_);
if (lean_obj_tag(v_r_1509_) == 0)
{
lean_object* v_size_1536_; 
v_size_1536_ = lean_ctor_get(v_r_1509_, 0);
lean_inc(v_size_1536_);
v___y_1519_ = v___x_1534_;
v___y_1520_ = v___x_1535_;
v___y_1521_ = v_size_1536_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_unsigned_to_nat(0u);
v___y_1519_ = v___x_1534_;
v___y_1520_ = v___x_1535_;
v___y_1521_ = v___x_1537_;
goto v___jp_1518_;
}
}
}
}
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_del_object(v___x_1343_);
v___x_1547_ = lean_nat_add(v___x_1486_, v_size_1488_);
lean_dec(v_size_1488_);
v___x_1548_ = lean_nat_add(v___x_1547_, v_size_1487_);
lean_dec(v___x_1547_);
v___x_1549_ = lean_nat_add(v___x_1486_, v_size_1487_);
v___x_1550_ = lean_nat_add(v___x_1549_, v_size_1505_);
lean_dec(v___x_1549_);
lean_inc_ref(v_r_1341_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 4, v_r_1341_);
lean_ctor_set(v___x_1502_, 3, v_r_1492_);
lean_ctor_set(v___x_1502_, 2, v_v_1339_);
lean_ctor_set(v___x_1502_, 1, v_k_1338_);
lean_ctor_set(v___x_1502_, 0, v___x_1550_);
v___x_1552_ = v___x_1502_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_r_1492_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_r_1341_);
v___x_1552_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_isSharedCheck_1559_ = !lean_is_exclusive(v_r_1341_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; lean_object* v_unused_1561_; lean_object* v_unused_1562_; lean_object* v_unused_1563_; lean_object* v_unused_1564_; 
v_unused_1560_ = lean_ctor_get(v_r_1341_, 4);
lean_dec(v_unused_1560_);
v_unused_1561_ = lean_ctor_get(v_r_1341_, 3);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_r_1341_, 2);
lean_dec(v_unused_1562_);
v_unused_1563_ = lean_ctor_get(v_r_1341_, 1);
lean_dec(v_unused_1563_);
v_unused_1564_ = lean_ctor_get(v_r_1341_, 0);
lean_dec(v_unused_1564_);
v___x_1554_ = v_r_1341_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_dec(v_r_1341_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 4, v___x_1552_);
lean_ctor_set(v___x_1554_, 3, v_l_1491_);
lean_ctor_set(v___x_1554_, 2, v_v_1490_);
lean_ctor_set(v___x_1554_, 1, v_k_1489_);
lean_ctor_set(v___x_1554_, 0, v___x_1548_);
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_l_1491_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v___x_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1572_; 
v_l_1572_ = lean_ctor_get(v_impl_1485_, 3);
lean_inc(v_l_1572_);
if (lean_obj_tag(v_l_1572_) == 0)
{
lean_object* v_r_1573_; lean_object* v_k_1574_; lean_object* v_v_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1586_; 
v_r_1573_ = lean_ctor_get(v_impl_1485_, 4);
v_k_1574_ = lean_ctor_get(v_impl_1485_, 1);
v_v_1575_ = lean_ctor_get(v_impl_1485_, 2);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_impl_1485_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; lean_object* v_unused_1588_; 
v_unused_1587_ = lean_ctor_get(v_impl_1485_, 3);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_impl_1485_, 0);
lean_dec(v_unused_1588_);
v___x_1577_ = v_impl_1485_;
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_r_1573_);
lean_inc(v_v_1575_);
lean_inc(v_k_1574_);
lean_dec(v_impl_1485_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1586_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1573_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 3, v_r_1573_);
lean_ctor_set(v___x_1577_, 2, v_v_1339_);
lean_ctor_set(v___x_1577_, 1, v_k_1338_);
lean_ctor_set(v___x_1577_, 0, v___x_1486_);
v___x_1581_ = v___x_1577_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_r_1573_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_r_1573_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v___x_1581_);
lean_ctor_set(v___x_1343_, 3, v_l_1572_);
lean_ctor_set(v___x_1343_, 2, v_v_1575_);
lean_ctor_set(v___x_1343_, 1, v_k_1574_);
lean_ctor_set(v___x_1343_, 0, v___x_1579_);
v___x_1583_ = v___x_1343_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_k_1574_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_v_1575_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v_l_1572_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_r_1589_; 
v_r_1589_ = lean_ctor_get(v_impl_1485_, 4);
lean_inc(v_r_1589_);
if (lean_obj_tag(v_r_1589_) == 0)
{
lean_object* v_k_1590_; lean_object* v_v_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1614_; 
v_k_1590_ = lean_ctor_get(v_impl_1485_, 1);
v_v_1591_ = lean_ctor_get(v_impl_1485_, 2);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_impl_1485_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; lean_object* v_unused_1616_; lean_object* v_unused_1617_; 
v_unused_1615_ = lean_ctor_get(v_impl_1485_, 4);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_impl_1485_, 3);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_impl_1485_, 0);
lean_dec(v_unused_1617_);
v___x_1593_ = v_impl_1485_;
v_isShared_1594_ = v_isSharedCheck_1614_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_v_1591_);
lean_inc(v_k_1590_);
lean_dec(v_impl_1485_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1614_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v_k_1595_; lean_object* v_v_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1610_; 
v_k_1595_ = lean_ctor_get(v_r_1589_, 1);
v_v_1596_ = lean_ctor_get(v_r_1589_, 2);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_r_1589_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; lean_object* v_unused_1612_; lean_object* v_unused_1613_; 
v_unused_1611_ = lean_ctor_get(v_r_1589_, 4);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_r_1589_, 3);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_r_1589_, 0);
lean_dec(v_unused_1613_);
v___x_1598_ = v_r_1589_;
v_isShared_1599_ = v_isSharedCheck_1610_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_v_1596_);
lean_inc(v_k_1595_);
lean_dec(v_r_1589_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1610_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1600_ = lean_unsigned_to_nat(3u);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 4, v_l_1572_);
lean_ctor_set(v___x_1598_, 3, v_l_1572_);
lean_ctor_set(v___x_1598_, 2, v_v_1591_);
lean_ctor_set(v___x_1598_, 1, v_k_1590_);
lean_ctor_set(v___x_1598_, 0, v___x_1486_);
v___x_1602_ = v___x_1598_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_k_1590_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_v_1591_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_l_1572_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v_l_1572_);
v___x_1602_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1604_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 4, v_l_1572_);
lean_ctor_set(v___x_1593_, 2, v_v_1339_);
lean_ctor_set(v___x_1593_, 1, v_k_1338_);
lean_ctor_set(v___x_1593_, 0, v___x_1486_);
v___x_1604_ = v___x_1593_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v_l_1572_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v_l_1572_);
v___x_1604_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1606_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v___x_1604_);
lean_ctor_set(v___x_1343_, 3, v___x_1602_);
lean_ctor_set(v___x_1343_, 2, v_v_1596_);
lean_ctor_set(v___x_1343_, 1, v_k_1595_);
lean_ctor_set(v___x_1343_, 0, v___x_1600_);
v___x_1606_ = v___x_1343_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_k_1595_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_v_1596_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1618_ = lean_unsigned_to_nat(2u);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v_r_1589_);
lean_ctor_set(v___x_1343_, 3, v_impl_1485_);
lean_ctor_set(v___x_1343_, 0, v___x_1618_);
v___x_1620_ = v___x_1343_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_k_1338_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_v_1339_);
lean_ctor_set(v_reuseFailAlloc_1621_, 3, v_impl_1485_);
lean_ctor_set(v_reuseFailAlloc_1621_, 4, v_r_1589_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_unsigned_to_nat(1u);
v___x_1624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v_k_1334_);
lean_ctor_set(v___x_1624_, 2, v_v_1335_);
lean_ctor_set(v___x_1624_, 3, v_t_1336_);
lean_ctor_set(v___x_1624_, 4, v_t_1336_);
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(lean_object* v_k_1625_, lean_object* v_x_1626_){
_start:
{
if (lean_obj_tag(v_x_1626_) == 0)
{
lean_object* v___x_1627_; 
lean_dec_ref(v_k_1625_);
v___x_1627_ = lean_box(0);
return v___x_1627_;
}
else
{
lean_object* v_val_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v_val_1628_ = lean_ctor_get(v_x_1626_, 0);
lean_inc(v_val_1628_);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v_k_1625_);
lean_ctor_set(v___x_1629_, 1, v_val_1628_);
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4___boxed(lean_object* v_k_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v_k_1632_, v_x_1633_);
lean_dec(v_x_1633_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(size_t v_sz_1635_, size_t v_i_1636_, lean_object* v_bs_1637_){
_start:
{
uint8_t v___x_1638_; 
v___x_1638_ = lean_usize_dec_lt(v_i_1636_, v_sz_1635_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v_bs_1637_);
return v___x_1639_;
}
else
{
lean_object* v_v_1640_; lean_object* v___x_1641_; 
v_v_1640_ = lean_array_uget_borrowed(v_bs_1637_, v_i_1636_);
lean_inc(v_v_1640_);
v___x_1641_ = l_Lean_Lsp_instFromJsonCallHierarchyIncomingCall_fromJson(v_v_1640_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref(v_bs_1637_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1651_; lean_object* v_bs_x27_1652_; size_t v___x_1653_; size_t v___x_1654_; lean_object* v___x_1655_; 
v_a_1650_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1641_);
v___x_1651_ = lean_unsigned_to_nat(0u);
v_bs_x27_1652_ = lean_array_uset(v_bs_1637_, v_i_1636_, v___x_1651_);
v___x_1653_ = ((size_t)1ULL);
v___x_1654_ = lean_usize_add(v_i_1636_, v___x_1653_);
v___x_1655_ = lean_array_uset(v_bs_x27_1652_, v_i_1636_, v_a_1650_);
v_i_1636_ = v___x_1654_;
v_bs_1637_ = v___x_1655_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_sz_1657_, lean_object* v_i_1658_, lean_object* v_bs_1659_){
_start:
{
size_t v_sz_boxed_1660_; size_t v_i_boxed_1661_; lean_object* v_res_1662_; 
v_sz_boxed_1660_ = lean_unbox_usize(v_sz_1657_);
lean_dec(v_sz_1657_);
v_i_boxed_1661_ = lean_unbox_usize(v_i_1658_);
lean_dec(v_i_1658_);
v_res_1662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_boxed_1660_, v_i_boxed_1661_, v_bs_1659_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(lean_object* v_x_1663_){
_start:
{
if (lean_obj_tag(v_x_1663_) == 4)
{
lean_object* v_elems_1664_; size_t v_sz_1665_; size_t v___x_1666_; lean_object* v___x_1667_; 
v_elems_1664_ = lean_ctor_get(v_x_1663_, 0);
lean_inc_ref(v_elems_1664_);
lean_dec_ref(v_x_1663_);
v_sz_1665_ = lean_array_size(v_elems_1664_);
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_1665_, v___x_1666_, v_elems_1664_);
return v___x_1667_;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1668_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1669_ = lean_unsigned_to_nat(80u);
v___x_1670_ = l_Lean_Json_pretty(v_x_1663_, v___x_1669_);
v___x_1671_ = lean_string_append(v___x_1668_, v___x_1670_);
lean_dec_ref(v___x_1670_);
v___x_1672_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1673_ = lean_string_append(v___x_1671_, v___x_1672_);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(lean_object* v_x_1677_){
_start:
{
if (lean_obj_tag(v_x_1677_) == 0)
{
lean_object* v___x_1678_; 
v___x_1678_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0));
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(v_x_1677_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
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
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1696_; 
v_a_1688_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1690_ = v___x_1679_;
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1679_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_a_1688_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1692_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(lean_object* v_expectedID_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Lsp_Ipc_stdout(v_a_1698_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1844_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1844_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1844_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_IO_FS_Stream_readLspMessage(v_a_1701_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1835_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1835_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1835_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___y_1711_; lean_object* v___y_1712_; 
switch(lean_obj_tag(v_a_1706_))
{
case 2:
{
lean_object* v_id_1718_; lean_object* v_result_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1763_; 
v_id_1718_ = lean_ctor_get(v_a_1706_, 0);
v_result_1719_ = lean_ctor_get(v_a_1706_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_a_1706_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1721_ = v_a_1706_;
v_isShared_1722_ = v_isSharedCheck_1763_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_result_1719_);
lean_inc(v_id_1718_);
lean_dec(v_a_1706_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1763_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
uint8_t v___x_1723_; 
v___x_1723_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_1718_, v_expectedID_1697_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___y_1726_; 
lean_del_object(v___x_1721_);
lean_dec(v_result_1719_);
lean_del_object(v___x_1703_);
v___x_1724_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_1697_))
{
case 0:
{
lean_object* v_s_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_s_1737_ = lean_ctor_get(v_expectedID_1697_, 0);
lean_inc_ref(v_s_1737_);
lean_dec_ref(v_expectedID_1697_);
v___x_1738_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1739_ = lean_string_append(v___x_1738_, v_s_1737_);
lean_dec_ref(v_s_1737_);
v___x_1740_ = lean_string_append(v___x_1739_, v___x_1738_);
v___y_1726_ = v___x_1740_;
goto v___jp_1725_;
}
case 1:
{
lean_object* v_n_1741_; lean_object* v___x_1742_; 
v_n_1741_ = lean_ctor_get(v_expectedID_1697_, 0);
lean_inc_ref(v_n_1741_);
lean_dec_ref(v_expectedID_1697_);
v___x_1742_ = l_Lean_JsonNumber_toString(v_n_1741_);
v___y_1726_ = v___x_1742_;
goto v___jp_1725_;
}
default: 
{
lean_object* v___x_1743_; 
v___x_1743_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1726_ = v___x_1743_;
goto v___jp_1725_;
}
}
v___jp_1725_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_string_append(v___x_1724_, v___y_1726_);
lean_dec_ref(v___y_1726_);
v___x_1728_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_1729_ = lean_string_append(v___x_1727_, v___x_1728_);
switch(lean_obj_tag(v_id_1718_))
{
case 0:
{
lean_object* v_s_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_s_1730_ = lean_ctor_get(v_id_1718_, 0);
lean_inc_ref(v_s_1730_);
lean_dec_ref(v_id_1718_);
v___x_1731_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1732_ = lean_string_append(v___x_1731_, v_s_1730_);
lean_dec_ref(v_s_1730_);
v___x_1733_ = lean_string_append(v___x_1732_, v___x_1731_);
v___y_1711_ = v___x_1729_;
v___y_1712_ = v___x_1733_;
goto v___jp_1710_;
}
case 1:
{
lean_object* v_n_1734_; lean_object* v___x_1735_; 
v_n_1734_ = lean_ctor_get(v_id_1718_, 0);
lean_inc_ref(v_n_1734_);
lean_dec_ref(v_id_1718_);
v___x_1735_ = l_Lean_JsonNumber_toString(v_n_1734_);
v___y_1711_ = v___x_1729_;
v___y_1712_ = v___x_1735_;
goto v___jp_1710_;
}
default: 
{
lean_object* v___x_1736_; 
v___x_1736_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1711_ = v___x_1729_;
v___y_1712_ = v___x_1736_;
goto v___jp_1710_;
}
}
}
}
else
{
lean_object* v___x_1744_; 
lean_dec(v_id_1718_);
lean_del_object(v___x_1708_);
lean_inc(v_result_1719_);
v___x_1744_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(v_result_1719_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
lean_del_object(v___x_1721_);
lean_dec(v_expectedID_1697_);
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref(v___x_1744_);
v___x_1746_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_1747_ = l_Lean_Json_compress(v_result_1719_);
v___x_1748_ = lean_string_append(v___x_1746_, v___x_1747_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_1750_ = lean_string_append(v___x_1748_, v___x_1749_);
v___x_1751_ = lean_string_append(v___x_1750_, v_a_1745_);
lean_dec(v_a_1745_);
v___x_1752_ = lean_mk_io_user_error(v___x_1751_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 1);
lean_ctor_set(v___x_1703_, 0, v___x_1752_);
v___x_1754_ = v___x_1703_;
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
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; 
lean_dec(v_result_1719_);
v_a_1756_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1744_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set_tag(v___x_1721_, 0);
lean_ctor_set(v___x_1721_, 1, v_a_1756_);
lean_ctor_set(v___x_1721_, 0, v_expectedID_1697_);
v___x_1758_ = v___x_1721_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_expectedID_1697_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_a_1756_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1760_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1758_);
v___x_1760_ = v___x_1703_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_1764_; uint8_t v_code_1765_; lean_object* v_message_1766_; lean_object* v_data_x3f_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___x_1799_; lean_object* v___y_1801_; 
lean_del_object(v___x_1708_);
lean_dec(v_expectedID_1697_);
v_id_1764_ = lean_ctor_get(v_a_1706_, 0);
lean_inc(v_id_1764_);
v_code_1765_ = lean_ctor_get_uint8(v_a_1706_, sizeof(void*)*3);
v_message_1766_ = lean_ctor_get(v_a_1706_, 1);
lean_inc_ref(v_message_1766_);
v_data_x3f_1767_ = lean_ctor_get(v_a_1706_, 2);
lean_inc(v_data_x3f_1767_);
lean_dec_ref(v_a_1706_);
v___x_1768_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_1769_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_1799_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_1764_))
{
case 0:
{
lean_object* v_s_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_s_1817_ = lean_ctor_get(v_id_1764_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_id_1764_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v_id_1764_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_s_1817_);
lean_dec(v_id_1764_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set_tag(v___x_1819_, 3);
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_s_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
v___y_1801_ = v___x_1822_;
goto v___jp_1800_;
}
}
}
case 1:
{
lean_object* v_n_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_n_1825_ = lean_ctor_get(v_id_1764_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_id_1764_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v_id_1764_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_n_1825_);
lean_dec(v_id_1764_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 2);
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_n_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
v___y_1801_ = v___x_1830_;
goto v___jp_1800_;
}
}
}
default: 
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_box(0);
v___y_1801_ = v___x_1833_;
goto v___jp_1800_;
}
}
v___jp_1770_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
lean_inc(v___y_1774_);
lean_inc_ref(v___y_1772_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___y_1772_);
lean_ctor_set(v___x_1775_, 1, v___y_1774_);
v___x_1776_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_1777_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_message_1766_);
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = lean_box(0);
v___x_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1775_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_1783_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_1782_, v_data_x3f_1767_);
lean_dec(v_data_x3f_1767_);
v___x_1784_ = l_List_appendTR___redArg(v___x_1781_, v___x_1783_);
v___x_1785_ = l_Lean_Json_mkObj(v___x_1784_);
lean_dec(v___x_1784_);
lean_inc_ref(v___y_1771_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___y_1771_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
lean_ctor_set(v___x_1787_, 1, v___x_1779_);
v___x_1788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___y_1773_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1769_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = l_Lean_Json_mkObj(v___x_1789_);
lean_dec_ref(v___x_1789_);
v___x_1791_ = l_Lean_Json_compress(v___x_1790_);
v___x_1792_ = lean_string_append(v___x_1768_, v___x_1791_);
lean_dec_ref(v___x_1791_);
v___x_1793_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1794_ = lean_string_append(v___x_1792_, v___x_1793_);
v___x_1795_ = lean_mk_io_user_error(v___x_1794_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 1);
lean_ctor_set(v___x_1703_, 0, v___x_1795_);
v___x_1797_ = v___x_1703_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
v___jp_1800_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1799_);
lean_ctor_set(v___x_1802_, 1, v___y_1801_);
v___x_1803_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_1804_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_1765_)
{
case 0:
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1805_;
goto v___jp_1770_;
}
case 1:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1806_;
goto v___jp_1770_;
}
case 2:
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1807_;
goto v___jp_1770_;
}
case 3:
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1808_;
goto v___jp_1770_;
}
case 4:
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1809_;
goto v___jp_1770_;
}
case 5:
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1810_;
goto v___jp_1770_;
}
case 6:
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1811_;
goto v___jp_1770_;
}
case 7:
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1812_;
goto v___jp_1770_;
}
case 8:
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1813_;
goto v___jp_1770_;
}
case 9:
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1814_;
goto v___jp_1770_;
}
case 10:
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1815_;
goto v___jp_1770_;
}
default: 
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_1771_ = v___x_1803_;
v___y_1772_ = v___x_1804_;
v___y_1773_ = v___x_1802_;
v___y_1774_ = v___x_1816_;
goto v___jp_1770_;
}
}
}
}
default: 
{
lean_del_object(v___x_1708_);
lean_dec(v_a_1706_);
lean_del_object(v___x_1703_);
goto _start;
}
}
v___jp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1713_ = lean_string_append(v___y_1711_, v___y_1712_);
lean_dec_ref(v___y_1712_);
v___x_1714_ = lean_mk_io_user_error(v___x_1713_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set_tag(v___x_1708_, 1);
lean_ctor_set(v___x_1708_, 0, v___x_1714_);
v___x_1716_ = v___x_1708_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_del_object(v___x_1703_);
lean_dec(v_expectedID_1697_);
v_a_1836_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1705_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1705_);
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
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v_expectedID_1697_);
v_a_1845_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1700_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1700_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2___boxed(lean_object* v_expectedID_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v_expectedID_1853_, v_a_1854_);
lean_dec_ref(v_a_1854_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(lean_object* v_v_1857_){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = l_Lean_Lsp_instToJsonCallHierarchyIncomingCallsParams_toJson(v_v_1857_);
v___x_1859_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(lean_object* v_h_1860_, lean_object* v_r_1861_){
_start:
{
lean_object* v_id_1863_; lean_object* v_method_1864_; lean_object* v_param_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1885_; 
v_id_1863_ = lean_ctor_get(v_r_1861_, 0);
v_method_1864_ = lean_ctor_get(v_r_1861_, 1);
v_param_1865_ = lean_ctor_get(v_r_1861_, 2);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_r_1861_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1867_ = v_r_1861_;
v_isShared_1868_ = v_isSharedCheck_1885_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_param_1865_);
lean_inc(v_method_1864_);
lean_inc(v_id_1863_);
lean_dec(v_r_1861_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1885_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___y_1870_; lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(v_param_1865_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1876_; 
lean_dec_ref(v___x_1875_);
v___x_1876_ = lean_box(0);
v___y_1870_ = v___x_1876_;
goto v___jp_1869_;
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1877_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1875_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
v___y_1870_ = v___x_1882_;
goto v___jp_1869_;
}
}
}
v___jp_1869_:
{
lean_object* v___x_1872_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 2, v___y_1870_);
v___x_1872_ = v___x_1867_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_id_1863_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_method_1864_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v___y_1870_);
v___x_1872_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_IO_FS_Stream_writeLspMessage(v_h_1860_, v___x_1872_);
return v___x_1873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1___boxed(lean_object* v_h_1886_, lean_object* v_r_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_h_1886_, v_r_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(lean_object* v_r_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v___x_1893_; lean_object* v_a_1894_; lean_object* v___x_1895_; 
v___x_1893_ = l_Lean_Lsp_Ipc_stdin(v_a_1891_);
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref(v___x_1893_);
v___x_1895_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_a_1894_, v_r_1890_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1___boxed(lean_object* v_r_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v_r_1896_, v_a_1897_);
lean_dec_ref(v_a_1897_);
return v_res_1899_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(lean_object* v_k_1900_, lean_object* v_t_1901_){
_start:
{
if (lean_obj_tag(v_t_1901_) == 0)
{
lean_object* v_k_1902_; lean_object* v_l_1903_; lean_object* v_r_1904_; uint8_t v___x_1905_; 
v_k_1902_ = lean_ctor_get(v_t_1901_, 1);
v_l_1903_ = lean_ctor_get(v_t_1901_, 3);
v_r_1904_ = lean_ctor_get(v_t_1901_, 4);
v___x_1905_ = lean_string_dec_lt(v_k_1900_, v_k_1902_);
if (v___x_1905_ == 0)
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_string_dec_eq(v_k_1900_, v_k_1902_);
if (v___x_1906_ == 0)
{
v_t_1901_ = v_r_1904_;
goto _start;
}
else
{
return v___x_1906_;
}
}
else
{
v_t_1901_ = v_l_1903_;
goto _start;
}
}
else
{
uint8_t v___x_1909_; 
v___x_1909_ = 0;
return v___x_1909_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg___boxed(lean_object* v_k_1910_, lean_object* v_t_1911_){
_start:
{
uint8_t v_res_1912_; lean_object* v_r_1913_; 
v_res_1912_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_1910_, v_t_1911_);
lean_dec(v_t_1911_);
lean_dec_ref(v_k_1910_);
v_r_1913_ = lean_box(v_res_1912_);
return v_r_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(lean_object* v_requestNo_1921_, lean_object* v_item_1922_, lean_object* v_fromRanges_1923_, lean_object* v_visited_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_name_1927_; uint8_t v___x_1928_; 
v_name_1927_ = lean_ctor_get(v_item_1922_, 0);
v___x_1928_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_1927_, v_visited_1924_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_inc(v_requestNo_1921_);
v___x_1929_ = l_Lean_JsonNumber_fromNat(v_requestNo_1921_);
v___x_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
v___x_1931_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_1922_);
lean_inc_ref(v___x_1930_);
v___x_1932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
lean_ctor_set(v___x_1932_, 2, v_item_1922_);
v___x_1933_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v___x_1932_, v_a_1925_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v___x_1934_; 
lean_dec_ref(v___x_1933_);
v___x_1934_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v___x_1930_, v_a_1925_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1972_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v___x_1934_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_box(0);
lean_inc_ref(v_name_1927_);
v___x_1979_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_1927_, v___x_1978_, v_visited_1924_);
v___y_1972_ = v___x_1979_;
goto v___jp_1971_;
}
else
{
v___y_1972_ = v_visited_1924_;
goto v___jp_1971_;
}
v___jp_1936_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; size_t v_sz_1942_; size_t v___x_1943_; lean_object* v___x_1944_; 
v___x_1940_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___y_1937_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v_sz_1942_ = lean_array_size(v___y_1939_);
v___x_1943_ = ((size_t)0ULL);
v___x_1944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___y_1938_, v___y_1939_, v_sz_1942_, v___x_1943_, v___x_1941_, v_a_1925_);
lean_dec_ref(v___y_1939_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1962_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1962_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1962_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v_fst_1949_; lean_object* v_snd_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1961_; 
v_fst_1949_ = lean_ctor_get(v_a_1945_, 0);
v_snd_1950_ = lean_ctor_get(v_a_1945_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_a_1945_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1952_ = v_a_1945_;
v_isShared_1953_ = v_isSharedCheck_1961_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_snd_1950_);
lean_inc(v_fst_1949_);
lean_dec(v_a_1945_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1961_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1954_, 0, v_item_1922_);
lean_ctor_set(v___x_1954_, 1, v_fromRanges_1923_);
lean_ctor_set(v___x_1954_, 2, v_snd_1950_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v_fst_1949_);
lean_ctor_set(v___x_1952_, 0, v___x_1954_);
v___x_1956_ = v___x_1952_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_fst_1949_);
v___x_1956_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1958_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1956_);
v___x_1958_ = v___x_1947_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref(v_fromRanges_1923_);
lean_dec_ref(v_item_1922_);
v_a_1963_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1944_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1944_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
v___jp_1971_:
{
lean_object* v_result_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_result_1973_ = lean_ctor_get(v_a_1935_, 1);
lean_inc(v_result_1973_);
lean_dec(v_a_1935_);
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = lean_nat_add(v_requestNo_1921_, v___x_1974_);
lean_dec(v_requestNo_1921_);
if (lean_obj_tag(v_result_1973_) == 0)
{
lean_object* v___x_1976_; 
v___x_1976_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2));
v___y_1937_ = v___x_1975_;
v___y_1938_ = v___y_1972_;
v___y_1939_ = v___x_1976_;
goto v___jp_1936_;
}
else
{
lean_object* v_val_1977_; 
v_val_1977_ = lean_ctor_get(v_result_1973_, 0);
lean_inc(v_val_1977_);
lean_dec_ref(v_result_1973_);
v___y_1937_ = v___x_1975_;
v___y_1938_ = v___y_1972_;
v___y_1939_ = v_val_1977_;
goto v___jp_1936_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_visited_1924_);
lean_dec_ref(v_fromRanges_1923_);
lean_dec_ref(v_item_1922_);
lean_dec(v_requestNo_1921_);
v_a_1980_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1934_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1934_);
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
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v___x_1930_);
lean_dec(v_visited_1924_);
lean_dec_ref(v_fromRanges_1923_);
lean_dec_ref(v_item_1922_);
lean_dec(v_requestNo_1921_);
v_a_1988_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1933_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1933_);
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
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_dec(v_visited_1924_);
lean_dec_ref(v_fromRanges_1923_);
v___x_1996_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_1997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1997_, 0, v_item_1922_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
lean_ctor_set(v___x_1997_, 2, v___x_1996_);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
lean_ctor_set(v___x_1998_, 1, v_requestNo_1921_);
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(lean_object* v___x_2000_, lean_object* v_as_2001_, size_t v_sz_2002_, size_t v_i_2003_, lean_object* v_b_2004_, lean_object* v___y_2005_){
_start:
{
uint8_t v___x_2007_; 
v___x_2007_ = lean_usize_dec_lt(v_i_2003_, v_sz_2002_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
lean_dec(v___x_2000_);
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v_b_2004_);
return v___x_2008_;
}
else
{
lean_object* v_fst_2009_; lean_object* v_snd_2010_; lean_object* v_a_2011_; lean_object* v_from_2012_; lean_object* v_fromRanges_2013_; lean_object* v___x_2014_; 
v_fst_2009_ = lean_ctor_get(v_b_2004_, 0);
lean_inc(v_fst_2009_);
v_snd_2010_ = lean_ctor_get(v_b_2004_, 1);
lean_inc(v_snd_2010_);
lean_dec_ref(v_b_2004_);
v_a_2011_ = lean_array_uget_borrowed(v_as_2001_, v_i_2003_);
v_from_2012_ = lean_ctor_get(v_a_2011_, 0);
v_fromRanges_2013_ = lean_ctor_get(v_a_2011_, 1);
lean_inc(v___x_2000_);
lean_inc_ref(v_fromRanges_2013_);
lean_inc_ref(v_from_2012_);
v___x_2014_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2009_, v_from_2012_, v_fromRanges_2013_, v___x_2000_, v___y_2005_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v_fst_2016_; lean_object* v_snd_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2028_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
v_fst_2016_ = lean_ctor_get(v_a_2015_, 0);
v_snd_2017_ = lean_ctor_get(v_a_2015_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2019_ = v_a_2015_;
v_isShared_2020_ = v_isSharedCheck_2028_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_snd_2017_);
lean_inc(v_fst_2016_);
lean_dec(v_a_2015_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2028_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_array_push(v_snd_2010_, v_fst_2016_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 1, v___x_2021_);
lean_ctor_set(v___x_2019_, 0, v_snd_2017_);
v___x_2023_ = v___x_2019_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_snd_2017_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
size_t v___x_2024_; size_t v___x_2025_; 
v___x_2024_ = ((size_t)1ULL);
v___x_2025_ = lean_usize_add(v_i_2003_, v___x_2024_);
v_i_2003_ = v___x_2025_;
v_b_2004_ = v___x_2023_;
goto _start;
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_snd_2010_);
lean_dec(v___x_2000_);
v_a_2029_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2014_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2014_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3___boxed(lean_object* v___x_2037_, lean_object* v_as_2038_, lean_object* v_sz_2039_, lean_object* v_i_2040_, lean_object* v_b_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
size_t v_sz_boxed_2044_; size_t v_i_boxed_2045_; lean_object* v_res_2046_; 
v_sz_boxed_2044_ = lean_unbox_usize(v_sz_2039_);
lean_dec(v_sz_2039_);
v_i_boxed_2045_ = lean_unbox_usize(v_i_2040_);
lean_dec(v_i_2040_);
v_res_2046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___x_2037_, v_as_2038_, v_sz_boxed_2044_, v_i_boxed_2045_, v_b_2041_, v___y_2042_);
lean_dec_ref(v___y_2042_);
lean_dec_ref(v_as_2038_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___boxed(lean_object* v_requestNo_2047_, lean_object* v_item_2048_, lean_object* v_fromRanges_2049_, lean_object* v_visited_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_requestNo_2047_, v_item_2048_, v_fromRanges_2049_, v_visited_2050_, v_a_2051_);
lean_dec_ref(v_a_2051_);
return v_res_2053_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(lean_object* v_00_u03b2_2054_, lean_object* v_k_2055_, lean_object* v_t_2056_){
_start:
{
uint8_t v___x_2057_; 
v___x_2057_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_2055_, v_t_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___boxed(lean_object* v_00_u03b2_2058_, lean_object* v_k_2059_, lean_object* v_t_2060_){
_start:
{
uint8_t v_res_2061_; lean_object* v_r_2062_; 
v_res_2061_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(v_00_u03b2_2058_, v_k_2059_, v_t_2060_);
lean_dec(v_t_2060_);
lean_dec_ref(v_k_2059_);
v_r_2062_ = lean_box(v_res_2061_);
return v_r_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4(lean_object* v_00_u03b2_2063_, lean_object* v_k_2064_, lean_object* v_v_2065_, lean_object* v_t_2066_, lean_object* v_hl_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_2064_, v_v_2065_, v_t_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2069_, size_t v_i_2070_, lean_object* v_bs_2071_){
_start:
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_usize_dec_lt(v_i_2070_, v_sz_2069_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2073_, 0, v_bs_2071_);
return v___x_2073_;
}
else
{
lean_object* v_v_2074_; lean_object* v___x_2075_; 
v_v_2074_ = lean_array_uget_borrowed(v_bs_2071_, v_i_2070_);
lean_inc(v_v_2074_);
v___x_2075_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v_v_2074_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec_ref(v_bs_2071_);
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2085_; lean_object* v_bs_x27_2086_; size_t v___x_2087_; size_t v___x_2088_; lean_object* v___x_2089_; 
v_a_2084_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2075_);
v___x_2085_ = lean_unsigned_to_nat(0u);
v_bs_x27_2086_ = lean_array_uset(v_bs_2071_, v_i_2070_, v___x_2085_);
v___x_2087_ = ((size_t)1ULL);
v___x_2088_ = lean_usize_add(v_i_2070_, v___x_2087_);
v___x_2089_ = lean_array_uset(v_bs_x27_2086_, v_i_2070_, v_a_2084_);
v_i_2070_ = v___x_2088_;
v_bs_2071_ = v___x_2089_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2091_, lean_object* v_i_2092_, lean_object* v_bs_2093_){
_start:
{
size_t v_sz_boxed_2094_; size_t v_i_boxed_2095_; lean_object* v_res_2096_; 
v_sz_boxed_2094_ = lean_unbox_usize(v_sz_2091_);
lean_dec(v_sz_2091_);
v_i_boxed_2095_ = lean_unbox_usize(v_i_2092_);
lean_dec(v_i_2092_);
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2094_, v_i_boxed_2095_, v_bs_2093_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(lean_object* v_x_2097_){
_start:
{
if (lean_obj_tag(v_x_2097_) == 4)
{
lean_object* v_elems_2098_; size_t v_sz_2099_; size_t v___x_2100_; lean_object* v___x_2101_; 
v_elems_2098_ = lean_ctor_get(v_x_2097_, 0);
lean_inc_ref(v_elems_2098_);
lean_dec_ref(v_x_2097_);
v_sz_2099_ = lean_array_size(v_elems_2098_);
v___x_2100_ = ((size_t)0ULL);
v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_2099_, v___x_2100_, v_elems_2098_);
return v___x_2101_;
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2102_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2103_ = lean_unsigned_to_nat(80u);
v___x_2104_ = l_Lean_Json_pretty(v_x_2097_, v___x_2103_);
v___x_2105_ = lean_string_append(v___x_2102_, v___x_2104_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2107_ = lean_string_append(v___x_2105_, v___x_2106_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(lean_object* v_x_2111_){
_start:
{
if (lean_obj_tag(v_x_2111_) == 0)
{
lean_object* v___x_2112_; 
v___x_2112_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0));
return v___x_2112_;
}
else
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(v_x_2111_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
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
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2130_; 
v_a_2122_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2124_ = v___x_2113_;
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2113_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2130_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_a_2122_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(lean_object* v_expectedID_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_Lsp_Ipc_stdout(v_a_2132_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2278_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2278_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2278_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_IO_FS_Stream_readLspMessage(v_a_2135_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2269_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2269_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2269_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___y_2145_; lean_object* v___y_2146_; 
switch(lean_obj_tag(v_a_2140_))
{
case 2:
{
lean_object* v_id_2152_; lean_object* v_result_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2197_; 
v_id_2152_ = lean_ctor_get(v_a_2140_, 0);
v_result_2153_ = lean_ctor_get(v_a_2140_, 1);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_a_2140_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2155_ = v_a_2140_;
v_isShared_2156_ = v_isSharedCheck_2197_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_result_2153_);
lean_inc(v_id_2152_);
lean_dec(v_a_2140_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2197_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
uint8_t v___x_2157_; 
v___x_2157_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2152_, v_expectedID_2131_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; lean_object* v___y_2160_; 
lean_del_object(v___x_2155_);
lean_dec(v_result_2153_);
lean_del_object(v___x_2137_);
v___x_2158_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2131_))
{
case 0:
{
lean_object* v_s_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_s_2171_ = lean_ctor_get(v_expectedID_2131_, 0);
lean_inc_ref(v_s_2171_);
lean_dec_ref(v_expectedID_2131_);
v___x_2172_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2173_ = lean_string_append(v___x_2172_, v_s_2171_);
lean_dec_ref(v_s_2171_);
v___x_2174_ = lean_string_append(v___x_2173_, v___x_2172_);
v___y_2160_ = v___x_2174_;
goto v___jp_2159_;
}
case 1:
{
lean_object* v_n_2175_; lean_object* v___x_2176_; 
v_n_2175_ = lean_ctor_get(v_expectedID_2131_, 0);
lean_inc_ref(v_n_2175_);
lean_dec_ref(v_expectedID_2131_);
v___x_2176_ = l_Lean_JsonNumber_toString(v_n_2175_);
v___y_2160_ = v___x_2176_;
goto v___jp_2159_;
}
default: 
{
lean_object* v___x_2177_; 
v___x_2177_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2160_ = v___x_2177_;
goto v___jp_2159_;
}
}
v___jp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_string_append(v___x_2158_, v___y_2160_);
lean_dec_ref(v___y_2160_);
v___x_2162_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2163_ = lean_string_append(v___x_2161_, v___x_2162_);
switch(lean_obj_tag(v_id_2152_))
{
case 0:
{
lean_object* v_s_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_s_2164_ = lean_ctor_get(v_id_2152_, 0);
lean_inc_ref(v_s_2164_);
lean_dec_ref(v_id_2152_);
v___x_2165_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2166_ = lean_string_append(v___x_2165_, v_s_2164_);
lean_dec_ref(v_s_2164_);
v___x_2167_ = lean_string_append(v___x_2166_, v___x_2165_);
v___y_2145_ = v___x_2163_;
v___y_2146_ = v___x_2167_;
goto v___jp_2144_;
}
case 1:
{
lean_object* v_n_2168_; lean_object* v___x_2169_; 
v_n_2168_ = lean_ctor_get(v_id_2152_, 0);
lean_inc_ref(v_n_2168_);
lean_dec_ref(v_id_2152_);
v___x_2169_ = l_Lean_JsonNumber_toString(v_n_2168_);
v___y_2145_ = v___x_2163_;
v___y_2146_ = v___x_2169_;
goto v___jp_2144_;
}
default: 
{
lean_object* v___x_2170_; 
v___x_2170_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2145_ = v___x_2163_;
v___y_2146_ = v___x_2170_;
goto v___jp_2144_;
}
}
}
}
else
{
lean_object* v___x_2178_; 
lean_dec(v_id_2152_);
lean_del_object(v___x_2142_);
lean_inc(v_result_2153_);
v___x_2178_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(v_result_2153_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2188_; 
lean_del_object(v___x_2155_);
lean_dec(v_expectedID_2131_);
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref(v___x_2178_);
v___x_2180_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2181_ = l_Lean_Json_compress(v_result_2153_);
v___x_2182_ = lean_string_append(v___x_2180_, v___x_2181_);
lean_dec_ref(v___x_2181_);
v___x_2183_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2184_ = lean_string_append(v___x_2182_, v___x_2183_);
v___x_2185_ = lean_string_append(v___x_2184_, v_a_2179_);
lean_dec(v_a_2179_);
v___x_2186_ = lean_mk_io_user_error(v___x_2185_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 1);
lean_ctor_set(v___x_2137_, 0, v___x_2186_);
v___x_2188_ = v___x_2137_;
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
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; 
lean_dec(v_result_2153_);
v_a_2190_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2190_);
lean_dec_ref(v___x_2178_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 0);
lean_ctor_set(v___x_2155_, 1, v_a_2190_);
lean_ctor_set(v___x_2155_, 0, v_expectedID_2131_);
v___x_2192_ = v___x_2155_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_expectedID_2131_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_a_2190_);
v___x_2192_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2194_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2192_);
v___x_2194_ = v___x_2137_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2198_; uint8_t v_code_2199_; lean_object* v_message_2200_; lean_object* v_data_x3f_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___x_2233_; lean_object* v___y_2235_; 
lean_del_object(v___x_2142_);
lean_dec(v_expectedID_2131_);
v_id_2198_ = lean_ctor_get(v_a_2140_, 0);
lean_inc(v_id_2198_);
v_code_2199_ = lean_ctor_get_uint8(v_a_2140_, sizeof(void*)*3);
v_message_2200_ = lean_ctor_get(v_a_2140_, 1);
lean_inc_ref(v_message_2200_);
v_data_x3f_2201_ = lean_ctor_get(v_a_2140_, 2);
lean_inc(v_data_x3f_2201_);
lean_dec_ref(v_a_2140_);
v___x_2202_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2203_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2233_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2198_))
{
case 0:
{
lean_object* v_s_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
v_s_2251_ = lean_ctor_get(v_id_2198_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_id_2198_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v_id_2198_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_s_2251_);
lean_dec(v_id_2198_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set_tag(v___x_2253_, 3);
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_s_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
v___y_2235_ = v___x_2256_;
goto v___jp_2234_;
}
}
}
case 1:
{
lean_object* v_n_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_n_2259_ = lean_ctor_get(v_id_2198_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_id_2198_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v_id_2198_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_n_2259_);
lean_dec(v_id_2198_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set_tag(v___x_2261_, 2);
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_n_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
v___y_2235_ = v___x_2264_;
goto v___jp_2234_;
}
}
}
default: 
{
lean_object* v___x_2267_; 
v___x_2267_ = lean_box(0);
v___y_2235_ = v___x_2267_;
goto v___jp_2234_;
}
}
v___jp_2204_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
lean_inc(v___y_2208_);
lean_inc_ref(v___y_2205_);
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___y_2205_);
lean_ctor_set(v___x_2209_, 1, v___y_2208_);
v___x_2210_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_message_2200_);
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2209_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2217_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2216_, v_data_x3f_2201_);
lean_dec(v_data_x3f_2201_);
v___x_2218_ = l_List_appendTR___redArg(v___x_2215_, v___x_2217_);
v___x_2219_ = l_Lean_Json_mkObj(v___x_2218_);
lean_dec(v___x_2218_);
lean_inc_ref(v___y_2206_);
v___x_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___y_2206_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___x_2213_);
v___x_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___y_2207_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2203_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = l_Lean_Json_mkObj(v___x_2223_);
lean_dec_ref(v___x_2223_);
v___x_2225_ = l_Lean_Json_compress(v___x_2224_);
v___x_2226_ = lean_string_append(v___x_2202_, v___x_2225_);
lean_dec_ref(v___x_2225_);
v___x_2227_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2228_ = lean_string_append(v___x_2226_, v___x_2227_);
v___x_2229_ = lean_mk_io_user_error(v___x_2228_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 1);
lean_ctor_set(v___x_2137_, 0, v___x_2229_);
v___x_2231_ = v___x_2137_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
v___jp_2234_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2233_);
lean_ctor_set(v___x_2236_, 1, v___y_2235_);
v___x_2237_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2238_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2199_)
{
case 0:
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2239_;
goto v___jp_2204_;
}
case 1:
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2240_;
goto v___jp_2204_;
}
case 2:
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2241_;
goto v___jp_2204_;
}
case 3:
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2242_;
goto v___jp_2204_;
}
case 4:
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2243_;
goto v___jp_2204_;
}
case 5:
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2244_;
goto v___jp_2204_;
}
case 6:
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2245_;
goto v___jp_2204_;
}
case 7:
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2246_;
goto v___jp_2204_;
}
case 8:
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2247_;
goto v___jp_2204_;
}
case 9:
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2248_;
goto v___jp_2204_;
}
case 10:
{
lean_object* v___x_2249_; 
v___x_2249_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2249_;
goto v___jp_2204_;
}
default: 
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2205_ = v___x_2238_;
v___y_2206_ = v___x_2237_;
v___y_2207_ = v___x_2236_;
v___y_2208_ = v___x_2250_;
goto v___jp_2204_;
}
}
}
}
default: 
{
lean_del_object(v___x_2142_);
lean_dec(v_a_2140_);
lean_del_object(v___x_2137_);
goto _start;
}
}
v___jp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2147_ = lean_string_append(v___y_2145_, v___y_2146_);
lean_dec_ref(v___y_2146_);
v___x_2148_ = lean_mk_io_user_error(v___x_2147_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set_tag(v___x_2142_, 1);
lean_ctor_set(v___x_2142_, 0, v___x_2148_);
v___x_2150_ = v___x_2142_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_del_object(v___x_2137_);
lean_dec(v_expectedID_2131_);
v_a_2270_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2139_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2139_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec(v_expectedID_2131_);
v_a_2279_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2134_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2134_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1___boxed(lean_object* v_expectedID_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v_expectedID_2287_, v_a_2288_);
lean_dec_ref(v_a_2288_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(lean_object* v_as_2291_, size_t v_sz_2292_, size_t v_i_2293_, lean_object* v_b_2294_, lean_object* v___y_2295_){
_start:
{
uint8_t v___x_2297_; 
v___x_2297_ = lean_usize_dec_lt(v_i_2293_, v_sz_2292_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v_b_2294_);
return v___x_2298_;
}
else
{
lean_object* v_fst_2299_; lean_object* v_snd_2300_; lean_object* v_a_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_fst_2299_ = lean_ctor_get(v_b_2294_, 0);
lean_inc(v_fst_2299_);
v_snd_2300_ = lean_ctor_get(v_b_2294_, 1);
lean_inc(v_snd_2300_);
lean_dec_ref(v_b_2294_);
v_a_2301_ = lean_array_uget_borrowed(v_as_2291_, v_i_2293_);
v___x_2302_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2303_ = lean_box(1);
lean_inc(v_a_2301_);
v___x_2304_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2299_, v_a_2301_, v___x_2302_, v___x_2303_, v___y_2295_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v_fst_2306_; lean_object* v_snd_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2318_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref(v___x_2304_);
v_fst_2306_ = lean_ctor_get(v_a_2305_, 0);
v_snd_2307_ = lean_ctor_get(v_a_2305_, 1);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_a_2305_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2309_ = v_a_2305_;
v_isShared_2310_ = v_isSharedCheck_2318_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_snd_2307_);
lean_inc(v_fst_2306_);
lean_dec(v_a_2305_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2318_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_array_push(v_snd_2300_, v_fst_2306_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v___x_2311_);
lean_ctor_set(v___x_2309_, 0, v_snd_2307_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_snd_2307_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
size_t v___x_2314_; size_t v___x_2315_; 
v___x_2314_ = ((size_t)1ULL);
v___x_2315_ = lean_usize_add(v_i_2293_, v___x_2314_);
v_i_2293_ = v___x_2315_;
v_b_2294_ = v___x_2313_;
goto _start;
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_snd_2300_);
v_a_2319_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2304_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2304_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2___boxed(lean_object* v_as_2327_, lean_object* v_sz_2328_, lean_object* v_i_2329_, lean_object* v_b_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
size_t v_sz_boxed_2333_; size_t v_i_boxed_2334_; lean_object* v_res_2335_; 
v_sz_boxed_2333_ = lean_unbox_usize(v_sz_2328_);
lean_dec(v_sz_2328_);
v_i_boxed_2334_ = lean_unbox_usize(v_i_2329_);
lean_dec(v_i_2329_);
v_res_2335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v_as_2327_, v_sz_boxed_2333_, v_i_boxed_2334_, v_b_2330_, v___y_2331_);
lean_dec_ref(v___y_2331_);
lean_dec_ref(v_as_2327_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(lean_object* v_v_2336_){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = l_Lean_Lsp_instToJsonCallHierarchyPrepareParams_toJson(v_v_2336_);
v___x_2338_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(lean_object* v_h_2339_, lean_object* v_r_2340_){
_start:
{
lean_object* v_id_2342_; lean_object* v_method_2343_; lean_object* v_param_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2364_; 
v_id_2342_ = lean_ctor_get(v_r_2340_, 0);
v_method_2343_ = lean_ctor_get(v_r_2340_, 1);
v_param_2344_ = lean_ctor_get(v_r_2340_, 2);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_r_2340_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2346_ = v_r_2340_;
v_isShared_2347_ = v_isSharedCheck_2364_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_param_2344_);
lean_inc(v_method_2343_);
lean_inc(v_id_2342_);
lean_dec(v_r_2340_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2364_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___y_2349_; lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(v_param_2344_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v___x_2355_; 
lean_dec_ref(v___x_2354_);
v___x_2355_ = lean_box(0);
v___y_2349_ = v___x_2355_;
goto v___jp_2348_;
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
v_a_2356_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2354_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2354_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
v___y_2349_ = v___x_2361_;
goto v___jp_2348_;
}
}
}
v___jp_2348_:
{
lean_object* v___x_2351_; 
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 2, v___y_2349_);
v___x_2351_ = v___x_2346_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_id_2342_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_method_2343_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v___y_2349_);
v___x_2351_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_IO_FS_Stream_writeLspMessage(v_h_2339_, v___x_2351_);
return v___x_2352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0___boxed(lean_object* v_h_2365_, lean_object* v_r_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_h_2365_, v_r_2366_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(lean_object* v_r_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___x_2372_; lean_object* v_a_2373_; lean_object* v___x_2374_; 
v___x_2372_ = l_Lean_Lsp_Ipc_stdin(v_a_2370_);
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref(v___x_2372_);
v___x_2374_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_a_2373_, v_r_2369_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0___boxed(lean_object* v_r_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v_r_2375_, v_a_2376_);
lean_dec_ref(v_a_2376_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(lean_object* v_requestNo_2382_, lean_object* v_uri_2383_, lean_object* v_pos_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
lean_inc(v_requestNo_2382_);
v___x_2387_ = l_Lean_JsonNumber_fromNat(v_requestNo_2382_);
v___x_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
v___x_2389_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_uri_2383_);
lean_ctor_set(v___x_2390_, 1, v_pos_2384_);
lean_inc_ref(v___x_2388_);
v___x_2391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2388_);
lean_ctor_set(v___x_2391_, 1, v___x_2389_);
lean_ctor_set(v___x_2391_, 2, v___x_2390_);
v___x_2392_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2391_, v_a_2385_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v___x_2393_; 
lean_dec_ref(v___x_2392_);
v___x_2393_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2388_, v_a_2385_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v_result_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2437_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref(v___x_2393_);
v_result_2395_ = lean_ctor_get(v_a_2394_, 1);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_a_2394_);
if (v_isSharedCheck_2437_ == 0)
{
lean_object* v_unused_2438_; 
v_unused_2438_ = lean_ctor_get(v_a_2394_, 0);
lean_dec(v_unused_2438_);
v___x_2397_ = v_a_2394_;
v_isShared_2398_ = v_isSharedCheck_2437_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_result_2395_);
lean_dec(v_a_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2437_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___y_2402_; 
v___x_2399_ = lean_unsigned_to_nat(1u);
v___x_2400_ = lean_nat_add(v_requestNo_2382_, v___x_2399_);
lean_dec(v_requestNo_2382_);
if (lean_obj_tag(v_result_2395_) == 0)
{
lean_object* v___x_2435_; 
v___x_2435_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2402_ = v___x_2435_;
goto v___jp_2401_;
}
else
{
lean_object* v_val_2436_; 
v_val_2436_ = lean_ctor_get(v_result_2395_, 0);
lean_inc(v_val_2436_);
lean_dec_ref(v_result_2395_);
v___y_2402_ = v_val_2436_;
goto v___jp_2401_;
}
v___jp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 1, v___x_2403_);
lean_ctor_set(v___x_2397_, 0, v___x_2400_);
v___x_2405_ = v___x_2397_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
size_t v_sz_2406_; size_t v___x_2407_; lean_object* v___x_2408_; 
v_sz_2406_ = lean_array_size(v___y_2402_);
v___x_2407_ = ((size_t)0ULL);
v___x_2408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v___y_2402_, v_sz_2406_, v___x_2407_, v___x_2405_, v_a_2385_);
lean_dec_ref(v___y_2402_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2425_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2425_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2425_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v_fst_2413_; lean_object* v_snd_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2424_; 
v_fst_2413_ = lean_ctor_get(v_a_2409_, 0);
v_snd_2414_ = lean_ctor_get(v_a_2409_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_a_2409_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2416_ = v_a_2409_;
v_isShared_2417_ = v_isSharedCheck_2424_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_snd_2414_);
lean_inc(v_fst_2413_);
lean_dec(v_a_2409_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2424_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v_fst_2413_);
lean_ctor_set(v___x_2416_, 0, v_snd_2414_);
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_snd_2414_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_fst_2413_);
v___x_2419_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2421_; 
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2419_);
v___x_2421_ = v___x_2411_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2408_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2408_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec(v_requestNo_2382_);
v_a_2439_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2393_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2393_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec_ref(v___x_2388_);
lean_dec(v_requestNo_2382_);
v_a_2447_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2392_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2392_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___boxed(lean_object* v_requestNo_2455_, lean_object* v_uri_2456_, lean_object* v_pos_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(v_requestNo_2455_, v_uri_2456_, v_pos_2457_, v_a_2458_);
lean_dec_ref(v_a_2458_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2461_, size_t v_i_2462_, lean_object* v_bs_2463_){
_start:
{
uint8_t v___x_2464_; 
v___x_2464_ = lean_usize_dec_lt(v_i_2462_, v_sz_2461_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2465_, 0, v_bs_2463_);
return v___x_2465_;
}
else
{
lean_object* v_v_2466_; lean_object* v___x_2467_; 
v_v_2466_ = lean_array_uget_borrowed(v_bs_2463_, v_i_2462_);
lean_inc(v_v_2466_);
v___x_2467_ = l_Lean_Lsp_instFromJsonCallHierarchyOutgoingCall_fromJson(v_v_2466_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec_ref(v_bs_2463_);
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v_bs_x27_2478_; size_t v___x_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
v_a_2476_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2476_);
lean_dec_ref(v___x_2467_);
v___x_2477_ = lean_unsigned_to_nat(0u);
v_bs_x27_2478_ = lean_array_uset(v_bs_2463_, v_i_2462_, v___x_2477_);
v___x_2479_ = ((size_t)1ULL);
v___x_2480_ = lean_usize_add(v_i_2462_, v___x_2479_);
v___x_2481_ = lean_array_uset(v_bs_x27_2478_, v_i_2462_, v_a_2476_);
v_i_2462_ = v___x_2480_;
v_bs_2463_ = v___x_2481_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2483_, lean_object* v_i_2484_, lean_object* v_bs_2485_){
_start:
{
size_t v_sz_boxed_2486_; size_t v_i_boxed_2487_; lean_object* v_res_2488_; 
v_sz_boxed_2486_ = lean_unbox_usize(v_sz_2483_);
lean_dec(v_sz_2483_);
v_i_boxed_2487_ = lean_unbox_usize(v_i_2484_);
lean_dec(v_i_2484_);
v_res_2488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2486_, v_i_boxed_2487_, v_bs_2485_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(lean_object* v_x_2489_){
_start:
{
if (lean_obj_tag(v_x_2489_) == 4)
{
lean_object* v_elems_2490_; size_t v_sz_2491_; size_t v___x_2492_; lean_object* v___x_2493_; 
v_elems_2490_ = lean_ctor_get(v_x_2489_, 0);
lean_inc_ref(v_elems_2490_);
lean_dec_ref(v_x_2489_);
v_sz_2491_ = lean_array_size(v_elems_2490_);
v___x_2492_ = ((size_t)0ULL);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_2491_, v___x_2492_, v_elems_2490_);
return v___x_2493_;
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2494_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2495_ = lean_unsigned_to_nat(80u);
v___x_2496_ = l_Lean_Json_pretty(v_x_2489_, v___x_2495_);
v___x_2497_ = lean_string_append(v___x_2494_, v___x_2496_);
lean_dec_ref(v___x_2496_);
v___x_2498_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2499_ = lean_string_append(v___x_2497_, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
return v___x_2500_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(lean_object* v_x_2503_){
_start:
{
if (lean_obj_tag(v_x_2503_) == 0)
{
lean_object* v___x_2504_; 
v___x_2504_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0));
return v___x_2504_;
}
else
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(v_x_2503_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
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
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2522_; 
v_a_2514_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2516_ = v___x_2505_;
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2505_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2518_, 0, v_a_2514_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2518_);
v___x_2520_ = v___x_2516_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(lean_object* v_expectedID_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_Lsp_Ipc_stdout(v_a_2524_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2670_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2529_ = v___x_2526_;
v_isShared_2530_ = v_isSharedCheck_2670_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2670_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_IO_FS_Stream_readLspMessage(v_a_2527_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2661_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2661_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2661_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___y_2537_; lean_object* v___y_2538_; 
switch(lean_obj_tag(v_a_2532_))
{
case 2:
{
lean_object* v_id_2544_; lean_object* v_result_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2589_; 
v_id_2544_ = lean_ctor_get(v_a_2532_, 0);
v_result_2545_ = lean_ctor_get(v_a_2532_, 1);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_a_2532_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2547_ = v_a_2532_;
v_isShared_2548_ = v_isSharedCheck_2589_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_result_2545_);
lean_inc(v_id_2544_);
lean_dec(v_a_2532_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2589_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
uint8_t v___x_2549_; 
v___x_2549_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2544_, v_expectedID_2523_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___y_2552_; 
lean_del_object(v___x_2547_);
lean_dec(v_result_2545_);
lean_del_object(v___x_2529_);
v___x_2550_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2523_))
{
case 0:
{
lean_object* v_s_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_s_2563_ = lean_ctor_get(v_expectedID_2523_, 0);
lean_inc_ref(v_s_2563_);
lean_dec_ref(v_expectedID_2523_);
v___x_2564_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2565_ = lean_string_append(v___x_2564_, v_s_2563_);
lean_dec_ref(v_s_2563_);
v___x_2566_ = lean_string_append(v___x_2565_, v___x_2564_);
v___y_2552_ = v___x_2566_;
goto v___jp_2551_;
}
case 1:
{
lean_object* v_n_2567_; lean_object* v___x_2568_; 
v_n_2567_ = lean_ctor_get(v_expectedID_2523_, 0);
lean_inc_ref(v_n_2567_);
lean_dec_ref(v_expectedID_2523_);
v___x_2568_ = l_Lean_JsonNumber_toString(v_n_2567_);
v___y_2552_ = v___x_2568_;
goto v___jp_2551_;
}
default: 
{
lean_object* v___x_2569_; 
v___x_2569_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2552_ = v___x_2569_;
goto v___jp_2551_;
}
}
v___jp_2551_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = lean_string_append(v___x_2550_, v___y_2552_);
lean_dec_ref(v___y_2552_);
v___x_2554_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2555_ = lean_string_append(v___x_2553_, v___x_2554_);
switch(lean_obj_tag(v_id_2544_))
{
case 0:
{
lean_object* v_s_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_s_2556_ = lean_ctor_get(v_id_2544_, 0);
lean_inc_ref(v_s_2556_);
lean_dec_ref(v_id_2544_);
v___x_2557_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2558_ = lean_string_append(v___x_2557_, v_s_2556_);
lean_dec_ref(v_s_2556_);
v___x_2559_ = lean_string_append(v___x_2558_, v___x_2557_);
v___y_2537_ = v___x_2555_;
v___y_2538_ = v___x_2559_;
goto v___jp_2536_;
}
case 1:
{
lean_object* v_n_2560_; lean_object* v___x_2561_; 
v_n_2560_ = lean_ctor_get(v_id_2544_, 0);
lean_inc_ref(v_n_2560_);
lean_dec_ref(v_id_2544_);
v___x_2561_ = l_Lean_JsonNumber_toString(v_n_2560_);
v___y_2537_ = v___x_2555_;
v___y_2538_ = v___x_2561_;
goto v___jp_2536_;
}
default: 
{
lean_object* v___x_2562_; 
v___x_2562_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2537_ = v___x_2555_;
v___y_2538_ = v___x_2562_;
goto v___jp_2536_;
}
}
}
}
else
{
lean_object* v___x_2570_; 
lean_dec(v_id_2544_);
lean_del_object(v___x_2534_);
lean_inc(v_result_2545_);
v___x_2570_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(v_result_2545_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
lean_del_object(v___x_2547_);
lean_dec(v_expectedID_2523_);
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref(v___x_2570_);
v___x_2572_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2573_ = l_Lean_Json_compress(v_result_2545_);
v___x_2574_ = lean_string_append(v___x_2572_, v___x_2573_);
lean_dec_ref(v___x_2573_);
v___x_2575_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2576_ = lean_string_append(v___x_2574_, v___x_2575_);
v___x_2577_ = lean_string_append(v___x_2576_, v_a_2571_);
lean_dec(v_a_2571_);
v___x_2578_ = lean_mk_io_user_error(v___x_2577_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set_tag(v___x_2529_, 1);
lean_ctor_set(v___x_2529_, 0, v___x_2578_);
v___x_2580_ = v___x_2529_;
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
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; 
lean_dec(v_result_2545_);
v_a_2582_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2582_);
lean_dec_ref(v___x_2570_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set_tag(v___x_2547_, 0);
lean_ctor_set(v___x_2547_, 1, v_a_2582_);
lean_ctor_set(v___x_2547_, 0, v_expectedID_2523_);
v___x_2584_ = v___x_2547_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_expectedID_2523_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_a_2582_);
v___x_2584_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v___x_2586_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 0, v___x_2584_);
v___x_2586_ = v___x_2529_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2590_; uint8_t v_code_2591_; lean_object* v_message_2592_; lean_object* v_data_x3f_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___x_2625_; lean_object* v___y_2627_; 
lean_del_object(v___x_2534_);
lean_dec(v_expectedID_2523_);
v_id_2590_ = lean_ctor_get(v_a_2532_, 0);
lean_inc(v_id_2590_);
v_code_2591_ = lean_ctor_get_uint8(v_a_2532_, sizeof(void*)*3);
v_message_2592_ = lean_ctor_get(v_a_2532_, 1);
lean_inc_ref(v_message_2592_);
v_data_x3f_2593_ = lean_ctor_get(v_a_2532_, 2);
lean_inc(v_data_x3f_2593_);
lean_dec_ref(v_a_2532_);
v___x_2594_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2595_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2625_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2590_))
{
case 0:
{
lean_object* v_s_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
v_s_2643_ = lean_ctor_get(v_id_2590_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_id_2590_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v_id_2590_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_s_2643_);
lean_dec(v_id_2590_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
lean_ctor_set_tag(v___x_2645_, 3);
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_s_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
v___y_2627_ = v___x_2648_;
goto v___jp_2626_;
}
}
}
case 1:
{
lean_object* v_n_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
v_n_2651_ = lean_ctor_get(v_id_2590_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_id_2590_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v_id_2590_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_n_2651_);
lean_dec(v_id_2590_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
lean_ctor_set_tag(v___x_2653_, 2);
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_n_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
v___y_2627_ = v___x_2656_;
goto v___jp_2626_;
}
}
}
default: 
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_box(0);
v___y_2627_ = v___x_2659_;
goto v___jp_2626_;
}
}
v___jp_2596_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2597_);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___y_2597_);
lean_ctor_set(v___x_2601_, 1, v___y_2600_);
v___x_2602_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2603_, 0, v_message_2592_);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_box(0);
v___x_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2601_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2609_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2608_, v_data_x3f_2593_);
lean_dec(v_data_x3f_2593_);
v___x_2610_ = l_List_appendTR___redArg(v___x_2607_, v___x_2609_);
v___x_2611_ = l_Lean_Json_mkObj(v___x_2610_);
lean_dec(v___x_2610_);
lean_inc_ref(v___y_2598_);
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___y_2598_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___x_2605_);
v___x_2614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___y_2599_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2595_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = l_Lean_Json_mkObj(v___x_2615_);
lean_dec_ref(v___x_2615_);
v___x_2617_ = l_Lean_Json_compress(v___x_2616_);
v___x_2618_ = lean_string_append(v___x_2594_, v___x_2617_);
lean_dec_ref(v___x_2617_);
v___x_2619_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2620_ = lean_string_append(v___x_2618_, v___x_2619_);
v___x_2621_ = lean_mk_io_user_error(v___x_2620_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set_tag(v___x_2529_, 1);
lean_ctor_set(v___x_2529_, 0, v___x_2621_);
v___x_2623_ = v___x_2529_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
v___jp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2625_);
lean_ctor_set(v___x_2628_, 1, v___y_2627_);
v___x_2629_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2630_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2591_)
{
case 0:
{
lean_object* v___x_2631_; 
v___x_2631_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2631_;
goto v___jp_2596_;
}
case 1:
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2632_;
goto v___jp_2596_;
}
case 2:
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2633_;
goto v___jp_2596_;
}
case 3:
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2634_;
goto v___jp_2596_;
}
case 4:
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2635_;
goto v___jp_2596_;
}
case 5:
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2636_;
goto v___jp_2596_;
}
case 6:
{
lean_object* v___x_2637_; 
v___x_2637_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2637_;
goto v___jp_2596_;
}
case 7:
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2638_;
goto v___jp_2596_;
}
case 8:
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2639_;
goto v___jp_2596_;
}
case 9:
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2640_;
goto v___jp_2596_;
}
case 10:
{
lean_object* v___x_2641_; 
v___x_2641_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2641_;
goto v___jp_2596_;
}
default: 
{
lean_object* v___x_2642_; 
v___x_2642_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2597_ = v___x_2630_;
v___y_2598_ = v___x_2629_;
v___y_2599_ = v___x_2628_;
v___y_2600_ = v___x_2642_;
goto v___jp_2596_;
}
}
}
}
default: 
{
lean_del_object(v___x_2534_);
lean_dec(v_a_2532_);
lean_del_object(v___x_2529_);
goto _start;
}
}
v___jp_2536_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2539_ = lean_string_append(v___y_2537_, v___y_2538_);
lean_dec_ref(v___y_2538_);
v___x_2540_ = lean_mk_io_user_error(v___x_2539_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set_tag(v___x_2534_, 1);
lean_ctor_set(v___x_2534_, 0, v___x_2540_);
v___x_2542_ = v___x_2534_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_del_object(v___x_2529_);
lean_dec(v_expectedID_2523_);
v_a_2662_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2531_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2531_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec(v_expectedID_2523_);
v_a_2671_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2526_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2526_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1___boxed(lean_object* v_expectedID_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v_expectedID_2679_, v_a_2680_);
lean_dec_ref(v_a_2680_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(lean_object* v_v_2683_){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = l_Lean_Lsp_instToJsonCallHierarchyOutgoingCallsParams_toJson(v_v_2683_);
v___x_2685_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(lean_object* v_h_2686_, lean_object* v_r_2687_){
_start:
{
lean_object* v_id_2689_; lean_object* v_method_2690_; lean_object* v_param_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2711_; 
v_id_2689_ = lean_ctor_get(v_r_2687_, 0);
v_method_2690_ = lean_ctor_get(v_r_2687_, 1);
v_param_2691_ = lean_ctor_get(v_r_2687_, 2);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_r_2687_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2693_ = v_r_2687_;
v_isShared_2694_ = v_isSharedCheck_2711_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_param_2691_);
lean_inc(v_method_2690_);
lean_inc(v_id_2689_);
lean_dec(v_r_2687_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2711_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___y_2696_; lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(v_param_2691_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v___x_2702_; 
lean_dec_ref(v___x_2701_);
v___x_2702_ = lean_box(0);
v___y_2696_ = v___x_2702_;
goto v___jp_2695_;
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
v_a_2703_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2701_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2701_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
v___y_2696_ = v___x_2708_;
goto v___jp_2695_;
}
}
}
v___jp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 2, v___y_2696_);
v___x_2698_ = v___x_2693_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_id_2689_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_method_2690_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v___y_2696_);
v___x_2698_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_IO_FS_Stream_writeLspMessage(v_h_2686_, v___x_2698_);
return v___x_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0___boxed(lean_object* v_h_2712_, lean_object* v_r_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_h_2712_, v_r_2713_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(lean_object* v_r_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v___x_2719_; lean_object* v_a_2720_; lean_object* v___x_2721_; 
v___x_2719_ = l_Lean_Lsp_Ipc_stdin(v_a_2717_);
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref(v___x_2719_);
v___x_2721_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_a_2720_, v_r_2716_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0___boxed(lean_object* v_r_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v_r_2722_, v_a_2723_);
lean_dec_ref(v_a_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(lean_object* v_requestNo_2729_, lean_object* v_item_2730_, lean_object* v_fromRanges_2731_, lean_object* v_visited_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v_name_2735_; uint8_t v___x_2736_; 
v_name_2735_ = lean_ctor_get(v_item_2730_, 0);
v___x_2736_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_2735_, v_visited_2732_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_inc(v_requestNo_2729_);
v___x_2737_ = l_Lean_JsonNumber_fromNat(v_requestNo_2729_);
v___x_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
v___x_2739_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_2730_);
lean_inc_ref(v___x_2738_);
v___x_2740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
lean_ctor_set(v___x_2740_, 2, v_item_2730_);
v___x_2741_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v___x_2740_, v_a_2733_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; 
lean_dec_ref(v___x_2741_);
v___x_2742_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v___x_2738_, v_a_2733_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2780_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref(v___x_2742_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_box(0);
lean_inc_ref(v_name_2735_);
v___x_2787_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_2735_, v___x_2786_, v_visited_2732_);
v___y_2780_ = v___x_2787_;
goto v___jp_2779_;
}
else
{
v___y_2780_ = v_visited_2732_;
goto v___jp_2779_;
}
v___jp_2744_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; size_t v_sz_2750_; size_t v___x_2751_; lean_object* v___x_2752_; 
v___x_2748_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___y_2745_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v_sz_2750_ = lean_array_size(v___y_2747_);
v___x_2751_ = ((size_t)0ULL);
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___y_2746_, v___y_2747_, v_sz_2750_, v___x_2751_, v___x_2749_, v_a_2733_);
lean_dec_ref(v___y_2747_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2770_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2755_ = v___x_2752_;
v_isShared_2756_ = v_isSharedCheck_2770_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2770_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v_fst_2757_; lean_object* v_snd_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2769_; 
v_fst_2757_ = lean_ctor_get(v_a_2753_, 0);
v_snd_2758_ = lean_ctor_get(v_a_2753_, 1);
v_isSharedCheck_2769_ = !lean_is_exclusive(v_a_2753_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2760_ = v_a_2753_;
v_isShared_2761_ = v_isSharedCheck_2769_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_snd_2758_);
lean_inc(v_fst_2757_);
lean_dec(v_a_2753_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2769_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2762_, 0, v_item_2730_);
lean_ctor_set(v___x_2762_, 1, v_fromRanges_2731_);
lean_ctor_set(v___x_2762_, 2, v_snd_2758_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 1, v_fst_2757_);
lean_ctor_set(v___x_2760_, 0, v___x_2762_);
v___x_2764_ = v___x_2760_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2762_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_fst_2757_);
v___x_2764_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2766_; 
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 0, v___x_2764_);
v___x_2766_ = v___x_2755_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec_ref(v_fromRanges_2731_);
lean_dec_ref(v_item_2730_);
v_a_2771_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2752_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2752_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
v___jp_2779_:
{
lean_object* v_result_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_result_2781_ = lean_ctor_get(v_a_2743_, 1);
lean_inc(v_result_2781_);
lean_dec(v_a_2743_);
v___x_2782_ = lean_unsigned_to_nat(1u);
v___x_2783_ = lean_nat_add(v_requestNo_2729_, v___x_2782_);
lean_dec(v_requestNo_2729_);
if (lean_obj_tag(v_result_2781_) == 0)
{
lean_object* v___x_2784_; 
v___x_2784_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1));
v___y_2745_ = v___x_2783_;
v___y_2746_ = v___y_2780_;
v___y_2747_ = v___x_2784_;
goto v___jp_2744_;
}
else
{
lean_object* v_val_2785_; 
v_val_2785_ = lean_ctor_get(v_result_2781_, 0);
lean_inc(v_val_2785_);
lean_dec_ref(v_result_2781_);
v___y_2745_ = v___x_2783_;
v___y_2746_ = v___y_2780_;
v___y_2747_ = v_val_2785_;
goto v___jp_2744_;
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_visited_2732_);
lean_dec_ref(v_fromRanges_2731_);
lean_dec_ref(v_item_2730_);
lean_dec(v_requestNo_2729_);
v_a_2788_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2742_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2742_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v___x_2738_);
lean_dec(v_visited_2732_);
lean_dec_ref(v_fromRanges_2731_);
lean_dec_ref(v_item_2730_);
lean_dec(v_requestNo_2729_);
v_a_2796_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2741_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2741_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_dec(v_visited_2732_);
lean_dec_ref(v_fromRanges_2731_);
v___x_2804_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2805_, 0, v_item_2730_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
lean_ctor_set(v___x_2805_, 2, v___x_2804_);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
lean_ctor_set(v___x_2806_, 1, v_requestNo_2729_);
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(lean_object* v___x_2808_, lean_object* v_as_2809_, size_t v_sz_2810_, size_t v_i_2811_, lean_object* v_b_2812_, lean_object* v___y_2813_){
_start:
{
uint8_t v___x_2815_; 
v___x_2815_ = lean_usize_dec_lt(v_i_2811_, v_sz_2810_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; 
lean_dec(v___x_2808_);
v___x_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2816_, 0, v_b_2812_);
return v___x_2816_;
}
else
{
lean_object* v_fst_2817_; lean_object* v_snd_2818_; lean_object* v_a_2819_; lean_object* v_to_2820_; lean_object* v_fromRanges_2821_; lean_object* v___x_2822_; 
v_fst_2817_ = lean_ctor_get(v_b_2812_, 0);
lean_inc(v_fst_2817_);
v_snd_2818_ = lean_ctor_get(v_b_2812_, 1);
lean_inc(v_snd_2818_);
lean_dec_ref(v_b_2812_);
v_a_2819_ = lean_array_uget_borrowed(v_as_2809_, v_i_2811_);
v_to_2820_ = lean_ctor_get(v_a_2819_, 0);
v_fromRanges_2821_ = lean_ctor_get(v_a_2819_, 1);
lean_inc(v___x_2808_);
lean_inc_ref(v_fromRanges_2821_);
lean_inc_ref(v_to_2820_);
v___x_2822_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2817_, v_to_2820_, v_fromRanges_2821_, v___x_2808_, v___y_2813_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v_fst_2824_; lean_object* v_snd_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2836_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref(v___x_2822_);
v_fst_2824_ = lean_ctor_get(v_a_2823_, 0);
v_snd_2825_ = lean_ctor_get(v_a_2823_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_a_2823_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2827_ = v_a_2823_;
v_isShared_2828_ = v_isSharedCheck_2836_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_snd_2825_);
lean_inc(v_fst_2824_);
lean_dec(v_a_2823_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2836_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2829_; lean_object* v___x_2831_; 
v___x_2829_ = lean_array_push(v_snd_2818_, v_fst_2824_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 1, v___x_2829_);
lean_ctor_set(v___x_2827_, 0, v_snd_2825_);
v___x_2831_ = v___x_2827_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_snd_2825_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v___x_2829_);
v___x_2831_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
size_t v___x_2832_; size_t v___x_2833_; 
v___x_2832_ = ((size_t)1ULL);
v___x_2833_ = lean_usize_add(v_i_2811_, v___x_2832_);
v_i_2811_ = v___x_2833_;
v_b_2812_ = v___x_2831_;
goto _start;
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v_snd_2818_);
lean_dec(v___x_2808_);
v_a_2837_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2822_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2822_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2___boxed(lean_object* v___x_2845_, lean_object* v_as_2846_, lean_object* v_sz_2847_, lean_object* v_i_2848_, lean_object* v_b_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
size_t v_sz_boxed_2852_; size_t v_i_boxed_2853_; lean_object* v_res_2854_; 
v_sz_boxed_2852_ = lean_unbox_usize(v_sz_2847_);
lean_dec(v_sz_2847_);
v_i_boxed_2853_ = lean_unbox_usize(v_i_2848_);
lean_dec(v_i_2848_);
v_res_2854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___x_2845_, v_as_2846_, v_sz_boxed_2852_, v_i_boxed_2853_, v_b_2849_, v___y_2850_);
lean_dec_ref(v___y_2850_);
lean_dec_ref(v_as_2846_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___boxed(lean_object* v_requestNo_2855_, lean_object* v_item_2856_, lean_object* v_fromRanges_2857_, lean_object* v_visited_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_requestNo_2855_, v_item_2856_, v_fromRanges_2857_, v_visited_2858_, v_a_2859_);
lean_dec_ref(v_a_2859_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(lean_object* v_as_2862_, size_t v_sz_2863_, size_t v_i_2864_, lean_object* v_b_2865_, lean_object* v___y_2866_){
_start:
{
uint8_t v___x_2868_; 
v___x_2868_ = lean_usize_dec_lt(v_i_2864_, v_sz_2863_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; 
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v_b_2865_);
return v___x_2869_;
}
else
{
lean_object* v_fst_2870_; lean_object* v_snd_2871_; lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_fst_2870_ = lean_ctor_get(v_b_2865_, 0);
lean_inc(v_fst_2870_);
v_snd_2871_ = lean_ctor_get(v_b_2865_, 1);
lean_inc(v_snd_2871_);
lean_dec_ref(v_b_2865_);
v_a_2872_ = lean_array_uget_borrowed(v_as_2862_, v_i_2864_);
v___x_2873_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2874_ = lean_box(1);
lean_inc(v_a_2872_);
v___x_2875_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2870_, v_a_2872_, v___x_2873_, v___x_2874_, v___y_2866_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v_fst_2877_; lean_object* v_snd_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2889_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref(v___x_2875_);
v_fst_2877_ = lean_ctor_get(v_a_2876_, 0);
v_snd_2878_ = lean_ctor_get(v_a_2876_, 1);
v_isSharedCheck_2889_ = !lean_is_exclusive(v_a_2876_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2880_ = v_a_2876_;
v_isShared_2881_ = v_isSharedCheck_2889_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_snd_2878_);
lean_inc(v_fst_2877_);
lean_dec(v_a_2876_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2889_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2882_ = lean_array_push(v_snd_2871_, v_fst_2877_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 1, v___x_2882_);
lean_ctor_set(v___x_2880_, 0, v_snd_2878_);
v___x_2884_ = v___x_2880_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_snd_2878_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
size_t v___x_2885_; size_t v___x_2886_; 
v___x_2885_ = ((size_t)1ULL);
v___x_2886_ = lean_usize_add(v_i_2864_, v___x_2885_);
v_i_2864_ = v___x_2886_;
v_b_2865_ = v___x_2884_;
goto _start;
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_snd_2871_);
v_a_2890_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2875_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2875_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0___boxed(lean_object* v_as_2898_, lean_object* v_sz_2899_, lean_object* v_i_2900_, lean_object* v_b_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
size_t v_sz_boxed_2904_; size_t v_i_boxed_2905_; lean_object* v_res_2906_; 
v_sz_boxed_2904_ = lean_unbox_usize(v_sz_2899_);
lean_dec(v_sz_2899_);
v_i_boxed_2905_ = lean_unbox_usize(v_i_2900_);
lean_dec(v_i_2900_);
v_res_2906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v_as_2898_, v_sz_boxed_2904_, v_i_boxed_2905_, v_b_2901_, v___y_2902_);
lean_dec_ref(v___y_2902_);
lean_dec_ref(v_as_2898_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(lean_object* v_requestNo_2907_, lean_object* v_uri_2908_, lean_object* v_pos_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
lean_inc(v_requestNo_2907_);
v___x_2912_ = l_Lean_JsonNumber_fromNat(v_requestNo_2907_);
v___x_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
v___x_2914_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v_uri_2908_);
lean_ctor_set(v___x_2915_, 1, v_pos_2909_);
lean_inc_ref(v___x_2913_);
v___x_2916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2913_);
lean_ctor_set(v___x_2916_, 1, v___x_2914_);
lean_ctor_set(v___x_2916_, 2, v___x_2915_);
v___x_2917_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2916_, v_a_2910_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v___x_2918_; 
lean_dec_ref(v___x_2917_);
v___x_2918_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2913_, v_a_2910_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v_result_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2962_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref(v___x_2918_);
v_result_2920_ = lean_ctor_get(v_a_2919_, 1);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_a_2919_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; 
v_unused_2963_ = lean_ctor_get(v_a_2919_, 0);
lean_dec(v_unused_2963_);
v___x_2922_ = v_a_2919_;
v_isShared_2923_ = v_isSharedCheck_2962_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_result_2920_);
lean_dec(v_a_2919_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2962_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___y_2927_; 
v___x_2924_ = lean_unsigned_to_nat(1u);
v___x_2925_ = lean_nat_add(v_requestNo_2907_, v___x_2924_);
lean_dec(v_requestNo_2907_);
if (lean_obj_tag(v_result_2920_) == 0)
{
lean_object* v___x_2960_; 
v___x_2960_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2927_ = v___x_2960_;
goto v___jp_2926_;
}
else
{
lean_object* v_val_2961_; 
v_val_2961_ = lean_ctor_get(v_result_2920_, 0);
lean_inc(v_val_2961_);
lean_dec_ref(v_result_2920_);
v___y_2927_ = v_val_2961_;
goto v___jp_2926_;
}
v___jp_2926_:
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
v___x_2928_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 1, v___x_2928_);
lean_ctor_set(v___x_2922_, 0, v___x_2925_);
v___x_2930_ = v___x_2922_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2925_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
size_t v_sz_2931_; size_t v___x_2932_; lean_object* v___x_2933_; 
v_sz_2931_ = lean_array_size(v___y_2927_);
v___x_2932_ = ((size_t)0ULL);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v___y_2927_, v_sz_2931_, v___x_2932_, v___x_2930_, v_a_2910_);
lean_dec_ref(v___y_2927_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2950_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_2950_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2950_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v_fst_2938_; lean_object* v_snd_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2949_; 
v_fst_2938_ = lean_ctor_get(v_a_2934_, 0);
v_snd_2939_ = lean_ctor_get(v_a_2934_, 1);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_a_2934_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2941_ = v_a_2934_;
v_isShared_2942_ = v_isSharedCheck_2949_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_snd_2939_);
lean_inc(v_fst_2938_);
lean_dec(v_a_2934_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2949_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v_fst_2938_);
lean_ctor_set(v___x_2941_, 0, v_snd_2939_);
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_snd_2939_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_fst_2938_);
v___x_2944_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
lean_object* v___x_2946_; 
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 0, v___x_2944_);
v___x_2946_ = v___x_2936_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2944_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
v_a_2951_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2933_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2933_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec(v_requestNo_2907_);
v_a_2964_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2918_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2918_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec_ref(v___x_2913_);
lean_dec(v_requestNo_2907_);
v_a_2972_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2917_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2917_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy___boxed(lean_object* v_requestNo_2980_, lean_object* v_uri_2981_, lean_object* v_pos_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(v_requestNo_2980_, v_uri_2981_, v_pos_2982_, v_a_2983_);
lean_dec_ref(v_a_2983_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(lean_object* v_j_2986_, lean_object* v_k_2987_){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = l_Lean_Json_getObjValD(v_j_2986_, v_k_2987_);
v___x_2989_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v___x_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0___boxed(lean_object* v_j_2990_, lean_object* v_k_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_j_2990_, v_k_2991_);
lean_dec_ref(v_k_2991_);
return v_res_2992_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2999_ = 1;
v___x_3000_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1));
v___x_3001_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3000_, v___x_2999_);
return v___x_3001_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3002_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_3003_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2);
v___x_3004_ = lean_string_append(v___x_3003_, v___x_3002_);
return v___x_3004_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_3006_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3007_ = lean_string_append(v___x_3006_, v___x_3005_);
return v___x_3007_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3009_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4);
v___x_3010_ = lean_string_append(v___x_3009_, v___x_3008_);
return v___x_3010_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_3012_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3013_ = lean_string_append(v___x_3012_, v___x_3011_);
return v___x_3013_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3015_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6);
v___x_3016_ = lean_string_append(v___x_3015_, v___x_3014_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(lean_object* v_json_3017_){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_3017_);
v___x_3019_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_json_3017_, v___x_3018_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v_json_3017_);
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3029_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3029_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3027_; 
v___x_3024_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5);
v___x_3025_ = lean_string_append(v___x_3024_, v_a_3020_);
lean_dec(v_a_3020_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3025_);
v___x_3027_ = v___x_3022_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
else
{
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec(v_json_3017_);
v_a_3030_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3019_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3019_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set_tag(v___x_3032_, 0);
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_a_3038_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3038_);
lean_dec_ref(v___x_3019_);
v___x_3039_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3040_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_json_3017_, v___x_3039_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3050_; 
lean_dec(v_a_3038_);
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3050_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3050_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3045_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7);
v___x_3046_ = lean_string_append(v___x_3045_, v_a_3041_);
lean_dec(v_a_3041_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3046_);
v___x_3048_ = v___x_3043_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
else
{
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec(v_a_3038_);
v_a_3051_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3040_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3040_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
lean_ctor_set_tag(v___x_3053_, 0);
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3067_; 
v_a_3059_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3061_ = v___x_3040_;
v_isShared_3062_ = v_isSharedCheck_3067_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3040_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3067_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v_a_3038_);
lean_ctor_set(v___x_3063_, 1, v_a_3059_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3063_);
v___x_3065_ = v___x_3061_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_3068_, size_t v_i_3069_, lean_object* v_bs_3070_){
_start:
{
uint8_t v___x_3071_; 
v___x_3071_ = lean_usize_dec_lt(v_i_3069_, v_sz_3068_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3072_, 0, v_bs_3070_);
return v___x_3072_;
}
else
{
lean_object* v_v_3073_; lean_object* v___x_3074_; 
v_v_3073_ = lean_array_uget_borrowed(v_bs_3070_, v_i_3069_);
lean_inc(v_v_3073_);
v___x_3074_ = l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(v_v_3073_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec_ref(v_bs_3070_);
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3074_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3084_; lean_object* v_bs_x27_3085_; size_t v___x_3086_; size_t v___x_3087_; lean_object* v___x_3088_; 
v_a_3083_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3083_);
lean_dec_ref(v___x_3074_);
v___x_3084_ = lean_unsigned_to_nat(0u);
v_bs_x27_3085_ = lean_array_uset(v_bs_3070_, v_i_3069_, v___x_3084_);
v___x_3086_ = ((size_t)1ULL);
v___x_3087_ = lean_usize_add(v_i_3069_, v___x_3086_);
v___x_3088_ = lean_array_uset(v_bs_x27_3085_, v_i_3069_, v_a_3083_);
v_i_3069_ = v___x_3087_;
v_bs_3070_ = v___x_3088_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_3090_){
_start:
{
if (lean_obj_tag(v_x_3090_) == 4)
{
lean_object* v_elems_3091_; size_t v_sz_3092_; size_t v___x_3093_; lean_object* v___x_3094_; 
v_elems_3091_ = lean_ctor_get(v_x_3090_, 0);
lean_inc_ref(v_elems_3091_);
lean_dec_ref(v_x_3090_);
v_sz_3092_ = lean_array_size(v_elems_3091_);
v___x_3093_ = ((size_t)0ULL);
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_3092_, v___x_3093_, v_elems_3091_);
return v___x_3094_;
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3095_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3096_ = lean_unsigned_to_nat(80u);
v___x_3097_ = l_Lean_Json_pretty(v_x_3090_, v___x_3096_);
v___x_3098_ = lean_string_append(v___x_3095_, v___x_3097_);
lean_dec_ref(v___x_3097_);
v___x_3099_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3100_ = lean_string_append(v___x_3098_, v___x_3099_);
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
return v___x_3101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(lean_object* v_j_3102_, lean_object* v_k_3103_){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = l_Lean_Json_getObjValD(v_j_3102_, v_k_3103_);
v___x_3105_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(v___x_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1___boxed(lean_object* v_j_3106_, lean_object* v_k_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_j_3106_, v_k_3107_);
lean_dec_ref(v_k_3107_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_3109_, lean_object* v_i_3110_, lean_object* v_bs_3111_){
_start:
{
size_t v_sz_boxed_3112_; size_t v_i_boxed_3113_; lean_object* v_res_3114_; 
v_sz_boxed_3112_ = lean_unbox_usize(v_sz_3109_);
lean_dec(v_sz_3109_);
v_i_boxed_3113_ = lean_unbox_usize(v_i_3110_);
lean_dec(v_i_3110_);
v_res_3114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_3112_, v_i_boxed_3113_, v_bs_3111_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(lean_object* v_x_3117_){
_start:
{
lean_object* v_item_3118_; lean_object* v_children_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3139_; 
v_item_3118_ = lean_ctor_get(v_x_3117_, 0);
v_children_3119_ = lean_ctor_get(v_x_3117_, 1);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_x_3117_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3121_ = v_x_3117_;
v_isShared_3122_ = v_isSharedCheck_3139_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_children_3119_);
lean_inc(v_item_3118_);
lean_dec(v_x_3117_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3139_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3123_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_3124_ = l_Lean_Lsp_instToJsonLeanImport_toJson(v_item_3118_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 1, v___x_3124_);
lean_ctor_set(v___x_3121_, 0, v___x_3123_);
v___x_3126_ = v___x_3121_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3127_ = lean_box(0);
v___x_3128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3126_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
v___x_3129_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3130_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(v_children_3119_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3129_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set(v___x_3132_, 1, v___x_3127_);
v___x_3133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
lean_ctor_set(v___x_3133_, 1, v___x_3127_);
v___x_3134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3128_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_3136_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_3134_, v___x_3135_);
v___x_3137_ = l_Lean_Json_mkObj(v___x_3136_);
lean_dec(v___x_3136_);
return v___x_3137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(size_t v_sz_3140_, size_t v_i_3141_, lean_object* v_bs_3142_){
_start:
{
uint8_t v___x_3143_; 
v___x_3143_ = lean_usize_dec_lt(v_i_3141_, v_sz_3140_);
if (v___x_3143_ == 0)
{
return v_bs_3142_;
}
else
{
lean_object* v_v_3144_; lean_object* v___x_3145_; lean_object* v_bs_x27_3146_; lean_object* v___x_3147_; size_t v___x_3148_; size_t v___x_3149_; lean_object* v___x_3150_; 
v_v_3144_ = lean_array_uget(v_bs_3142_, v_i_3141_);
v___x_3145_ = lean_unsigned_to_nat(0u);
v_bs_x27_3146_ = lean_array_uset(v_bs_3142_, v_i_3141_, v___x_3145_);
v___x_3147_ = l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(v_v_3144_);
v___x_3148_ = ((size_t)1ULL);
v___x_3149_ = lean_usize_add(v_i_3141_, v___x_3148_);
v___x_3150_ = lean_array_uset(v_bs_x27_3146_, v_i_3141_, v___x_3147_);
v_i_3141_ = v___x_3149_;
v_bs_3142_ = v___x_3150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(lean_object* v_a_3152_){
_start:
{
size_t v_sz_3153_; size_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v_sz_3153_ = lean_array_size(v_a_3152_);
v___x_3154_ = ((size_t)0ULL);
v___x_3155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_3153_, v___x_3154_, v_a_3152_);
v___x_3156_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3157_, lean_object* v_i_3158_, lean_object* v_bs_3159_){
_start:
{
size_t v_sz_boxed_3160_; size_t v_i_boxed_3161_; lean_object* v_res_3162_; 
v_sz_boxed_3160_ = lean_unbox_usize(v_sz_3157_);
lean_dec(v_sz_3157_);
v_i_boxed_3161_ = lean_unbox_usize(v_i_3158_);
lean_dec(v_i_3158_);
v_res_3162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_boxed_3160_, v_i_boxed_3161_, v_bs_3159_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(size_t v_sz_3165_, size_t v_i_3166_, lean_object* v_bs_3167_){
_start:
{
uint8_t v___x_3168_; 
v___x_3168_ = lean_usize_dec_lt(v_i_3166_, v_sz_3165_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; 
v___x_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3169_, 0, v_bs_3167_);
return v___x_3169_;
}
else
{
lean_object* v_v_3170_; lean_object* v___x_3171_; 
v_v_3170_ = lean_array_uget_borrowed(v_bs_3167_, v_i_3166_);
lean_inc(v_v_3170_);
v___x_3171_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v_v_3170_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec_ref(v_bs_3167_);
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3171_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3181_; lean_object* v_bs_x27_3182_; size_t v___x_3183_; size_t v___x_3184_; lean_object* v___x_3185_; 
v_a_3180_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3180_);
lean_dec_ref(v___x_3171_);
v___x_3181_ = lean_unsigned_to_nat(0u);
v_bs_x27_3182_ = lean_array_uset(v_bs_3167_, v_i_3166_, v___x_3181_);
v___x_3183_ = ((size_t)1ULL);
v___x_3184_ = lean_usize_add(v_i_3166_, v___x_3183_);
v___x_3185_ = lean_array_uset(v_bs_x27_3182_, v_i_3166_, v_a_3180_);
v_i_3166_ = v___x_3184_;
v_bs_3167_ = v___x_3185_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_3187_, lean_object* v_i_3188_, lean_object* v_bs_3189_){
_start:
{
size_t v_sz_boxed_3190_; size_t v_i_boxed_3191_; lean_object* v_res_3192_; 
v_sz_boxed_3190_ = lean_unbox_usize(v_sz_3187_);
lean_dec(v_sz_3187_);
v_i_boxed_3191_ = lean_unbox_usize(v_i_3188_);
lean_dec(v_i_3188_);
v_res_3192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_boxed_3190_, v_i_boxed_3191_, v_bs_3189_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(lean_object* v_x_3193_){
_start:
{
if (lean_obj_tag(v_x_3193_) == 4)
{
lean_object* v_elems_3194_; size_t v_sz_3195_; size_t v___x_3196_; lean_object* v___x_3197_; 
v_elems_3194_ = lean_ctor_get(v_x_3193_, 0);
lean_inc_ref(v_elems_3194_);
lean_dec_ref(v_x_3193_);
v_sz_3195_ = lean_array_size(v_elems_3194_);
v___x_3196_ = ((size_t)0ULL);
v___x_3197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_3195_, v___x_3196_, v_elems_3194_);
return v___x_3197_;
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3198_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3199_ = lean_unsigned_to_nat(80u);
v___x_3200_ = l_Lean_Json_pretty(v_x_3193_, v___x_3199_);
v___x_3201_ = lean_string_append(v___x_3198_, v___x_3200_);
lean_dec_ref(v___x_3200_);
v___x_3202_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3203_ = lean_string_append(v___x_3201_, v___x_3202_);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
return v___x_3204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(lean_object* v_expectedID_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Lean_Lsp_Ipc_stdout(v_a_3206_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3352_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3352_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3352_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_IO_FS_Stream_readLspMessage(v_a_3209_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3343_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3216_ = v___x_3213_;
v_isShared_3217_ = v_isSharedCheck_3343_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3213_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3343_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___y_3219_; lean_object* v___y_3220_; 
switch(lean_obj_tag(v_a_3214_))
{
case 2:
{
lean_object* v_id_3226_; lean_object* v_result_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3271_; 
v_id_3226_ = lean_ctor_get(v_a_3214_, 0);
v_result_3227_ = lean_ctor_get(v_a_3214_, 1);
v_isSharedCheck_3271_ = !lean_is_exclusive(v_a_3214_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3229_ = v_a_3214_;
v_isShared_3230_ = v_isSharedCheck_3271_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_result_3227_);
lean_inc(v_id_3226_);
lean_dec(v_a_3214_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3271_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
uint8_t v___x_3231_; 
v___x_3231_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3226_, v_expectedID_3205_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v___y_3234_; 
lean_del_object(v___x_3229_);
lean_dec(v_result_3227_);
lean_del_object(v___x_3211_);
v___x_3232_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3205_))
{
case 0:
{
lean_object* v_s_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v_s_3245_ = lean_ctor_get(v_expectedID_3205_, 0);
lean_inc_ref(v_s_3245_);
lean_dec_ref(v_expectedID_3205_);
v___x_3246_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3247_ = lean_string_append(v___x_3246_, v_s_3245_);
lean_dec_ref(v_s_3245_);
v___x_3248_ = lean_string_append(v___x_3247_, v___x_3246_);
v___y_3234_ = v___x_3248_;
goto v___jp_3233_;
}
case 1:
{
lean_object* v_n_3249_; lean_object* v___x_3250_; 
v_n_3249_ = lean_ctor_get(v_expectedID_3205_, 0);
lean_inc_ref(v_n_3249_);
lean_dec_ref(v_expectedID_3205_);
v___x_3250_ = l_Lean_JsonNumber_toString(v_n_3249_);
v___y_3234_ = v___x_3250_;
goto v___jp_3233_;
}
default: 
{
lean_object* v___x_3251_; 
v___x_3251_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3234_ = v___x_3251_;
goto v___jp_3233_;
}
}
v___jp_3233_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3235_ = lean_string_append(v___x_3232_, v___y_3234_);
lean_dec_ref(v___y_3234_);
v___x_3236_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3237_ = lean_string_append(v___x_3235_, v___x_3236_);
switch(lean_obj_tag(v_id_3226_))
{
case 0:
{
lean_object* v_s_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v_s_3238_ = lean_ctor_get(v_id_3226_, 0);
lean_inc_ref(v_s_3238_);
lean_dec_ref(v_id_3226_);
v___x_3239_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3240_ = lean_string_append(v___x_3239_, v_s_3238_);
lean_dec_ref(v_s_3238_);
v___x_3241_ = lean_string_append(v___x_3240_, v___x_3239_);
v___y_3219_ = v___x_3237_;
v___y_3220_ = v___x_3241_;
goto v___jp_3218_;
}
case 1:
{
lean_object* v_n_3242_; lean_object* v___x_3243_; 
v_n_3242_ = lean_ctor_get(v_id_3226_, 0);
lean_inc_ref(v_n_3242_);
lean_dec_ref(v_id_3226_);
v___x_3243_ = l_Lean_JsonNumber_toString(v_n_3242_);
v___y_3219_ = v___x_3237_;
v___y_3220_ = v___x_3243_;
goto v___jp_3218_;
}
default: 
{
lean_object* v___x_3244_; 
v___x_3244_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3219_ = v___x_3237_;
v___y_3220_ = v___x_3244_;
goto v___jp_3218_;
}
}
}
}
else
{
lean_object* v___x_3252_; 
lean_dec(v_id_3226_);
lean_del_object(v___x_3216_);
lean_inc(v_result_3227_);
v___x_3252_ = l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(v_result_3227_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
lean_del_object(v___x_3229_);
lean_dec(v_expectedID_3205_);
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref(v___x_3252_);
v___x_3254_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3255_ = l_Lean_Json_compress(v_result_3227_);
v___x_3256_ = lean_string_append(v___x_3254_, v___x_3255_);
lean_dec_ref(v___x_3255_);
v___x_3257_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3258_ = lean_string_append(v___x_3256_, v___x_3257_);
v___x_3259_ = lean_string_append(v___x_3258_, v_a_3253_);
lean_dec(v_a_3253_);
v___x_3260_ = lean_mk_io_user_error(v___x_3259_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set_tag(v___x_3211_, 1);
lean_ctor_set(v___x_3211_, 0, v___x_3260_);
v___x_3262_ = v___x_3211_;
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
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; 
lean_dec(v_result_3227_);
v_a_3264_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3264_);
lean_dec_ref(v___x_3252_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set_tag(v___x_3229_, 0);
lean_ctor_set(v___x_3229_, 1, v_a_3264_);
lean_ctor_set(v___x_3229_, 0, v_expectedID_3205_);
v___x_3266_ = v___x_3229_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_expectedID_3205_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_a_3264_);
v___x_3266_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
lean_object* v___x_3268_; 
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3266_);
v___x_3268_ = v___x_3211_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3272_; uint8_t v_code_3273_; lean_object* v_message_3274_; lean_object* v_data_x3f_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___x_3307_; lean_object* v___y_3309_; 
lean_del_object(v___x_3216_);
lean_dec(v_expectedID_3205_);
v_id_3272_ = lean_ctor_get(v_a_3214_, 0);
lean_inc(v_id_3272_);
v_code_3273_ = lean_ctor_get_uint8(v_a_3214_, sizeof(void*)*3);
v_message_3274_ = lean_ctor_get(v_a_3214_, 1);
lean_inc_ref(v_message_3274_);
v_data_x3f_3275_ = lean_ctor_get(v_a_3214_, 2);
lean_inc(v_data_x3f_3275_);
lean_dec_ref(v_a_3214_);
v___x_3276_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3277_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3307_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3272_))
{
case 0:
{
lean_object* v_s_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
v_s_3325_ = lean_ctor_get(v_id_3272_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v_id_3272_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v_id_3272_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_s_3325_);
lean_dec(v_id_3272_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 3);
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_s_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
v___y_3309_ = v___x_3330_;
goto v___jp_3308_;
}
}
}
case 1:
{
lean_object* v_n_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
v_n_3333_ = lean_ctor_get(v_id_3272_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_id_3272_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v_id_3272_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_n_3333_);
lean_dec(v_id_3272_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set_tag(v___x_3335_, 2);
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_n_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
v___y_3309_ = v___x_3338_;
goto v___jp_3308_;
}
}
}
default: 
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_box(0);
v___y_3309_ = v___x_3341_;
goto v___jp_3308_;
}
}
v___jp_3278_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3305_; 
lean_inc(v___y_3282_);
lean_inc_ref(v___y_3280_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___y_3280_);
lean_ctor_set(v___x_3283_, 1, v___y_3282_);
v___x_3284_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3285_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3285_, 0, v_message_3274_);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_box(0);
v___x_3288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3283_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3291_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3290_, v_data_x3f_3275_);
lean_dec(v_data_x3f_3275_);
v___x_3292_ = l_List_appendTR___redArg(v___x_3289_, v___x_3291_);
v___x_3293_ = l_Lean_Json_mkObj(v___x_3292_);
lean_dec(v___x_3292_);
lean_inc_ref(v___y_3279_);
v___x_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___y_3279_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
lean_ctor_set(v___x_3295_, 1, v___x_3287_);
v___x_3296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___y_3281_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3277_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = l_Lean_Json_mkObj(v___x_3297_);
lean_dec_ref(v___x_3297_);
v___x_3299_ = l_Lean_Json_compress(v___x_3298_);
v___x_3300_ = lean_string_append(v___x_3276_, v___x_3299_);
lean_dec_ref(v___x_3299_);
v___x_3301_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3302_ = lean_string_append(v___x_3300_, v___x_3301_);
v___x_3303_ = lean_mk_io_user_error(v___x_3302_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set_tag(v___x_3211_, 1);
lean_ctor_set(v___x_3211_, 0, v___x_3303_);
v___x_3305_ = v___x_3211_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
v___jp_3308_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3307_);
lean_ctor_set(v___x_3310_, 1, v___y_3309_);
v___x_3311_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3312_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3273_)
{
case 0:
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3313_;
goto v___jp_3278_;
}
case 1:
{
lean_object* v___x_3314_; 
v___x_3314_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3314_;
goto v___jp_3278_;
}
case 2:
{
lean_object* v___x_3315_; 
v___x_3315_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3315_;
goto v___jp_3278_;
}
case 3:
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3316_;
goto v___jp_3278_;
}
case 4:
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3317_;
goto v___jp_3278_;
}
case 5:
{
lean_object* v___x_3318_; 
v___x_3318_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3318_;
goto v___jp_3278_;
}
case 6:
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3319_;
goto v___jp_3278_;
}
case 7:
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3320_;
goto v___jp_3278_;
}
case 8:
{
lean_object* v___x_3321_; 
v___x_3321_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3321_;
goto v___jp_3278_;
}
case 9:
{
lean_object* v___x_3322_; 
v___x_3322_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3322_;
goto v___jp_3278_;
}
case 10:
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3323_;
goto v___jp_3278_;
}
default: 
{
lean_object* v___x_3324_; 
v___x_3324_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3279_ = v___x_3311_;
v___y_3280_ = v___x_3312_;
v___y_3281_ = v___x_3310_;
v___y_3282_ = v___x_3324_;
goto v___jp_3278_;
}
}
}
}
default: 
{
lean_del_object(v___x_3216_);
lean_dec(v_a_3214_);
lean_del_object(v___x_3211_);
goto _start;
}
}
v___jp_3218_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3221_ = lean_string_append(v___y_3219_, v___y_3220_);
lean_dec_ref(v___y_3220_);
v___x_3222_ = lean_mk_io_user_error(v___x_3221_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set_tag(v___x_3216_, 1);
lean_ctor_set(v___x_3216_, 0, v___x_3222_);
v___x_3224_ = v___x_3216_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_del_object(v___x_3211_);
lean_dec(v_expectedID_3205_);
v_a_3344_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3213_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3213_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec(v_expectedID_3205_);
v_a_3353_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3208_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3208_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1___boxed(lean_object* v_expectedID_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v_expectedID_3361_, v_a_3362_);
lean_dec_ref(v_a_3362_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(lean_object* v_v_3365_){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_v_3365_);
v___x_3367_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3366_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_v_3368_);
lean_dec_ref(v_v_3368_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(lean_object* v_h_3370_, lean_object* v_r_3371_){
_start:
{
lean_object* v_id_3373_; lean_object* v_method_3374_; lean_object* v_param_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3395_; 
v_id_3373_ = lean_ctor_get(v_r_3371_, 0);
v_method_3374_ = lean_ctor_get(v_r_3371_, 1);
v_param_3375_ = lean_ctor_get(v_r_3371_, 2);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_r_3371_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3377_ = v_r_3371_;
v_isShared_3378_ = v_isSharedCheck_3395_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_param_3375_);
lean_inc(v_method_3374_);
lean_inc(v_id_3373_);
lean_dec(v_r_3371_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3395_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___y_3380_; lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_param_3375_);
lean_dec(v_param_3375_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v___x_3386_; 
lean_dec_ref(v___x_3385_);
v___x_3386_ = lean_box(0);
v___y_3380_ = v___x_3386_;
goto v___jp_3379_;
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
v_a_3387_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3385_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3385_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
v___y_3380_ = v___x_3392_;
goto v___jp_3379_;
}
}
}
v___jp_3379_:
{
lean_object* v___x_3382_; 
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 2, v___y_3380_);
v___x_3382_ = v___x_3377_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_id_3373_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_method_3374_);
lean_ctor_set(v_reuseFailAlloc_3384_, 2, v___y_3380_);
v___x_3382_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
lean_object* v___x_3383_; 
v___x_3383_ = l_IO_FS_Stream_writeLspMessage(v_h_3370_, v___x_3382_);
return v___x_3383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0___boxed(lean_object* v_h_3396_, lean_object* v_r_3397_, lean_object* v_a_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_h_3396_, v_r_3397_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(lean_object* v_r_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v___x_3403_; lean_object* v_a_3404_; lean_object* v___x_3405_; 
v___x_3403_ = l_Lean_Lsp_Ipc_stdin(v_a_3401_);
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref(v___x_3403_);
v___x_3405_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_a_3404_, v_r_3400_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0___boxed(lean_object* v_r_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v_r_3406_, v_a_3407_);
lean_dec_ref(v_a_3407_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(lean_object* v_requestNo_3413_, lean_object* v_item_3414_, lean_object* v_visited_3415_, lean_object* v_a_3416_){
_start:
{
lean_object* v_module_3418_; lean_object* v_name_3419_; uint8_t v___x_3420_; 
v_module_3418_ = lean_ctor_get(v_item_3414_, 0);
v_name_3419_ = lean_ctor_get(v_module_3418_, 0);
v___x_3420_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3419_, v_visited_3415_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
lean_inc(v_requestNo_3413_);
v___x_3421_ = l_Lean_JsonNumber_fromNat(v_requestNo_3413_);
v___x_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
v___x_3423_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0));
lean_inc_ref(v_module_3418_);
lean_inc_ref(v___x_3422_);
v___x_3424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
lean_ctor_set(v___x_3424_, 2, v_module_3418_);
v___x_3425_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v___x_3424_, v_a_3416_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v___x_3426_; 
lean_dec_ref(v___x_3425_);
v___x_3426_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3422_, v_a_3416_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___y_3429_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v___x_3426_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = lean_box(0);
lean_inc_ref(v_name_3419_);
v___x_3472_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3419_, v___x_3471_, v_visited_3415_);
v___y_3429_ = v___x_3472_;
goto v___jp_3428_;
}
else
{
v___y_3429_ = v_visited_3415_;
goto v___jp_3428_;
}
v___jp_3428_:
{
lean_object* v_result_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3469_; 
v_result_3430_ = lean_ctor_get(v_a_3427_, 1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_a_3427_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; 
v_unused_3470_ = lean_ctor_get(v_a_3427_, 0);
lean_dec(v_unused_3470_);
v___x_3432_ = v_a_3427_;
v_isShared_3433_ = v_isSharedCheck_3469_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_result_3430_);
lean_dec(v_a_3427_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3469_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3434_ = lean_unsigned_to_nat(1u);
v___x_3435_ = lean_nat_add(v_requestNo_3413_, v___x_3434_);
lean_dec(v_requestNo_3413_);
v___x_3436_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v___x_3436_);
lean_ctor_set(v___x_3432_, 0, v___x_3435_);
v___x_3438_ = v___x_3432_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
size_t v_sz_3439_; size_t v___x_3440_; lean_object* v___x_3441_; 
v_sz_3439_ = lean_array_size(v_result_3430_);
v___x_3440_ = ((size_t)0ULL);
v___x_3441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___y_3429_, v_result_3430_, v_sz_3439_, v___x_3440_, v___x_3438_, v_a_3416_);
lean_dec(v_result_3430_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3459_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3444_ = v___x_3441_;
v_isShared_3445_ = v_isSharedCheck_3459_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3459_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v_fst_3446_; lean_object* v_snd_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3458_; 
v_fst_3446_ = lean_ctor_get(v_a_3442_, 0);
v_snd_3447_ = lean_ctor_get(v_a_3442_, 1);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_a_3442_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3449_ = v_a_3442_;
v_isShared_3450_ = v_isSharedCheck_3458_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_snd_3447_);
lean_inc(v_fst_3446_);
lean_dec(v_a_3442_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3458_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3451_, 0, v_item_3414_);
lean_ctor_set(v___x_3451_, 1, v_snd_3447_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 1, v_fst_3446_);
lean_ctor_set(v___x_3449_, 0, v___x_3451_);
v___x_3453_ = v___x_3449_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_fst_3446_);
v___x_3453_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v___x_3453_);
v___x_3455_ = v___x_3444_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec_ref(v_item_3414_);
v_a_3460_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3441_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3441_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec(v_visited_3415_);
lean_dec_ref(v_item_3414_);
lean_dec(v_requestNo_3413_);
v_a_3473_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3426_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3426_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec_ref(v___x_3422_);
lean_dec(v_visited_3415_);
lean_dec_ref(v_item_3414_);
lean_dec(v_requestNo_3413_);
v_a_3481_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3425_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3425_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
lean_dec(v_visited_3415_);
v___x_3489_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v_item_3414_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
lean_ctor_set(v___x_3491_, 1, v_requestNo_3413_);
v___x_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3491_);
return v___x_3492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(lean_object* v___x_3493_, lean_object* v_as_3494_, size_t v_sz_3495_, size_t v_i_3496_, lean_object* v_b_3497_, lean_object* v___y_3498_){
_start:
{
uint8_t v___x_3500_; 
v___x_3500_ = lean_usize_dec_lt(v_i_3496_, v_sz_3495_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
lean_dec(v___x_3493_);
v___x_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3501_, 0, v_b_3497_);
return v___x_3501_;
}
else
{
lean_object* v_fst_3502_; lean_object* v_snd_3503_; lean_object* v_a_3504_; lean_object* v___x_3505_; 
v_fst_3502_ = lean_ctor_get(v_b_3497_, 0);
lean_inc(v_fst_3502_);
v_snd_3503_ = lean_ctor_get(v_b_3497_, 1);
lean_inc(v_snd_3503_);
lean_dec_ref(v_b_3497_);
v_a_3504_ = lean_array_uget_borrowed(v_as_3494_, v_i_3496_);
lean_inc(v___x_3493_);
lean_inc(v_a_3504_);
v___x_3505_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_fst_3502_, v_a_3504_, v___x_3493_, v___y_3498_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v_fst_3507_; lean_object* v_snd_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3519_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref(v___x_3505_);
v_fst_3507_ = lean_ctor_get(v_a_3506_, 0);
v_snd_3508_ = lean_ctor_get(v_a_3506_, 1);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_a_3506_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3510_ = v_a_3506_;
v_isShared_3511_ = v_isSharedCheck_3519_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_snd_3508_);
lean_inc(v_fst_3507_);
lean_dec(v_a_3506_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3519_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3512_; lean_object* v___x_3514_; 
v___x_3512_ = lean_array_push(v_snd_3503_, v_fst_3507_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___x_3512_);
lean_ctor_set(v___x_3510_, 0, v_snd_3508_);
v___x_3514_ = v___x_3510_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_snd_3508_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
size_t v___x_3515_; size_t v___x_3516_; 
v___x_3515_ = ((size_t)1ULL);
v___x_3516_ = lean_usize_add(v_i_3496_, v___x_3515_);
v_i_3496_ = v___x_3516_;
v_b_3497_ = v___x_3514_;
goto _start;
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec(v_snd_3503_);
lean_dec(v___x_3493_);
v_a_3520_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3505_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3505_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2___boxed(lean_object* v___x_3528_, lean_object* v_as_3529_, lean_object* v_sz_3530_, lean_object* v_i_3531_, lean_object* v_b_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
size_t v_sz_boxed_3535_; size_t v_i_boxed_3536_; lean_object* v_res_3537_; 
v_sz_boxed_3535_ = lean_unbox_usize(v_sz_3530_);
lean_dec(v_sz_3530_);
v_i_boxed_3536_ = lean_unbox_usize(v_i_3531_);
lean_dec(v_i_3531_);
v_res_3537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___x_3528_, v_as_3529_, v_sz_boxed_3535_, v_i_boxed_3536_, v_b_3532_, v___y_3533_);
lean_dec_ref(v___y_3533_);
lean_dec_ref(v_as_3529_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___boxed(lean_object* v_requestNo_3538_, lean_object* v_item_3539_, lean_object* v_visited_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_requestNo_3538_, v_item_3539_, v_visited_3540_, v_a_3541_);
lean_dec_ref(v_a_3541_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(lean_object* v_v_3544_){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(v_v_3544_);
v___x_3546_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3545_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(lean_object* v_h_3547_, lean_object* v_r_3548_){
_start:
{
lean_object* v_id_3550_; lean_object* v_method_3551_; lean_object* v_param_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3572_; 
v_id_3550_ = lean_ctor_get(v_r_3548_, 0);
v_method_3551_ = lean_ctor_get(v_r_3548_, 1);
v_param_3552_ = lean_ctor_get(v_r_3548_, 2);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_r_3548_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3554_ = v_r_3548_;
v_isShared_3555_ = v_isSharedCheck_3572_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_param_3552_);
lean_inc(v_method_3551_);
lean_inc(v_id_3550_);
lean_dec(v_r_3548_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3572_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___y_3557_; lean_object* v___x_3562_; 
v___x_3562_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(v_param_3552_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v___x_3563_; 
lean_dec_ref(v___x_3562_);
v___x_3563_ = lean_box(0);
v___y_3557_ = v___x_3563_;
goto v___jp_3556_;
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
v_a_3564_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3562_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3562_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
v___y_3557_ = v___x_3569_;
goto v___jp_3556_;
}
}
}
v___jp_3556_:
{
lean_object* v___x_3559_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 2, v___y_3557_);
v___x_3559_ = v___x_3554_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_id_3550_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_method_3551_);
lean_ctor_set(v_reuseFailAlloc_3561_, 2, v___y_3557_);
v___x_3559_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_IO_FS_Stream_writeLspMessage(v_h_3547_, v___x_3559_);
return v___x_3560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0___boxed(lean_object* v_h_3573_, lean_object* v_r_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_h_3573_, v_r_3574_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(lean_object* v_r_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v___x_3580_; lean_object* v_a_3581_; lean_object* v___x_3582_; 
v___x_3580_ = l_Lean_Lsp_Ipc_stdin(v_a_3578_);
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref(v___x_3580_);
v___x_3582_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_a_3581_, v_r_3577_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0___boxed(lean_object* v_r_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v_r_3583_, v_a_3584_);
lean_dec_ref(v_a_3584_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(lean_object* v_x_3589_){
_start:
{
if (lean_obj_tag(v_x_3589_) == 0)
{
lean_object* v___x_3590_; 
v___x_3590_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0));
return v___x_3590_;
}
else
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v_x_3589_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3591_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3591_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3608_; 
v_a_3600_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3602_ = v___x_3591_;
v_isShared_3603_ = v_isSharedCheck_3608_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3591_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3608_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3604_; lean_object* v___x_3606_; 
v___x_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3604_, 0, v_a_3600_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v___x_3604_);
v___x_3606_ = v___x_3602_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(lean_object* v_expectedID_3609_, lean_object* v_a_3610_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Lean_Lsp_Ipc_stdout(v_a_3610_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3756_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3615_ = v___x_3612_;
v_isShared_3616_ = v_isSharedCheck_3756_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3612_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3756_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_IO_FS_Stream_readLspMessage(v_a_3613_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3747_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3620_ = v___x_3617_;
v_isShared_3621_ = v_isSharedCheck_3747_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3617_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3747_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___y_3623_; lean_object* v___y_3624_; 
switch(lean_obj_tag(v_a_3618_))
{
case 2:
{
lean_object* v_id_3630_; lean_object* v_result_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3675_; 
v_id_3630_ = lean_ctor_get(v_a_3618_, 0);
v_result_3631_ = lean_ctor_get(v_a_3618_, 1);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_a_3618_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3633_ = v_a_3618_;
v_isShared_3634_ = v_isSharedCheck_3675_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_result_3631_);
lean_inc(v_id_3630_);
lean_dec(v_a_3618_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3675_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
uint8_t v___x_3635_; 
v___x_3635_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3630_, v_expectedID_3609_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; lean_object* v___y_3638_; 
lean_del_object(v___x_3633_);
lean_dec(v_result_3631_);
lean_del_object(v___x_3615_);
v___x_3636_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3609_))
{
case 0:
{
lean_object* v_s_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v_s_3649_ = lean_ctor_get(v_expectedID_3609_, 0);
lean_inc_ref(v_s_3649_);
lean_dec_ref(v_expectedID_3609_);
v___x_3650_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3651_ = lean_string_append(v___x_3650_, v_s_3649_);
lean_dec_ref(v_s_3649_);
v___x_3652_ = lean_string_append(v___x_3651_, v___x_3650_);
v___y_3638_ = v___x_3652_;
goto v___jp_3637_;
}
case 1:
{
lean_object* v_n_3653_; lean_object* v___x_3654_; 
v_n_3653_ = lean_ctor_get(v_expectedID_3609_, 0);
lean_inc_ref(v_n_3653_);
lean_dec_ref(v_expectedID_3609_);
v___x_3654_ = l_Lean_JsonNumber_toString(v_n_3653_);
v___y_3638_ = v___x_3654_;
goto v___jp_3637_;
}
default: 
{
lean_object* v___x_3655_; 
v___x_3655_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3638_ = v___x_3655_;
goto v___jp_3637_;
}
}
v___jp_3637_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = lean_string_append(v___x_3636_, v___y_3638_);
lean_dec_ref(v___y_3638_);
v___x_3640_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3641_ = lean_string_append(v___x_3639_, v___x_3640_);
switch(lean_obj_tag(v_id_3630_))
{
case 0:
{
lean_object* v_s_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v_s_3642_ = lean_ctor_get(v_id_3630_, 0);
lean_inc_ref(v_s_3642_);
lean_dec_ref(v_id_3630_);
v___x_3643_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3644_ = lean_string_append(v___x_3643_, v_s_3642_);
lean_dec_ref(v_s_3642_);
v___x_3645_ = lean_string_append(v___x_3644_, v___x_3643_);
v___y_3623_ = v___x_3641_;
v___y_3624_ = v___x_3645_;
goto v___jp_3622_;
}
case 1:
{
lean_object* v_n_3646_; lean_object* v___x_3647_; 
v_n_3646_ = lean_ctor_get(v_id_3630_, 0);
lean_inc_ref(v_n_3646_);
lean_dec_ref(v_id_3630_);
v___x_3647_ = l_Lean_JsonNumber_toString(v_n_3646_);
v___y_3623_ = v___x_3641_;
v___y_3624_ = v___x_3647_;
goto v___jp_3622_;
}
default: 
{
lean_object* v___x_3648_; 
v___x_3648_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3623_ = v___x_3641_;
v___y_3624_ = v___x_3648_;
goto v___jp_3622_;
}
}
}
}
else
{
lean_object* v___x_3656_; 
lean_dec(v_id_3630_);
lean_del_object(v___x_3620_);
lean_inc(v_result_3631_);
v___x_3656_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(v_result_3631_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
lean_del_object(v___x_3633_);
lean_dec(v_expectedID_3609_);
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref(v___x_3656_);
v___x_3658_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3659_ = l_Lean_Json_compress(v_result_3631_);
v___x_3660_ = lean_string_append(v___x_3658_, v___x_3659_);
lean_dec_ref(v___x_3659_);
v___x_3661_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3662_ = lean_string_append(v___x_3660_, v___x_3661_);
v___x_3663_ = lean_string_append(v___x_3662_, v_a_3657_);
lean_dec(v_a_3657_);
v___x_3664_ = lean_mk_io_user_error(v___x_3663_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 1);
lean_ctor_set(v___x_3615_, 0, v___x_3664_);
v___x_3666_ = v___x_3615_;
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
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; 
lean_dec(v_result_3631_);
v_a_3668_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3668_);
lean_dec_ref(v___x_3656_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 0);
lean_ctor_set(v___x_3633_, 1, v_a_3668_);
lean_ctor_set(v___x_3633_, 0, v_expectedID_3609_);
v___x_3670_ = v___x_3633_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_expectedID_3609_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_a_3668_);
v___x_3670_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3672_; 
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 0, v___x_3670_);
v___x_3672_ = v___x_3615_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3676_; uint8_t v_code_3677_; lean_object* v_message_3678_; lean_object* v_data_x3f_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___x_3711_; lean_object* v___y_3713_; 
lean_del_object(v___x_3620_);
lean_dec(v_expectedID_3609_);
v_id_3676_ = lean_ctor_get(v_a_3618_, 0);
lean_inc(v_id_3676_);
v_code_3677_ = lean_ctor_get_uint8(v_a_3618_, sizeof(void*)*3);
v_message_3678_ = lean_ctor_get(v_a_3618_, 1);
lean_inc_ref(v_message_3678_);
v_data_x3f_3679_ = lean_ctor_get(v_a_3618_, 2);
lean_inc(v_data_x3f_3679_);
lean_dec_ref(v_a_3618_);
v___x_3680_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3681_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3711_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3676_))
{
case 0:
{
lean_object* v_s_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
v_s_3729_ = lean_ctor_get(v_id_3676_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_id_3676_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v_id_3676_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_s_3729_);
lean_dec(v_id_3676_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
lean_ctor_set_tag(v___x_3731_, 3);
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_s_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
v___y_3713_ = v___x_3734_;
goto v___jp_3712_;
}
}
}
case 1:
{
lean_object* v_n_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
v_n_3737_ = lean_ctor_get(v_id_3676_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v_id_3676_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v_id_3676_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_n_3737_);
lean_dec(v_id_3676_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
lean_ctor_set_tag(v___x_3739_, 2);
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_n_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
v___y_3713_ = v___x_3742_;
goto v___jp_3712_;
}
}
}
default: 
{
lean_object* v___x_3745_; 
v___x_3745_ = lean_box(0);
v___y_3713_ = v___x_3745_;
goto v___jp_3712_;
}
}
v___jp_3682_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3709_; 
lean_inc(v___y_3686_);
lean_inc_ref(v___y_3685_);
v___x_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___y_3685_);
lean_ctor_set(v___x_3687_, 1, v___y_3686_);
v___x_3688_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3689_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3689_, 0, v_message_3678_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = lean_box(0);
v___x_3692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3687_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3695_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3694_, v_data_x3f_3679_);
lean_dec(v_data_x3f_3679_);
v___x_3696_ = l_List_appendTR___redArg(v___x_3693_, v___x_3695_);
v___x_3697_ = l_Lean_Json_mkObj(v___x_3696_);
lean_dec(v___x_3696_);
lean_inc_ref(v___y_3683_);
v___x_3698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___y_3683_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
lean_ctor_set(v___x_3699_, 1, v___x_3691_);
v___x_3700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___y_3684_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3681_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = l_Lean_Json_mkObj(v___x_3701_);
lean_dec_ref(v___x_3701_);
v___x_3703_ = l_Lean_Json_compress(v___x_3702_);
v___x_3704_ = lean_string_append(v___x_3680_, v___x_3703_);
lean_dec_ref(v___x_3703_);
v___x_3705_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3706_ = lean_string_append(v___x_3704_, v___x_3705_);
v___x_3707_ = lean_mk_io_user_error(v___x_3706_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 1);
lean_ctor_set(v___x_3615_, 0, v___x_3707_);
v___x_3709_ = v___x_3615_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3707_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
v___jp_3712_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3711_);
lean_ctor_set(v___x_3714_, 1, v___y_3713_);
v___x_3715_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3716_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3677_)
{
case 0:
{
lean_object* v___x_3717_; 
v___x_3717_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3717_;
goto v___jp_3682_;
}
case 1:
{
lean_object* v___x_3718_; 
v___x_3718_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3718_;
goto v___jp_3682_;
}
case 2:
{
lean_object* v___x_3719_; 
v___x_3719_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3719_;
goto v___jp_3682_;
}
case 3:
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3720_;
goto v___jp_3682_;
}
case 4:
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3721_;
goto v___jp_3682_;
}
case 5:
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3722_;
goto v___jp_3682_;
}
case 6:
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3723_;
goto v___jp_3682_;
}
case 7:
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3724_;
goto v___jp_3682_;
}
case 8:
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3725_;
goto v___jp_3682_;
}
case 9:
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3726_;
goto v___jp_3682_;
}
case 10:
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3727_;
goto v___jp_3682_;
}
default: 
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3683_ = v___x_3715_;
v___y_3684_ = v___x_3714_;
v___y_3685_ = v___x_3716_;
v___y_3686_ = v___x_3728_;
goto v___jp_3682_;
}
}
}
}
default: 
{
lean_del_object(v___x_3620_);
lean_dec(v_a_3618_);
lean_del_object(v___x_3615_);
goto _start;
}
}
v___jp_3622_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3625_ = lean_string_append(v___y_3623_, v___y_3624_);
lean_dec_ref(v___y_3624_);
v___x_3626_ = lean_mk_io_user_error(v___x_3625_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set_tag(v___x_3620_, 1);
lean_ctor_set(v___x_3620_, 0, v___x_3626_);
v___x_3628_ = v___x_3620_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3626_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_del_object(v___x_3615_);
lean_dec(v_expectedID_3609_);
v_a_3748_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3617_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3617_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_expectedID_3609_);
v_a_3757_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3612_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3612_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1___boxed(lean_object* v_expectedID_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v_expectedID_3765_, v_a_3766_);
lean_dec_ref(v_a_3766_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports(lean_object* v_requestNo_3773_, lean_object* v_uri_3774_, lean_object* v_a_3775_){
_start:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
lean_inc(v_requestNo_3773_);
v___x_3777_ = l_Lean_JsonNumber_fromNat(v_requestNo_3773_);
v___x_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
v___x_3779_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_3778_);
v___x_3780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3778_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
lean_ctor_set(v___x_3780_, 2, v_uri_3774_);
v___x_3781_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_3780_, v_a_3775_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v___x_3782_; 
lean_dec_ref(v___x_3781_);
v___x_3782_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_3778_, v_a_3775_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3841_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3841_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3841_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v_result_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3839_; 
v_result_3787_ = lean_ctor_get(v_a_3783_, 1);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_a_3783_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v_a_3783_, 0);
lean_dec(v_unused_3840_);
v___x_3789_ = v_a_3783_;
v_isShared_3790_ = v_isSharedCheck_3839_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_result_3787_);
lean_dec(v_a_3783_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3839_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_unsigned_to_nat(1u);
v___x_3792_ = lean_nat_add(v_requestNo_3773_, v___x_3791_);
lean_dec(v_requestNo_3773_);
if (lean_obj_tag(v_result_3787_) == 1)
{
lean_object* v_val_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3831_; 
lean_del_object(v___x_3785_);
v_val_3793_ = lean_ctor_get(v_result_3787_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_result_3787_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3795_ = v_result_3787_;
v_isShared_3796_ = v_isSharedCheck_3831_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_val_3793_);
lean_dec(v_result_3787_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3831_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3797_; lean_object* v___x_3799_; 
v___x_3797_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 1, v___x_3797_);
lean_ctor_set(v___x_3789_, 0, v_val_3793_);
v___x_3799_ = v___x_3789_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_val_3793_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = lean_box(1);
v___x_3801_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v___x_3792_, v___x_3799_, v___x_3800_, v_a_3775_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3821_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3804_ = v___x_3801_;
v_isShared_3805_ = v_isSharedCheck_3821_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3821_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v_fst_3806_; lean_object* v_snd_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3820_; 
v_fst_3806_ = lean_ctor_get(v_a_3802_, 0);
v_snd_3807_ = lean_ctor_get(v_a_3802_, 1);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_a_3802_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3809_ = v_a_3802_;
v_isShared_3810_ = v_isSharedCheck_3820_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_snd_3807_);
lean_inc(v_fst_3806_);
lean_dec(v_a_3802_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3820_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v_fst_3806_);
v___x_3812_ = v___x_3795_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_fst_3806_);
v___x_3812_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3814_; 
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v___x_3812_);
v___x_3814_ = v___x_3809_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3812_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_snd_3807_);
v___x_3814_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3816_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3814_);
v___x_3816_ = v___x_3804_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_del_object(v___x_3795_);
v_a_3822_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3801_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3801_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
}
else
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
lean_dec(v_result_3787_);
v___x_3832_ = lean_box(0);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 1, v___x_3792_);
lean_ctor_set(v___x_3789_, 0, v___x_3832_);
v___x_3834_ = v___x_3789_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3838_, 1, v___x_3792_);
v___x_3834_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3836_; 
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v___x_3834_);
v___x_3836_ = v___x_3785_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec(v_requestNo_3773_);
v_a_3842_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3782_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3782_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref(v___x_3778_);
lean_dec(v_requestNo_3773_);
v_a_3850_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3781_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3781_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___boxed(lean_object* v_requestNo_3858_, lean_object* v_uri_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImports(v_requestNo_3858_, v_uri_3859_, v_a_3860_);
lean_dec_ref(v_a_3860_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(lean_object* v_v_3863_){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_v_3863_);
v___x_3865_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_v_3866_);
lean_dec_ref(v_v_3866_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(lean_object* v_h_3868_, lean_object* v_r_3869_){
_start:
{
lean_object* v_id_3871_; lean_object* v_method_3872_; lean_object* v_param_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3893_; 
v_id_3871_ = lean_ctor_get(v_r_3869_, 0);
v_method_3872_ = lean_ctor_get(v_r_3869_, 1);
v_param_3873_ = lean_ctor_get(v_r_3869_, 2);
v_isSharedCheck_3893_ = !lean_is_exclusive(v_r_3869_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3875_ = v_r_3869_;
v_isShared_3876_ = v_isSharedCheck_3893_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_param_3873_);
lean_inc(v_method_3872_);
lean_inc(v_id_3871_);
lean_dec(v_r_3869_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3893_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___y_3878_; lean_object* v___x_3883_; 
v___x_3883_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_param_3873_);
lean_dec(v_param_3873_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v___x_3884_; 
lean_dec_ref(v___x_3883_);
v___x_3884_ = lean_box(0);
v___y_3878_ = v___x_3884_;
goto v___jp_3877_;
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
v_a_3885_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3883_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3883_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
v___y_3878_ = v___x_3890_;
goto v___jp_3877_;
}
}
}
v___jp_3877_:
{
lean_object* v___x_3880_; 
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 2, v___y_3878_);
v___x_3880_ = v___x_3875_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v_id_3871_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_method_3872_);
lean_ctor_set(v_reuseFailAlloc_3882_, 2, v___y_3878_);
v___x_3880_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_IO_FS_Stream_writeLspMessage(v_h_3868_, v___x_3880_);
return v___x_3881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0___boxed(lean_object* v_h_3894_, lean_object* v_r_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_h_3894_, v_r_3895_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(lean_object* v_r_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v___x_3901_; lean_object* v_a_3902_; lean_object* v___x_3903_; 
v___x_3901_ = l_Lean_Lsp_Ipc_stdin(v_a_3899_);
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref(v___x_3901_);
v___x_3903_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_a_3902_, v_r_3898_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0___boxed(lean_object* v_r_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v_r_3904_, v_a_3905_);
lean_dec_ref(v_a_3905_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(lean_object* v_requestNo_3909_, lean_object* v_item_3910_, lean_object* v_visited_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_module_3914_; lean_object* v_name_3915_; uint8_t v___x_3916_; 
v_module_3914_ = lean_ctor_get(v_item_3910_, 0);
v_name_3915_ = lean_ctor_get(v_module_3914_, 0);
v___x_3916_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3915_, v_visited_3911_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
lean_inc(v_requestNo_3909_);
v___x_3917_ = l_Lean_JsonNumber_fromNat(v_requestNo_3909_);
v___x_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
v___x_3919_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0));
lean_inc_ref(v_module_3914_);
lean_inc_ref(v___x_3918_);
v___x_3920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
lean_ctor_set(v___x_3920_, 2, v_module_3914_);
v___x_3921_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v___x_3920_, v_a_3912_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v___x_3922_; 
lean_dec_ref(v___x_3921_);
v___x_3922_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3918_, v_a_3912_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___y_3925_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3923_);
lean_dec_ref(v___x_3922_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = lean_box(0);
lean_inc_ref(v_name_3915_);
v___x_3968_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3915_, v___x_3967_, v_visited_3911_);
v___y_3925_ = v___x_3968_;
goto v___jp_3924_;
}
else
{
v___y_3925_ = v_visited_3911_;
goto v___jp_3924_;
}
v___jp_3924_:
{
lean_object* v_result_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3965_; 
v_result_3926_ = lean_ctor_get(v_a_3923_, 1);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_a_3923_);
if (v_isSharedCheck_3965_ == 0)
{
lean_object* v_unused_3966_; 
v_unused_3966_ = lean_ctor_get(v_a_3923_, 0);
lean_dec(v_unused_3966_);
v___x_3928_ = v_a_3923_;
v_isShared_3929_ = v_isSharedCheck_3965_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_result_3926_);
lean_dec(v_a_3923_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3965_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3930_ = lean_unsigned_to_nat(1u);
v___x_3931_ = lean_nat_add(v_requestNo_3909_, v___x_3930_);
lean_dec(v_requestNo_3909_);
v___x_3932_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 1, v___x_3932_);
lean_ctor_set(v___x_3928_, 0, v___x_3931_);
v___x_3934_ = v___x_3928_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3931_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
size_t v_sz_3935_; size_t v___x_3936_; lean_object* v___x_3937_; 
v_sz_3935_ = lean_array_size(v_result_3926_);
v___x_3936_ = ((size_t)0ULL);
v___x_3937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___y_3925_, v_result_3926_, v_sz_3935_, v___x_3936_, v___x_3934_, v_a_3912_);
lean_dec(v_result_3926_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3955_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3940_ = v___x_3937_;
v_isShared_3941_ = v_isSharedCheck_3955_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3937_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3955_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v_fst_3942_; lean_object* v_snd_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3954_; 
v_fst_3942_ = lean_ctor_get(v_a_3938_, 0);
v_snd_3943_ = lean_ctor_get(v_a_3938_, 1);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_a_3938_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3945_ = v_a_3938_;
v_isShared_3946_ = v_isSharedCheck_3954_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_snd_3943_);
lean_inc(v_fst_3942_);
lean_dec(v_a_3938_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3954_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3947_; lean_object* v___x_3949_; 
v___x_3947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3947_, 0, v_item_3910_);
lean_ctor_set(v___x_3947_, 1, v_snd_3943_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 1, v_fst_3942_);
lean_ctor_set(v___x_3945_, 0, v___x_3947_);
v___x_3949_ = v___x_3945_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3947_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_fst_3942_);
v___x_3949_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
lean_object* v___x_3951_; 
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3949_);
v___x_3951_ = v___x_3940_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3949_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec_ref(v_item_3910_);
v_a_3956_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3937_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3937_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec(v_visited_3911_);
lean_dec_ref(v_item_3910_);
lean_dec(v_requestNo_3909_);
v_a_3969_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3922_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3922_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec_ref(v___x_3918_);
lean_dec(v_visited_3911_);
lean_dec_ref(v_item_3910_);
lean_dec(v_requestNo_3909_);
v_a_3977_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3921_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3921_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
else
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
lean_dec(v_visited_3911_);
v___x_3985_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v_item_3910_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
lean_ctor_set(v___x_3987_, 1, v_requestNo_3909_);
v___x_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
return v___x_3988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(lean_object* v___x_3989_, lean_object* v_as_3990_, size_t v_sz_3991_, size_t v_i_3992_, lean_object* v_b_3993_, lean_object* v___y_3994_){
_start:
{
uint8_t v___x_3996_; 
v___x_3996_ = lean_usize_dec_lt(v_i_3992_, v_sz_3991_);
if (v___x_3996_ == 0)
{
lean_object* v___x_3997_; 
lean_dec(v___x_3989_);
v___x_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3997_, 0, v_b_3993_);
return v___x_3997_;
}
else
{
lean_object* v_fst_3998_; lean_object* v_snd_3999_; lean_object* v_a_4000_; lean_object* v___x_4001_; 
v_fst_3998_ = lean_ctor_get(v_b_3993_, 0);
lean_inc(v_fst_3998_);
v_snd_3999_ = lean_ctor_get(v_b_3993_, 1);
lean_inc(v_snd_3999_);
lean_dec_ref(v_b_3993_);
v_a_4000_ = lean_array_uget_borrowed(v_as_3990_, v_i_3992_);
lean_inc(v___x_3989_);
lean_inc(v_a_4000_);
v___x_4001_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_fst_3998_, v_a_4000_, v___x_3989_, v___y_3994_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v_fst_4003_; lean_object* v_snd_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4015_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref(v___x_4001_);
v_fst_4003_ = lean_ctor_get(v_a_4002_, 0);
v_snd_4004_ = lean_ctor_get(v_a_4002_, 1);
v_isSharedCheck_4015_ = !lean_is_exclusive(v_a_4002_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4006_ = v_a_4002_;
v_isShared_4007_ = v_isSharedCheck_4015_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_snd_4004_);
lean_inc(v_fst_4003_);
lean_dec(v_a_4002_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4015_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; lean_object* v___x_4010_; 
v___x_4008_ = lean_array_push(v_snd_3999_, v_fst_4003_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 1, v___x_4008_);
lean_ctor_set(v___x_4006_, 0, v_snd_4004_);
v___x_4010_ = v___x_4006_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_snd_4004_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v___x_4008_);
v___x_4010_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
size_t v___x_4011_; size_t v___x_4012_; 
v___x_4011_ = ((size_t)1ULL);
v___x_4012_ = lean_usize_add(v_i_3992_, v___x_4011_);
v_i_3992_ = v___x_4012_;
v_b_3993_ = v___x_4010_;
goto _start;
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v_snd_3999_);
lean_dec(v___x_3989_);
v_a_4016_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4001_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4001_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1___boxed(lean_object* v___x_4024_, lean_object* v_as_4025_, lean_object* v_sz_4026_, lean_object* v_i_4027_, lean_object* v_b_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
size_t v_sz_boxed_4031_; size_t v_i_boxed_4032_; lean_object* v_res_4033_; 
v_sz_boxed_4031_ = lean_unbox_usize(v_sz_4026_);
lean_dec(v_sz_4026_);
v_i_boxed_4032_ = lean_unbox_usize(v_i_4027_);
lean_dec(v_i_4027_);
v_res_4033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___x_4024_, v_as_4025_, v_sz_boxed_4031_, v_i_boxed_4032_, v_b_4028_, v___y_4029_);
lean_dec_ref(v___y_4029_);
lean_dec_ref(v_as_4025_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___boxed(lean_object* v_requestNo_4034_, lean_object* v_item_4035_, lean_object* v_visited_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_requestNo_4034_, v_item_4035_, v_visited_4036_, v_a_4037_);
lean_dec_ref(v_a_4037_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(lean_object* v_requestNo_4040_, lean_object* v_uri_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
lean_inc(v_requestNo_4040_);
v___x_4044_ = l_Lean_JsonNumber_fromNat(v_requestNo_4040_);
v___x_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
v___x_4046_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_4045_);
v___x_4047_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4045_);
lean_ctor_set(v___x_4047_, 1, v___x_4046_);
lean_ctor_set(v___x_4047_, 2, v_uri_4041_);
v___x_4048_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_4047_, v_a_4042_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v___x_4049_; 
lean_dec_ref(v___x_4048_);
v___x_4049_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_4045_, v_a_4042_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4108_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4108_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4108_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v_result_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4106_; 
v_result_4054_ = lean_ctor_get(v_a_4050_, 1);
v_isSharedCheck_4106_ = !lean_is_exclusive(v_a_4050_);
if (v_isSharedCheck_4106_ == 0)
{
lean_object* v_unused_4107_; 
v_unused_4107_ = lean_ctor_get(v_a_4050_, 0);
lean_dec(v_unused_4107_);
v___x_4056_ = v_a_4050_;
v_isShared_4057_ = v_isSharedCheck_4106_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_result_4054_);
lean_dec(v_a_4050_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4106_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4058_ = lean_unsigned_to_nat(1u);
v___x_4059_ = lean_nat_add(v_requestNo_4040_, v___x_4058_);
lean_dec(v_requestNo_4040_);
if (lean_obj_tag(v_result_4054_) == 1)
{
lean_object* v_val_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4098_; 
lean_del_object(v___x_4052_);
v_val_4060_ = lean_ctor_get(v_result_4054_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v_result_4054_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4062_ = v_result_4054_;
v_isShared_4063_ = v_isSharedCheck_4098_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_val_4060_);
lean_dec(v_result_4054_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4098_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4064_; lean_object* v___x_4066_; 
v___x_4064_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 1, v___x_4064_);
lean_ctor_set(v___x_4056_, 0, v_val_4060_);
v___x_4066_ = v___x_4056_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_val_4060_);
lean_ctor_set(v_reuseFailAlloc_4097_, 1, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4067_ = lean_box(1);
v___x_4068_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v___x_4059_, v___x_4066_, v___x_4067_, v_a_4042_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4088_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4071_ = v___x_4068_;
v_isShared_4072_ = v_isSharedCheck_4088_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4068_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4088_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v_fst_4073_; lean_object* v_snd_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4087_; 
v_fst_4073_ = lean_ctor_get(v_a_4069_, 0);
v_snd_4074_ = lean_ctor_get(v_a_4069_, 1);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_a_4069_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4076_ = v_a_4069_;
v_isShared_4077_ = v_isSharedCheck_4087_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_snd_4074_);
lean_inc(v_fst_4073_);
lean_dec(v_a_4069_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4087_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4063_ == 0)
{
lean_ctor_set(v___x_4062_, 0, v_fst_4073_);
v___x_4079_ = v___x_4062_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_fst_4073_);
v___x_4079_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
lean_object* v___x_4081_; 
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v___x_4079_);
v___x_4081_ = v___x_4076_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4079_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_snd_4074_);
v___x_4081_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
lean_object* v___x_4083_; 
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 0, v___x_4081_);
v___x_4083_ = v___x_4071_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4081_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_del_object(v___x_4062_);
v_a_4089_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4068_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4068_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
}
}
else
{
lean_object* v___x_4099_; lean_object* v___x_4101_; 
lean_dec(v_result_4054_);
v___x_4099_ = lean_box(0);
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 1, v___x_4059_);
lean_ctor_set(v___x_4056_, 0, v___x_4099_);
v___x_4101_ = v___x_4056_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4099_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v___x_4059_);
v___x_4101_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
lean_object* v___x_4103_; 
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4101_);
v___x_4103_ = v___x_4052_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___x_4101_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
}
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
lean_dec(v_requestNo_4040_);
v_a_4109_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4049_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4049_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec_ref(v___x_4045_);
lean_dec(v_requestNo_4040_);
v_a_4117_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4048_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4048_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy___boxed(lean_object* v_requestNo_4125_, lean_object* v_uri_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(v_requestNo_4125_, v_uri_4126_, v_a_4127_);
lean_dec_ref(v_a_4127_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object* v_lean_4132_, lean_object* v_args_4133_, lean_object* v_test_4134_){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; uint8_t v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4136_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_4137_ = lean_box(0);
v___x_4138_ = ((lean_object*)(l_Lean_Lsp_Ipc_runWith___redArg___closed__0));
v___x_4139_ = 1;
v___x_4140_ = 0;
v___x_4141_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4141_, 0, v___x_4136_);
lean_ctor_set(v___x_4141_, 1, v_lean_4132_);
lean_ctor_set(v___x_4141_, 2, v_args_4133_);
lean_ctor_set(v___x_4141_, 3, v___x_4137_);
lean_ctor_set(v___x_4141_, 4, v___x_4138_);
lean_ctor_set_uint8(v___x_4141_, sizeof(void*)*5, v___x_4139_);
lean_ctor_set_uint8(v___x_4141_, sizeof(void*)*5 + 1, v___x_4140_);
v___x_4142_ = lean_io_process_spawn(v___x_4141_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4144_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref(v___x_4142_);
v___x_4144_ = lean_apply_2(v_test_4134_, v_a_4143_, lean_box(0));
return v___x_4144_;
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec_ref(v_test_4134_);
v_a_4145_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4142_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4142_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg___boxed(lean_object* v_lean_4153_, lean_object* v_args_4154_, lean_object* v_test_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4153_, v_args_4154_, v_test_4155_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object* v_00_u03b1_4158_, lean_object* v_lean_4159_, lean_object* v_args_4160_, lean_object* v_test_4161_){
_start:
{
lean_object* v___x_4163_; 
v___x_4163_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4159_, v_args_4160_, v_test_4161_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___boxed(lean_object* v_00_u03b1_4164_, lean_object* v_lean_4165_, lean_object* v_args_4166_, lean_object* v_test_4167_, lean_object* v_a_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Lean_Lsp_Ipc_runWith(v_00_u03b1_4164_, v_lean_4165_, v_args_4166_, v_test_4167_);
return v_res_4169_;
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
