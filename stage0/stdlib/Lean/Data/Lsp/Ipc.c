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
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_Lean_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyOutgoingCallsParams_toJson(lean_object*);
lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object*);
lean_object* l_Lean_IO_FS_Stream_readLspMessage(lean_object*);
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
lean_object* l_Lean_Lsp_instToJsonCallHierarchyIncomingCallsParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyPrepareParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonLeanModule_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Lsp_instToJsonLeanImport_toJson(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Json_isNull(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCallHierarchyIncomingCall_fromJson(lean_object*);
lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyItem_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object*);
uint8_t l_Lean_Lsp_instOrdRange_ord(lean_object*, lean_object*);
lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mergeSort___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "exit"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Data.Lsp.Ipc"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Lsp.Ipc.shutdown"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: result.isNull\n      "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Expected id "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", got id "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_shutdown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "shutdown"};
static const lean_object* l_Lean_Lsp_Ipc_shutdown___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_shutdown___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_collectDiagnostics___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "textDocument/waitForDiagnostics"};
static const lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_collectDiagnostics___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Waiting for ILeans failed: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_waitForILeans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "$/lean/waitForILeans"};
static const lean_object* l_Lean_Lsp_Ipc_waitForILeans___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_waitForILeans___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(lean_object*);
static const lean_array_object l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonCallHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "textDocument/prepareCallHierarchy"};
static const lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0_value;
static const lean_array_object l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy = (const lean_object*)&l_Lean_Lsp_Ipc_instToJsonModuleHierarchy___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "$/lean/prepareModuleHierarchy"};
static const lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 2, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1 = (const lean_object*)&l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Lsp_Ipc_stdin(lean_object* v_a_5_){
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
LEAN_EXPORT void l_Lean_Lsp_Ipc_stdin_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5_ = stack[0].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_Lsp_Ipc_stdin(v_a_5_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin___boxed(lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_Lsp_Ipc_stdin(v_a_11_);
lean_dec_ref(v_a_11_);
return v_res_13_;
}
}
lean_object* l_Lean_Lsp_Ipc_stdout(lean_object* v_a_14_){
_start:
{
lean_object* v_stdout_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_stdout_16_ = lean_ctor_get(v_a_14_, 1);
lean_inc(v_stdout_16_);
v___x_17_ = lean_stream_of_handle(v_stdout_16_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_stdout_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_14_ = stack[0].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_Lsp_Ipc_stdout(v_a_14_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout___boxed(lean_object* v_a_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Lsp_Ipc_stdout(v_a_20_);
lean_dec_ref(v_a_20_);
return v_res_22_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg(lean_object* v_inst_23_, lean_object* v_r_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_27_; lean_object* v_a_28_; lean_object* v___x_29_; 
v___x_27_ = l_Lean_Lsp_Ipc_stdin(v_a_25_);
v_a_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_a_28_);
lean_dec_ref(v___x_27_);
v___x_29_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_23_, v_a_28_, v_r_24_);
return v___x_29_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeRequest___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_23_ = stack[0].m_obj;
lean_object* v_r_24_ = stack[1].m_obj;
lean_object* v_a_25_ = stack[2].m_obj;
lean_object* v_res_30_;
v_res_30_ = l_Lean_Lsp_Ipc_writeRequest___redArg(v_inst_23_, v_r_24_, v_a_25_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg___boxed(lean_object* v_inst_31_, lean_object* v_r_32_, lean_object* v_a_33_, lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Lsp_Ipc_writeRequest___redArg(v_inst_31_, v_r_32_, v_a_33_);
lean_dec_ref(v_a_33_);
return v_res_35_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object* v_00_u03b1_36_, lean_object* v_inst_37_, lean_object* v_r_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Lsp_Ipc_writeRequest___redArg(v_inst_37_, v_r_38_, v_a_39_);
return v___x_41_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_37_ = stack[1].m_obj;
lean_object* v_r_38_ = stack[2].m_obj;
lean_object* v_a_39_ = stack[3].m_obj;
lean_object* v_res_42_;
v_res_42_ = l_Lean_Lsp_Ipc_writeRequest(lean_box(0), v_inst_37_, v_r_38_, v_a_39_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___boxed(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_r_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Lsp_Ipc_writeRequest(v_00_u03b1_43_, v_inst_44_, v_r_45_, v_a_46_);
lean_dec_ref(v_a_46_);
return v_res_48_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg(lean_object* v_inst_49_, lean_object* v_n_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_53_; lean_object* v_a_54_; lean_object* v___x_55_; 
v___x_53_ = l_Lean_Lsp_Ipc_stdin(v_a_51_);
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
lean_dec_ref(v___x_53_);
v___x_55_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_49_, v_a_54_, v_n_50_);
return v___x_55_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeNotification___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_49_ = stack[0].m_obj;
lean_object* v_n_50_ = stack[1].m_obj;
lean_object* v_a_51_ = stack[2].m_obj;
lean_object* v_res_56_;
v_res_56_ = l_Lean_Lsp_Ipc_writeNotification___redArg(v_inst_49_, v_n_50_, v_a_51_);
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg___boxed(lean_object* v_inst_57_, lean_object* v_n_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Lsp_Ipc_writeNotification___redArg(v_inst_57_, v_n_58_, v_a_59_);
lean_dec_ref(v_a_59_);
return v_res_61_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object* v_00_u03b1_62_, lean_object* v_inst_63_, lean_object* v_n_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Lsp_Ipc_writeNotification___redArg(v_inst_63_, v_n_64_, v_a_65_);
return v___x_67_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeNotification_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_63_ = stack[1].m_obj;
lean_object* v_n_64_ = stack[2].m_obj;
lean_object* v_a_65_ = stack[3].m_obj;
lean_object* v_res_68_;
v_res_68_ = l_Lean_Lsp_Ipc_writeNotification(lean_box(0), v_inst_63_, v_n_64_, v_a_65_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___boxed(lean_object* v_00_u03b1_69_, lean_object* v_inst_70_, lean_object* v_n_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Lsp_Ipc_writeNotification(v_00_u03b1_69_, v_inst_70_, v_n_71_, v_a_72_);
lean_dec_ref(v_a_72_);
return v_res_74_;
}
}
static lean_object* _init_l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = l_instInhabitedError;
v___x_76_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_76_, 0, lean_box(0));
lean_closure_set(v___x_76_, 1, lean_box(0));
lean_closure_set(v___x_76_, 2, v___x_75_);
return v___x_76_;
}
}
lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(lean_object* v_msg_77_, lean_object* v___y_78_){
_start:
{
lean_object* v___x_80_; lean_object* v___f_81_; lean_object* v___x_3064__overap_82_; lean_object* v___x_83_; 
v___x_80_ = lean_obj_once(&l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0, &l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0_once, _init_l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0);
v___f_81_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_81_, 0, v___x_80_);
v___x_3064__overap_82_ = lean_panic_fn_borrowed(v___f_81_, v_msg_77_);
lean_dec_ref(v___f_81_);
lean_inc_ref(v___y_78_);
v___x_83_ = lean_apply_2(v___x_3064__overap_82_, v___y_78_, lean_box(0));
return v___x_83_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_77_ = stack[0].m_obj;
lean_object* v___y_78_ = stack[1].m_obj;
lean_object* v_res_84_;
v_res_84_ = l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(v_msg_77_, v___y_78_);
stack->m_obj
 = v_res_84_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___boxed(lean_object* v_msg_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(v_msg_85_, v___y_86_);
lean_dec_ref(v___y_86_);
return v_res_88_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(lean_object* v_h_89_, lean_object* v_n_90_){
_start:
{
lean_object* v_method_92_; lean_object* v_param_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_113_; 
v_method_92_ = lean_ctor_get(v_n_90_, 0);
v_param_93_ = lean_ctor_get(v_n_90_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_n_90_);
if (v_isSharedCheck_113_ == 0)
{
v___x_95_ = v_n_90_;
v_isShared_96_ = v_isSharedCheck_113_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_param_93_);
lean_inc(v_method_92_);
lean_dec(v_n_90_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_113_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___y_98_; lean_object* v___x_103_; 
v___x_103_ = l_Lean_Json_Structured_fromJson_x3f(v_param_93_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v___x_104_; 
lean_dec_ref_known(v___x_103_, 1);
v___x_104_ = lean_box(0);
v___y_98_ = v___x_104_;
goto v___jp_97_;
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
v_a_105_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_103_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_103_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
v___y_98_ = v___x_110_;
goto v___jp_97_;
}
}
}
v___jp_97_:
{
lean_object* v___x_100_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set_tag(v___x_95_, 1);
lean_ctor_set(v___x_95_, 1, v___y_98_);
v___x_100_ = v___x_95_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_method_92_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___y_98_);
v___x_100_ = v_reuseFailAlloc_102_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_89_, v___x_100_);
return v___x_101_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_89_ = stack[0].m_obj;
lean_object* v_n_90_ = stack[1].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(v_h_89_, v_n_90_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1___boxed(lean_object* v_h_115_, lean_object* v_n_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(v_h_115_, v_n_116_);
return v_res_118_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_126_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4));
v___x_127_ = lean_unsigned_to_nat(6u);
v___x_128_ = lean_unsigned_to_nat(57u);
v___x_129_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3));
v___x_130_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2));
v___x_131_ = l_mkPanicMessageWithDecl(v___x_130_, v___x_129_, v___x_128_, v___x_127_, v___x_126_);
return v___x_131_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v___x_138_, lean_object* v_requestNo_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_box(0);
lean_inc_ref(v_a_136_);
v___x_143_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_136_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_203_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_203_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_203_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_203_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
if (lean_obj_tag(v_a_144_) == 2)
{
lean_object* v_id_159_; lean_object* v_result_160_; uint8_t v___x_161_; 
v_id_159_ = lean_ctor_get(v_a_144_, 0);
lean_inc(v_id_159_);
v_result_160_ = lean_ctor_get(v_a_144_, 1);
lean_inc(v_result_160_);
lean_dec_ref_known(v_a_144_, 2);
v___x_161_ = l_Lean_Json_isNull(v_result_160_);
lean_dec(v_result_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_id_159_);
lean_del_object(v___x_146_);
v___x_162_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5, &l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5);
v___x_163_ = l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2(v___x_162_, v___y_140_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_173_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_173_ == 0)
{
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_173_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_173_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
if (lean_obj_tag(v_a_164_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; 
lean_dec(v_requestNo_139_);
lean_dec_ref(v_a_137_);
lean_dec_ref(v_a_136_);
v_a_168_ = lean_ctor_get(v_a_164_, 0);
lean_inc(v_a_168_);
lean_dec_ref_known(v_a_164_, 1);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v_a_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
else
{
lean_dec_ref_known(v_a_164_, 1);
lean_del_object(v___x_166_);
goto _start;
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec(v_requestNo_139_);
lean_dec_ref(v_a_137_);
lean_dec_ref(v_a_136_);
v_a_174_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_163_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_163_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
else
{
uint8_t v___x_182_; 
lean_dec_ref(v_a_136_);
v___x_182_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_159_, v___x_138_);
if (v___x_182_ == 0)
{
if (v___x_161_ == 0)
{
lean_dec(v_id_159_);
lean_del_object(v___x_146_);
lean_dec(v_requestNo_139_);
goto v___jp_148_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___y_189_; 
lean_dec_ref(v_a_137_);
v___x_183_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_184_ = l_Nat_reprFast(v_requestNo_139_);
v___x_185_ = lean_string_append(v___x_183_, v___x_184_);
lean_dec_ref(v___x_184_);
v___x_186_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_187_ = lean_string_append(v___x_185_, v___x_186_);
switch(lean_obj_tag(v_id_159_))
{
case 0:
{
lean_object* v_s_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_s_195_ = lean_ctor_get(v_id_159_, 0);
lean_inc_ref(v_s_195_);
lean_dec_ref_known(v_id_159_, 1);
v___x_196_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_197_ = lean_string_append(v___x_196_, v_s_195_);
lean_dec_ref(v_s_195_);
v___x_198_ = lean_string_append(v___x_197_, v___x_196_);
v___y_189_ = v___x_198_;
goto v___jp_188_;
}
case 1:
{
lean_object* v_n_199_; lean_object* v___x_200_; 
v_n_199_ = lean_ctor_get(v_id_159_, 0);
lean_inc_ref(v_n_199_);
lean_dec_ref_known(v_id_159_, 1);
v___x_200_ = l_Lean_JsonNumber_toString(v_n_199_);
v___y_189_ = v___x_200_;
goto v___jp_188_;
}
default: 
{
lean_object* v___x_201_; 
v___x_201_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_189_ = v___x_201_;
goto v___jp_188_;
}
}
v___jp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_string_append(v___x_187_, v___y_189_);
lean_dec_ref(v___y_189_);
v___x_191_ = lean_mk_io_user_error(v___x_190_);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 1);
lean_ctor_set(v___x_146_, 0, v___x_191_);
v___x_193_ = v___x_146_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_dec(v_id_159_);
lean_del_object(v___x_146_);
lean_dec(v_requestNo_139_);
goto v___jp_148_;
}
}
}
else
{
lean_del_object(v___x_146_);
lean_dec(v_a_144_);
goto _start;
}
v___jp_148_:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1));
v___x_150_ = l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(v_a_137_, v___x_149_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v___x_150_, 0);
lean_dec(v_unused_158_);
v___x_152_ = v___x_150_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_dec(v___x_150_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_142_);
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_142_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
else
{
return v___x_150_;
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec(v_requestNo_139_);
lean_dec_ref(v_a_137_);
lean_dec_ref(v_a_136_);
v_a_204_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_143_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_143_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_136_ = stack[0].m_obj;
lean_object* v_a_137_ = stack[1].m_obj;
lean_object* v___x_138_ = stack[2].m_obj;
lean_object* v_requestNo_139_ = stack[3].m_obj;
lean_object* v___y_140_ = stack[4].m_obj;
lean_object* v_res_212_;
v_res_212_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_136_, v_a_137_, v___x_138_, v_requestNo_139_, v___y_140_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___boxed(lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v___x_215_, lean_object* v_requestNo_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_213_, v_a_214_, v___x_215_, v_requestNo_216_, v___y_217_);
lean_dec_ref(v___y_217_);
lean_dec(v___x_215_);
return v_res_219_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(lean_object* v_h_220_, lean_object* v_r_221_){
_start:
{
lean_object* v_id_223_; lean_object* v_method_224_; lean_object* v_param_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_245_; 
v_id_223_ = lean_ctor_get(v_r_221_, 0);
v_method_224_ = lean_ctor_get(v_r_221_, 1);
v_param_225_ = lean_ctor_get(v_r_221_, 2);
v_isSharedCheck_245_ = !lean_is_exclusive(v_r_221_);
if (v_isSharedCheck_245_ == 0)
{
v___x_227_ = v_r_221_;
v_isShared_228_ = v_isSharedCheck_245_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_param_225_);
lean_inc(v_method_224_);
lean_inc(v_id_223_);
lean_dec(v_r_221_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_245_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___y_230_; lean_object* v___x_235_; 
v___x_235_ = l_Lean_Json_Structured_fromJson_x3f(v_param_225_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v___x_236_; 
lean_dec_ref_known(v___x_235_, 1);
v___x_236_ = lean_box(0);
v___y_230_ = v___x_236_;
goto v___jp_229_;
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_a_237_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_235_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
v___y_230_ = v___x_242_;
goto v___jp_229_;
}
}
}
v___jp_229_:
{
lean_object* v___x_232_; 
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 2, v___y_230_);
v___x_232_ = v___x_227_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_id_223_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_method_224_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v___y_230_);
v___x_232_ = v_reuseFailAlloc_234_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_220_, v___x_232_);
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_220_ = stack[0].m_obj;
lean_object* v_r_221_ = stack[1].m_obj;
lean_object* v_res_246_;
v_res_246_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(v_h_220_, v_r_221_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0___boxed(lean_object* v_h_247_, lean_object* v_r_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(v_h_247_, v_r_248_);
return v_res_250_;
}
}
lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object* v_requestNo_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_255_; lean_object* v_a_256_; lean_object* v___x_257_; lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_280_; 
v___x_255_ = l_Lean_Lsp_Ipc_stdout(v_a_253_);
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref(v___x_255_);
v___x_257_ = l_Lean_Lsp_Ipc_stdin(v_a_253_);
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_280_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_280_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_280_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
lean_inc(v_requestNo_252_);
v___x_262_ = l_Lean_JsonNumber_fromNat(v_requestNo_252_);
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 1);
lean_ctor_set(v___x_260_, 0, v___x_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_279_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = ((lean_object*)(l_Lean_Lsp_Ipc_shutdown___closed__0));
v___x_266_ = lean_box(0);
lean_inc_ref(v___x_264_);
v___x_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_264_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
lean_inc(v_a_258_);
v___x_268_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(v_a_258_, v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec_ref_known(v___x_268_, 1);
v___x_269_ = lean_box(0);
v___x_270_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_256_, v_a_258_, v___x_264_, v_requestNo_252_, v_a_253_);
lean_dec_ref(v___x_264_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v___x_270_, 0);
lean_dec(v_unused_278_);
v___x_272_ = v___x_270_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_dec(v___x_270_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_269_);
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_269_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
return v___x_270_;
}
}
else
{
lean_dec_ref(v___x_264_);
lean_dec(v_a_258_);
lean_dec(v_a_256_);
lean_dec(v_requestNo_252_);
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_shutdown_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestNo_252_ = stack[0].m_obj;
lean_object* v_a_253_ = stack[1].m_obj;
lean_object* v_res_281_;
v_res_281_ = l_Lean_Lsp_Ipc_shutdown(v_requestNo_252_, v_a_253_);
stack->m_obj
 = v_res_281_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown___boxed(lean_object* v_requestNo_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Lsp_Ipc_shutdown(v_requestNo_282_, v_a_283_);
lean_dec_ref(v_a_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object* v_v_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Json_Structured_fromJson_x3f(v_v_286_);
return v___x_287_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v___x_290_, lean_object* v_requestNo_291_, lean_object* v_inst_292_, lean_object* v_a_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_288_, v_a_289_, v___x_290_, v_requestNo_291_, v___y_294_);
return v___x_296_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_288_ = stack[0].m_obj;
lean_object* v_a_289_ = stack[1].m_obj;
lean_object* v___x_290_ = stack[2].m_obj;
lean_object* v_requestNo_291_ = stack[3].m_obj;
lean_object* v_a_293_ = stack[5].m_obj;
lean_object* v___y_294_ = stack[6].m_obj;
lean_object* v_res_297_;
v_res_297_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(v_a_288_, v_a_289_, v___x_290_, v_requestNo_291_, lean_box(0), v_a_293_, v___y_294_);
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___boxed(lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v___x_300_, lean_object* v_requestNo_301_, lean_object* v_inst_302_, lean_object* v_a_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(v_a_298_, v_a_299_, v___x_300_, v_requestNo_301_, v_inst_302_, v_a_303_, v___y_304_);
lean_dec_ref(v___y_304_);
lean_dec(v___x_300_);
return v_res_306_;
}
}
lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object* v_a_307_){
_start:
{
lean_object* v___x_309_; lean_object* v_a_310_; lean_object* v___x_311_; 
v___x_309_ = l_Lean_Lsp_Ipc_stdout(v_a_307_);
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref(v___x_309_);
v___x_311_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_310_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_readMessage_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_307_ = stack[0].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_Lsp_Ipc_readMessage(v_a_307_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage___boxed(lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Lsp_Ipc_readMessage(v_a_313_);
lean_dec_ref(v_a_313_);
return v_res_315_;
}
}
lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg(lean_object* v_expectedMethod_316_, lean_object* v_inst_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; lean_object* v_a_321_; lean_object* v___x_322_; 
v___x_320_ = l_Lean_Lsp_Ipc_stdout(v_a_318_);
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref(v___x_320_);
v___x_322_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_a_321_, v_expectedMethod_316_, v_inst_317_);
return v___x_322_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_readRequestAs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedMethod_316_ = stack[0].m_obj;
lean_object* v_inst_317_ = stack[1].m_obj;
lean_object* v_a_318_ = stack[2].m_obj;
lean_object* v_res_323_;
v_res_323_ = l_Lean_Lsp_Ipc_readRequestAs___redArg(v_expectedMethod_316_, v_inst_317_, v_a_318_);
stack->m_obj
 = v_res_323_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg___boxed(lean_object* v_expectedMethod_324_, lean_object* v_inst_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Lsp_Ipc_readRequestAs___redArg(v_expectedMethod_324_, v_inst_325_, v_a_326_);
lean_dec_ref(v_a_326_);
return v_res_328_;
}
}
lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object* v_expectedMethod_329_, lean_object* v_00_u03b1_330_, lean_object* v_inst_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Lsp_Ipc_readRequestAs___redArg(v_expectedMethod_329_, v_inst_331_, v_a_332_);
return v___x_334_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_readRequestAs_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedMethod_329_ = stack[0].m_obj;
lean_object* v_inst_331_ = stack[2].m_obj;
lean_object* v_a_332_ = stack[3].m_obj;
lean_object* v_res_335_;
v_res_335_ = l_Lean_Lsp_Ipc_readRequestAs(v_expectedMethod_329_, lean_box(0), v_inst_331_, v_a_332_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___boxed(lean_object* v_expectedMethod_336_, lean_object* v_00_u03b1_337_, lean_object* v_inst_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Lsp_Ipc_readRequestAs(v_expectedMethod_336_, v_00_u03b1_337_, v_inst_338_, v_a_339_);
lean_dec_ref(v_a_339_);
return v_res_341_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(32700u);
v___x_360_ = lean_nat_to_int(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14);
v___x_362_ = lean_int_neg(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15);
v___x_364_ = l_Lean_JsonNumber_fromInt(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16);
v___x_366_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(32600u);
v___x_368_ = lean_nat_to_int(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18);
v___x_370_ = lean_int_neg(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19);
v___x_372_ = l_Lean_JsonNumber_fromInt(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20);
v___x_374_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(32601u);
v___x_376_ = lean_nat_to_int(v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22);
v___x_378_ = lean_int_neg(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23);
v___x_380_ = l_Lean_JsonNumber_fromInt(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24);
v___x_382_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(32602u);
v___x_384_ = lean_nat_to_int(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26);
v___x_386_ = lean_int_neg(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27);
v___x_388_ = l_Lean_JsonNumber_fromInt(v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28);
v___x_390_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(32603u);
v___x_392_ = lean_nat_to_int(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30);
v___x_394_ = lean_int_neg(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31);
v___x_396_ = l_Lean_JsonNumber_fromInt(v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32);
v___x_398_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_unsigned_to_nat(32002u);
v___x_400_ = lean_nat_to_int(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34);
v___x_402_ = lean_int_neg(v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35);
v___x_404_ = l_Lean_JsonNumber_fromInt(v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36);
v___x_406_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(32001u);
v___x_408_ = lean_nat_to_int(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38);
v___x_410_ = lean_int_neg(v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39);
v___x_412_ = l_Lean_JsonNumber_fromInt(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40);
v___x_414_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(32801u);
v___x_416_ = lean_nat_to_int(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42);
v___x_418_ = lean_int_neg(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43);
v___x_420_ = l_Lean_JsonNumber_fromInt(v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44);
v___x_422_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_unsigned_to_nat(32800u);
v___x_424_ = lean_nat_to_int(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46);
v___x_426_ = lean_int_neg(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47);
v___x_428_ = l_Lean_JsonNumber_fromInt(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48);
v___x_430_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_unsigned_to_nat(32900u);
v___x_432_ = lean_nat_to_int(v___x_431_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50);
v___x_434_ = lean_int_neg(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51);
v___x_436_ = l_Lean_JsonNumber_fromInt(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52);
v___x_438_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_unsigned_to_nat(32901u);
v___x_440_ = lean_nat_to_int(v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54);
v___x_442_ = lean_int_neg(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55);
v___x_444_ = l_Lean_JsonNumber_fromInt(v___x_443_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56);
v___x_446_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_unsigned_to_nat(32902u);
v___x_448_ = lean_nat_to_int(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58);
v___x_450_ = lean_int_neg(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59);
v___x_452_ = l_Lean_JsonNumber_fromInt(v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60);
v___x_454_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg(lean_object* v_expectedID_455_, lean_object* v_inst_456_, lean_object* v_a_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Lsp_Ipc_stdout(v_a_457_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_604_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_604_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_604_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_604_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_460_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_595_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_595_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_595_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_595_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___y_470_; lean_object* v___y_471_; 
switch(lean_obj_tag(v_a_465_))
{
case 2:
{
lean_object* v_id_477_; lean_object* v_result_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_522_; 
v_id_477_ = lean_ctor_get(v_a_465_, 0);
v_result_478_ = lean_ctor_get(v_a_465_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_a_465_);
if (v_isSharedCheck_522_ == 0)
{
v___x_480_ = v_a_465_;
v_isShared_481_ = v_isSharedCheck_522_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_result_478_);
lean_inc(v_id_477_);
lean_dec(v_a_465_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_522_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint8_t v___x_482_; 
v___x_482_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_477_, v_expectedID_455_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___y_485_; 
lean_del_object(v___x_480_);
lean_dec(v_result_478_);
lean_del_object(v___x_462_);
lean_dec_ref(v_inst_456_);
v___x_483_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_455_))
{
case 0:
{
lean_object* v_s_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_s_496_ = lean_ctor_get(v_expectedID_455_, 0);
lean_inc_ref(v_s_496_);
lean_dec_ref_known(v_expectedID_455_, 1);
v___x_497_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_498_ = lean_string_append(v___x_497_, v_s_496_);
lean_dec_ref(v_s_496_);
v___x_499_ = lean_string_append(v___x_498_, v___x_497_);
v___y_485_ = v___x_499_;
goto v___jp_484_;
}
case 1:
{
lean_object* v_n_500_; lean_object* v___x_501_; 
v_n_500_ = lean_ctor_get(v_expectedID_455_, 0);
lean_inc_ref(v_n_500_);
lean_dec_ref_known(v_expectedID_455_, 1);
v___x_501_ = l_Lean_JsonNumber_toString(v_n_500_);
v___y_485_ = v___x_501_;
goto v___jp_484_;
}
default: 
{
lean_object* v___x_502_; 
v___x_502_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_485_ = v___x_502_;
goto v___jp_484_;
}
}
v___jp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_string_append(v___x_483_, v___y_485_);
lean_dec_ref(v___y_485_);
v___x_487_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
switch(lean_obj_tag(v_id_477_))
{
case 0:
{
lean_object* v_s_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_s_489_ = lean_ctor_get(v_id_477_, 0);
lean_inc_ref(v_s_489_);
lean_dec_ref_known(v_id_477_, 1);
v___x_490_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_491_ = lean_string_append(v___x_490_, v_s_489_);
lean_dec_ref(v_s_489_);
v___x_492_ = lean_string_append(v___x_491_, v___x_490_);
v___y_470_ = v___x_488_;
v___y_471_ = v___x_492_;
goto v___jp_469_;
}
case 1:
{
lean_object* v_n_493_; lean_object* v___x_494_; 
v_n_493_ = lean_ctor_get(v_id_477_, 0);
lean_inc_ref(v_n_493_);
lean_dec_ref_known(v_id_477_, 1);
v___x_494_ = l_Lean_JsonNumber_toString(v_n_493_);
v___y_470_ = v___x_488_;
v___y_471_ = v___x_494_;
goto v___jp_469_;
}
default: 
{
lean_object* v___x_495_; 
v___x_495_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_470_ = v___x_488_;
v___y_471_ = v___x_495_;
goto v___jp_469_;
}
}
}
}
else
{
lean_object* v___x_503_; 
lean_dec(v_id_477_);
lean_del_object(v___x_467_);
lean_inc(v_result_478_);
v___x_503_ = lean_apply_1(v_inst_456_, v_result_478_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
lean_del_object(v___x_480_);
lean_dec(v_expectedID_455_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_506_ = l_Lean_Json_compress(v_result_478_);
v___x_507_ = lean_string_append(v___x_505_, v___x_506_);
lean_dec_ref(v___x_506_);
v___x_508_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_509_ = lean_string_append(v___x_507_, v___x_508_);
v___x_510_ = lean_string_append(v___x_509_, v_a_504_);
lean_dec(v_a_504_);
v___x_511_ = lean_mk_io_user_error(v___x_510_);
if (v_isShared_463_ == 0)
{
lean_ctor_set_tag(v___x_462_, 1);
lean_ctor_set(v___x_462_, 0, v___x_511_);
v___x_513_ = v___x_462_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; 
lean_dec(v_result_478_);
v_a_515_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_515_);
lean_dec_ref_known(v___x_503_, 1);
if (v_isShared_481_ == 0)
{
lean_ctor_set_tag(v___x_480_, 0);
lean_ctor_set(v___x_480_, 1, v_a_515_);
lean_ctor_set(v___x_480_, 0, v_expectedID_455_);
v___x_517_ = v___x_480_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_expectedID_455_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_a_515_);
v___x_517_ = v_reuseFailAlloc_521_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_517_);
v___x_519_ = v___x_462_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_523_; uint8_t v_code_524_; lean_object* v_message_525_; lean_object* v_data_x3f_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___x_559_; lean_object* v___y_561_; 
lean_del_object(v___x_467_);
lean_dec_ref(v_inst_456_);
lean_dec(v_expectedID_455_);
v_id_523_ = lean_ctor_get(v_a_465_, 0);
lean_inc(v_id_523_);
v_code_524_ = lean_ctor_get_uint8(v_a_465_, sizeof(void*)*3);
v_message_525_ = lean_ctor_get(v_a_465_, 1);
lean_inc_ref(v_message_525_);
v_data_x3f_526_ = lean_ctor_get(v_a_465_, 2);
lean_inc(v_data_x3f_526_);
lean_dec_ref_known(v_a_465_, 3);
v___x_527_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_528_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3));
v___x_529_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_559_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_523_))
{
case 0:
{
lean_object* v_s_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_s_577_ = lean_ctor_get(v_id_523_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_id_523_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v_id_523_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_s_577_);
lean_dec(v_id_523_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set_tag(v___x_579_, 3);
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_s_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
v___y_561_ = v___x_582_;
goto v___jp_560_;
}
}
}
case 1:
{
lean_object* v_n_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
v_n_585_ = lean_ctor_get(v_id_523_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v_id_523_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v_id_523_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_n_585_);
lean_dec(v_id_523_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set_tag(v___x_587_, 2);
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_n_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
v___y_561_ = v___x_590_;
goto v___jp_560_;
}
}
}
default: 
{
lean_object* v___x_593_; 
v___x_593_ = lean_box(0);
v___y_561_ = v___x_593_;
goto v___jp_560_;
}
}
v___jp_530_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
lean_inc(v___y_534_);
lean_inc_ref(v___y_531_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___y_531_);
lean_ctor_set(v___x_535_, 1, v___y_534_);
v___x_536_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_537_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_537_, 0, v_message_525_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = lean_box(0);
v___x_540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_535_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_543_ = l_Lean_Json_opt___redArg(v___x_528_, v___x_542_, v_data_x3f_526_);
v___x_544_ = l_List_appendTR___redArg(v___x_541_, v___x_543_);
v___x_545_ = l_Lean_Json_mkObj(v___x_544_);
lean_dec(v___x_544_);
lean_inc_ref(v___y_532_);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___y_532_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_539_);
v___x_548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_548_, 0, v___y_533_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_529_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = l_Lean_Json_mkObj(v___x_549_);
lean_dec_ref_known(v___x_549_, 2);
v___x_551_ = l_Lean_Json_compress(v___x_550_);
v___x_552_ = lean_string_append(v___x_527_, v___x_551_);
lean_dec_ref(v___x_551_);
v___x_553_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
v___x_555_ = lean_mk_io_user_error(v___x_554_);
if (v_isShared_463_ == 0)
{
lean_ctor_set_tag(v___x_462_, 1);
lean_ctor_set(v___x_462_, 0, v___x_555_);
v___x_557_ = v___x_462_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
v___jp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_559_);
lean_ctor_set(v___x_562_, 1, v___y_561_);
v___x_563_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_564_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_524_)
{
case 0:
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_565_;
goto v___jp_530_;
}
case 1:
{
lean_object* v___x_566_; 
v___x_566_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_566_;
goto v___jp_530_;
}
case 2:
{
lean_object* v___x_567_; 
v___x_567_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_567_;
goto v___jp_530_;
}
case 3:
{
lean_object* v___x_568_; 
v___x_568_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_568_;
goto v___jp_530_;
}
case 4:
{
lean_object* v___x_569_; 
v___x_569_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_569_;
goto v___jp_530_;
}
case 5:
{
lean_object* v___x_570_; 
v___x_570_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_570_;
goto v___jp_530_;
}
case 6:
{
lean_object* v___x_571_; 
v___x_571_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_571_;
goto v___jp_530_;
}
case 7:
{
lean_object* v___x_572_; 
v___x_572_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_572_;
goto v___jp_530_;
}
case 8:
{
lean_object* v___x_573_; 
v___x_573_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_573_;
goto v___jp_530_;
}
case 9:
{
lean_object* v___x_574_; 
v___x_574_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_574_;
goto v___jp_530_;
}
case 10:
{
lean_object* v___x_575_; 
v___x_575_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_575_;
goto v___jp_530_;
}
default: 
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_531_ = v___x_564_;
v___y_532_ = v___x_563_;
v___y_533_ = v___x_562_;
v___y_534_ = v___x_576_;
goto v___jp_530_;
}
}
}
}
default: 
{
lean_del_object(v___x_467_);
lean_dec(v_a_465_);
lean_del_object(v___x_462_);
goto _start;
}
}
v___jp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = lean_string_append(v___y_470_, v___y_471_);
lean_dec_ref(v___y_471_);
v___x_473_ = lean_mk_io_user_error(v___x_472_);
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 1);
lean_ctor_set(v___x_467_, 0, v___x_473_);
v___x_475_ = v___x_467_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_del_object(v___x_462_);
lean_dec_ref(v_inst_456_);
lean_dec(v_expectedID_455_);
v_a_596_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_464_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_464_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v_inst_456_);
lean_dec(v_expectedID_455_);
v_a_605_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_459_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_459_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_readResponseAs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedID_455_ = stack[0].m_obj;
lean_object* v_inst_456_ = stack[1].m_obj;
lean_object* v_a_457_ = stack[2].m_obj;
lean_object* v_res_613_;
v_res_613_ = l_Lean_Lsp_Ipc_readResponseAs___redArg(v_expectedID_455_, v_inst_456_, v_a_457_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___boxed(lean_object* v_expectedID_614_, lean_object* v_inst_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Lsp_Ipc_readResponseAs___redArg(v_expectedID_614_, v_inst_615_, v_a_616_);
lean_dec_ref(v_a_616_);
return v_res_618_;
}
}
lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object* v_expectedID_619_, lean_object* v_00_u03b1_620_, lean_object* v_inst_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Lsp_Ipc_readResponseAs___redArg(v_expectedID_619_, v_inst_621_, v_a_622_);
return v___x_624_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_readResponseAs_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedID_619_ = stack[0].m_obj;
lean_object* v_inst_621_ = stack[2].m_obj;
lean_object* v_a_622_ = stack[3].m_obj;
lean_object* v_res_625_;
v_res_625_ = l_Lean_Lsp_Ipc_readResponseAs(v_expectedID_619_, lean_box(0), v_inst_621_, v_a_622_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___boxed(lean_object* v_expectedID_626_, lean_object* v_00_u03b1_627_, lean_object* v_inst_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_Lsp_Ipc_readResponseAs(v_expectedID_626_, v_00_u03b1_627_, v_inst_628_, v_a_629_);
lean_dec_ref(v_a_629_);
return v_res_631_;
}
}
lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object* v_a_632_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_635_ = lean_io_process_child_wait(v___x_634_, v_a_632_);
return v___x_635_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_waitForExit_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_632_ = stack[0].m_obj;
lean_object* v_res_636_;
v_res_636_ = l_Lean_Lsp_Ipc_waitForExit(v_a_632_);
stack->m_obj
 = v_res_636_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Lsp_Ipc_waitForExit(v_a_637_);
lean_dec_ref(v_a_637_);
return v_res_639_;
}
}
uint8_t l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(lean_object* v_d1_640_, lean_object* v_d2_641_){
_start:
{
uint8_t v___y_643_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d1_640_);
v___x_647_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d2_641_);
v___x_648_ = l_Lean_Lsp_instOrdRange_ord(v___x_646_, v___x_647_);
lean_dec_ref(v___x_647_);
lean_dec_ref(v___x_646_);
if (v___x_648_ == 1)
{
lean_object* v_message_649_; lean_object* v_message_650_; uint8_t v___x_651_; 
v_message_649_ = lean_ctor_get(v_d1_640_, 6);
v_message_650_ = lean_ctor_get(v_d2_641_, 6);
v___x_651_ = lean_string_compare(v_message_649_, v_message_650_);
v___y_643_ = v___x_651_;
goto v___jp_642_;
}
else
{
v___y_643_ = v___x_648_;
goto v___jp_642_;
}
v___jp_642_:
{
if (v___y_643_ == 2)
{
uint8_t v___x_644_; 
v___x_644_ = 0;
return v___x_644_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = 1;
return v___x_645_;
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_d1_640_ = stack[0].m_obj;
lean_object* v_d2_641_ = stack[1].m_obj;
uint8_t v_res_652_;
v_res_652_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(v_d1_640_, v_d2_641_);
stack->m_num = v_res_652_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed(lean_object* v_d1_653_, lean_object* v_d2_654_){
_start:
{
uint8_t v_res_655_; lean_object* v_r_656_; 
v_res_655_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(v_d1_653_, v_d2_654_);
lean_dec_ref(v_d2_654_);
lean_dec_ref(v_d1_653_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(lean_object* v_p_658_){
_start:
{
lean_object* v_uri_659_; lean_object* v_version_x3f_660_; lean_object* v_isIncremental_x3f_661_; lean_object* v_diagnostics_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_673_; 
v_uri_659_ = lean_ctor_get(v_p_658_, 0);
v_version_x3f_660_ = lean_ctor_get(v_p_658_, 1);
v_isIncremental_x3f_661_ = lean_ctor_get(v_p_658_, 2);
v_diagnostics_662_ = lean_ctor_get(v_p_658_, 3);
v_isSharedCheck_673_ = !lean_is_exclusive(v_p_658_);
if (v_isSharedCheck_673_ == 0)
{
v___x_664_ = v_p_658_;
v_isShared_665_ = v_isSharedCheck_673_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_diagnostics_662_);
lean_inc(v_isIncremental_x3f_661_);
lean_inc(v_version_x3f_660_);
lean_inc(v_uri_659_);
lean_dec(v_p_658_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_673_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___f_666_; lean_object* v___x_667_; lean_object* v_sorted_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___f_666_ = ((lean_object*)(l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0));
v___x_667_ = lean_array_to_list(v_diagnostics_662_);
v_sorted_668_ = l_List_mergeSort___redArg(v___x_667_, v___f_666_);
v___x_669_ = lean_array_mk(v_sorted_668_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 3, v___x_669_);
v___x_671_ = v___x_664_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_uri_659_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_version_x3f_660_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_isIncremental_x3f_661_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(lean_object* v_prev_x3f_677_, lean_object* v_next_678_){
_start:
{
lean_object* v_uri_679_; lean_object* v_version_x3f_680_; lean_object* v_isIncremental_x3f_681_; lean_object* v_diagnostics_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_705_; 
v_uri_679_ = lean_ctor_get(v_next_678_, 0);
v_version_x3f_680_ = lean_ctor_get(v_next_678_, 1);
v_isIncremental_x3f_681_ = lean_ctor_get(v_next_678_, 2);
v_diagnostics_682_ = lean_ctor_get(v_next_678_, 3);
v_isSharedCheck_705_ = !lean_is_exclusive(v_next_678_);
if (v_isSharedCheck_705_ == 0)
{
v___x_684_ = v_next_678_;
v_isShared_685_ = v_isSharedCheck_705_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_diagnostics_682_);
lean_inc(v_isIncremental_x3f_681_);
lean_inc(v_version_x3f_680_);
lean_inc(v_uri_679_);
lean_dec(v_next_678_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_705_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v_replace_688_; 
v___x_686_ = ((lean_object*)(l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams___closed__0));
lean_inc_ref(v_diagnostics_682_);
lean_inc(v_version_x3f_680_);
lean_inc_ref(v_uri_679_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 2, v___x_686_);
v_replace_688_ = v___x_684_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_uri_679_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_version_x3f_680_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_diagnostics_682_);
v_replace_688_ = v_reuseFailAlloc_704_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
if (lean_obj_tag(v_prev_x3f_677_) == 1)
{
if (lean_obj_tag(v_isIncremental_x3f_681_) == 0)
{
lean_dec_ref_known(v_prev_x3f_677_, 1);
lean_dec_ref(v_diagnostics_682_);
lean_dec(v_version_x3f_680_);
lean_dec_ref(v_uri_679_);
return v_replace_688_;
}
else
{
lean_object* v_val_689_; uint8_t v___x_690_; 
v_val_689_ = lean_ctor_get(v_isIncremental_x3f_681_, 0);
lean_inc(v_val_689_);
lean_dec_ref_known(v_isIncremental_x3f_681_, 1);
v___x_690_ = lean_unbox(v_val_689_);
lean_dec(v_val_689_);
if (v___x_690_ == 0)
{
lean_dec_ref_known(v_prev_x3f_677_, 1);
lean_dec_ref(v_diagnostics_682_);
lean_dec(v_version_x3f_680_);
lean_dec_ref(v_uri_679_);
return v_replace_688_;
}
else
{
lean_object* v_val_691_; lean_object* v_diagnostics_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_replace_688_);
v_val_691_ = lean_ctor_get(v_prev_x3f_677_, 0);
lean_inc(v_val_691_);
lean_dec_ref_known(v_prev_x3f_677_, 1);
v_diagnostics_692_ = lean_ctor_get(v_val_691_, 3);
v_isSharedCheck_700_ = !lean_is_exclusive(v_val_691_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; lean_object* v_unused_702_; lean_object* v_unused_703_; 
v_unused_701_ = lean_ctor_get(v_val_691_, 2);
lean_dec(v_unused_701_);
v_unused_702_ = lean_ctor_get(v_val_691_, 1);
lean_dec(v_unused_702_);
v_unused_703_ = lean_ctor_get(v_val_691_, 0);
lean_dec(v_unused_703_);
v___x_694_ = v_val_691_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_diagnostics_692_);
lean_dec(v_val_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = l_Array_append___redArg(v_diagnostics_692_, v_diagnostics_682_);
lean_dec_ref(v_diagnostics_682_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 3, v___x_696_);
lean_ctor_set(v___x_694_, 2, v___x_686_);
lean_ctor_set(v___x_694_, 1, v_version_x3f_680_);
lean_ctor_set(v___x_694_, 0, v_uri_679_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_uri_679_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_version_x3f_680_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
else
{
lean_dec_ref(v_diagnostics_682_);
lean_dec(v_isIncremental_x3f_681_);
lean_dec(v_version_x3f_680_);
lean_dec_ref(v_uri_679_);
lean_dec(v_prev_x3f_677_);
return v_replace_688_;
}
}
}
}
}
lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object* v_waitForDiagnosticsId_709_, lean_object* v_accumulated_x3f_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Lsp_Ipc_readMessage(v_a_711_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_783_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_783_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_783_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_783_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
switch(lean_obj_tag(v_a_714_))
{
case 2:
{
lean_object* v_id_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_744_; 
v_id_718_ = lean_ctor_get(v_a_714_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v_a_714_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_a_714_, 1);
lean_dec(v_unused_745_);
v___x_720_ = v_a_714_;
v_isShared_721_ = v_isSharedCheck_744_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_id_718_);
lean_dec(v_a_714_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_744_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_718_, v_waitForDiagnosticsId_709_);
lean_dec(v_id_718_);
if (v___x_722_ == 0)
{
lean_del_object(v___x_720_);
lean_del_object(v___x_716_);
goto _start;
}
else
{
if (lean_obj_tag(v_accumulated_x3f_710_) == 0)
{
lean_object* v___x_724_; lean_object* v___x_726_; 
lean_del_object(v___x_720_);
v___x_724_ = lean_box(0);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_724_);
v___x_726_ = v___x_716_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
else
{
lean_object* v_val_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_743_; 
v_val_728_ = lean_ctor_get(v_accumulated_x3f_710_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v_accumulated_x3f_710_);
if (v_isSharedCheck_743_ == 0)
{
v___x_730_ = v_accumulated_x3f_710_;
v_isShared_731_ = v_isSharedCheck_743_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_val_728_);
lean_dec(v_accumulated_x3f_710_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_743_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_732_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_733_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(v_val_728_);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 0);
lean_ctor_set(v___x_720_, 1, v___x_733_);
lean_ctor_set(v___x_720_, 0, v___x_732_);
v___x_735_ = v___x_720_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_733_);
v___x_735_ = v_reuseFailAlloc_742_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_735_);
v___x_737_ = v___x_730_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_741_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_739_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_737_);
v___x_739_ = v___x_716_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
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
lean_object* v_id_746_; lean_object* v_message_747_; uint8_t v___x_748_; 
v_id_746_ = lean_ctor_get(v_a_714_, 0);
lean_inc(v_id_746_);
v_message_747_ = lean_ctor_get(v_a_714_, 1);
lean_inc_ref(v_message_747_);
lean_dec_ref_known(v_a_714_, 3);
v___x_748_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_746_, v_waitForDiagnosticsId_709_);
lean_dec(v_id_746_);
if (v___x_748_ == 0)
{
lean_dec_ref(v_message_747_);
lean_del_object(v___x_716_);
goto _start;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
lean_dec(v_accumulated_x3f_710_);
v___x_750_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1));
v___x_751_ = lean_string_append(v___x_750_, v_message_747_);
lean_dec_ref(v_message_747_);
v___x_752_ = lean_mk_io_user_error(v___x_751_);
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 1);
lean_ctor_set(v___x_716_, 0, v___x_752_);
v___x_754_ = v___x_716_;
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
}
case 1:
{
lean_object* v_method_756_; lean_object* v_params_x3f_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_method_756_ = lean_ctor_get(v_a_714_, 0);
lean_inc_ref(v_method_756_);
v_params_x3f_757_ = lean_ctor_get(v_a_714_, 1);
lean_inc(v_params_x3f_757_);
lean_dec_ref_known(v_a_714_, 2);
v___x_758_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_759_ = lean_string_dec_eq(v_method_756_, v___x_758_);
lean_dec_ref(v_method_756_);
if (v___x_759_ == 0)
{
lean_dec(v_params_x3f_757_);
lean_del_object(v___x_716_);
goto _start;
}
else
{
if (lean_obj_tag(v_params_x3f_757_) == 1)
{
lean_object* v_val_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_780_; 
v_val_761_ = lean_ctor_get(v_params_x3f_757_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_params_x3f_757_);
if (v_isSharedCheck_780_ == 0)
{
v___x_763_ = v_params_x3f_757_;
v_isShared_764_ = v_isSharedCheck_780_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_val_761_);
lean_dec(v_params_x3f_757_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_780_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = l_Lean_Json_Structured_toJson(v_val_761_);
v___x_766_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(v___x_765_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
lean_del_object(v___x_763_);
lean_dec(v_accumulated_x3f_710_);
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2));
v___x_769_ = lean_string_append(v___x_768_, v_a_767_);
lean_dec(v_a_767_);
v___x_770_ = lean_mk_io_user_error(v___x_769_);
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 1);
lean_ctor_set(v___x_716_, 0, v___x_770_);
v___x_772_ = v___x_716_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
lean_del_object(v___x_716_);
v_a_774_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_766_, 1);
v___x_775_ = l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(v_accumulated_x3f_710_, v_a_774_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_775_);
v___x_777_ = v___x_763_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_779_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
v_accumulated_x3f_710_ = v___x_777_;
goto _start;
}
}
}
}
else
{
lean_dec(v_params_x3f_757_);
lean_del_object(v___x_716_);
goto _start;
}
}
}
default: 
{
lean_del_object(v___x_716_);
lean_dec(v_a_714_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v_accumulated_x3f_710_);
v_a_784_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_713_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_713_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_waitForDiagnosticsId_709_ = stack[0].m_obj;
lean_object* v_accumulated_x3f_710_ = stack[1].m_obj;
lean_object* v_a_711_ = stack[2].m_obj;
lean_object* v_res_792_;
v_res_792_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_709_, v_accumulated_x3f_710_, v_a_711_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object* v_waitForDiagnosticsId_793_, lean_object* v_accumulated_x3f_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_793_, v_accumulated_x3f_794_, v_a_795_);
lean_dec_ref(v_a_795_);
lean_dec(v_waitForDiagnosticsId_793_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(lean_object* v_v_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(v_v_798_);
v___x_800_ = l_Lean_Json_Structured_fromJson_x3f(v___x_799_);
return v___x_800_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object* v_h_801_, lean_object* v_r_802_){
_start:
{
lean_object* v_id_804_; lean_object* v_method_805_; lean_object* v_param_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_826_; 
v_id_804_ = lean_ctor_get(v_r_802_, 0);
v_method_805_ = lean_ctor_get(v_r_802_, 1);
v_param_806_ = lean_ctor_get(v_r_802_, 2);
v_isSharedCheck_826_ = !lean_is_exclusive(v_r_802_);
if (v_isSharedCheck_826_ == 0)
{
v___x_808_ = v_r_802_;
v_isShared_809_ = v_isSharedCheck_826_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_param_806_);
lean_inc(v_method_805_);
lean_inc(v_id_804_);
lean_dec(v_r_802_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_826_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___y_811_; lean_object* v___x_816_; 
v___x_816_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(v_param_806_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_817_; 
lean_dec_ref_known(v___x_816_, 1);
v___x_817_ = lean_box(0);
v___y_811_ = v___x_817_;
goto v___jp_810_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_816_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_816_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
v___y_811_ = v___x_823_;
goto v___jp_810_;
}
}
}
v___jp_810_:
{
lean_object* v___x_813_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 2, v___y_811_);
v___x_813_ = v___x_808_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_id_804_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_method_805_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v___y_811_);
v___x_813_ = v_reuseFailAlloc_815_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_801_, v___x_813_);
return v___x_814_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_801_ = stack[0].m_obj;
lean_object* v_r_802_ = stack[1].m_obj;
lean_object* v_res_827_;
v_res_827_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_h_801_, v_r_802_);
stack->m_obj
 = v_res_827_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0___boxed(lean_object* v_h_828_, lean_object* v_r_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_h_828_, v_r_829_);
return v_res_831_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object* v_r_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_835_; lean_object* v_a_836_; lean_object* v___x_837_; 
v___x_835_ = l_Lean_Lsp_Ipc_stdin(v_a_833_);
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref(v___x_835_);
v___x_837_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_a_836_, v_r_832_);
return v___x_837_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_832_ = stack[0].m_obj;
lean_object* v_a_833_ = stack[1].m_obj;
lean_object* v_res_838_;
v_res_838_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v_r_832_, v_a_833_);
stack->m_obj
 = v_res_838_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0___boxed(lean_object* v_r_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v_r_839_, v_a_840_);
lean_dec_ref(v_a_840_);
return v_res_842_;
}
}
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object* v_waitForDiagnosticsId_844_, lean_object* v_target_845_, lean_object* v_version_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_849_ = ((lean_object*)(l_Lean_Lsp_Ipc_collectDiagnostics___closed__0));
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v_target_845_);
lean_ctor_set(v___x_850_, 1, v_version_846_);
lean_inc(v_waitForDiagnosticsId_844_);
v___x_851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_851_, 0, v_waitForDiagnosticsId_844_);
lean_ctor_set(v___x_851_, 1, v___x_849_);
lean_ctor_set(v___x_851_, 2, v___x_850_);
v___x_852_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v___x_851_, v_a_847_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec_ref_known(v___x_852_, 1);
v___x_853_ = lean_box(0);
v___x_854_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_844_, v___x_853_, v_a_847_);
lean_dec(v_waitForDiagnosticsId_844_);
return v___x_854_;
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v_waitForDiagnosticsId_844_);
v_a_855_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_852_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_852_);
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
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_collectDiagnostics_0interp(lean_interpreter_value* stack)
{
lean_object* v_waitForDiagnosticsId_844_ = stack[0].m_obj;
lean_object* v_target_845_ = stack[1].m_obj;
lean_object* v_version_846_ = stack[2].m_obj;
lean_object* v_a_847_ = stack[3].m_obj;
lean_object* v_res_863_;
v_res_863_ = l_Lean_Lsp_Ipc_collectDiagnostics(v_waitForDiagnosticsId_844_, v_target_845_, v_version_846_, v_a_847_);
stack->m_obj
 = v_res_863_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___boxed(lean_object* v_waitForDiagnosticsId_864_, lean_object* v_target_865_, lean_object* v_version_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Lsp_Ipc_collectDiagnostics(v_waitForDiagnosticsId_864_, v_target_865_, v_version_866_, v_a_867_);
lean_dec_ref(v_a_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(lean_object* v_v_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(v_v_870_);
v___x_872_ = l_Lean_Json_Structured_fromJson_x3f(v___x_871_);
return v___x_872_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object* v_h_873_, lean_object* v_r_874_){
_start:
{
lean_object* v_id_876_; lean_object* v_method_877_; lean_object* v_param_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_898_; 
v_id_876_ = lean_ctor_get(v_r_874_, 0);
v_method_877_ = lean_ctor_get(v_r_874_, 1);
v_param_878_ = lean_ctor_get(v_r_874_, 2);
v_isSharedCheck_898_ = !lean_is_exclusive(v_r_874_);
if (v_isSharedCheck_898_ == 0)
{
v___x_880_ = v_r_874_;
v_isShared_881_ = v_isSharedCheck_898_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_param_878_);
lean_inc(v_method_877_);
lean_inc(v_id_876_);
lean_dec(v_r_874_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_898_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___y_883_; lean_object* v___x_888_; 
v___x_888_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(v_param_878_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_889_; 
lean_dec_ref_known(v___x_888_, 1);
v___x_889_ = lean_box(0);
v___y_883_ = v___x_889_;
goto v___jp_882_;
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_a_890_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_888_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_888_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
v___y_883_ = v___x_895_;
goto v___jp_882_;
}
}
}
v___jp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 2, v___y_883_);
v___x_885_ = v___x_880_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_id_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_method_877_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v___y_883_);
v___x_885_ = v_reuseFailAlloc_887_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_873_, v___x_885_);
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_873_ = stack[0].m_obj;
lean_object* v_r_874_ = stack[1].m_obj;
lean_object* v_res_899_;
v_res_899_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_h_873_, v_r_874_);
stack->m_obj
 = v_res_899_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0___boxed(lean_object* v_h_900_, lean_object* v_r_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_h_900_, v_r_901_);
return v_res_903_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object* v_r_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_907_; lean_object* v_a_908_; lean_object* v___x_909_; 
v___x_907_ = l_Lean_Lsp_Ipc_stdin(v_a_905_);
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v___x_907_);
v___x_909_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_a_908_, v_r_904_);
return v___x_909_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_904_ = stack[0].m_obj;
lean_object* v_a_905_ = stack[1].m_obj;
lean_object* v_res_910_;
v_res_910_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v_r_904_, v_a_905_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0___boxed(lean_object* v_r_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v_r_911_, v_a_912_);
lean_dec_ref(v_a_912_);
return v_res_914_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(lean_object* v_waitForILeansId_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_Lsp_Ipc_readMessage(v___y_922_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_947_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_947_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_947_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_947_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
switch(lean_obj_tag(v_a_925_))
{
case 2:
{
lean_object* v_id_929_; uint8_t v___x_930_; 
v_id_929_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_id_929_);
lean_dec_ref_known(v_a_925_, 2);
v___x_930_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_929_, v_waitForILeansId_921_);
lean_dec(v_id_929_);
if (v___x_930_ == 0)
{
lean_del_object(v___x_927_);
goto _start;
}
else
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1));
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_932_);
v___x_934_ = v___x_927_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
case 3:
{
lean_object* v_id_936_; lean_object* v_message_937_; uint8_t v___x_938_; 
v_id_936_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_id_936_);
v_message_937_ = lean_ctor_get(v_a_925_, 1);
lean_inc_ref(v_message_937_);
lean_dec_ref_known(v_a_925_, 3);
v___x_938_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_936_, v_waitForILeansId_921_);
lean_dec(v_id_936_);
if (v___x_938_ == 0)
{
lean_dec_ref(v_message_937_);
lean_del_object(v___x_927_);
goto _start;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_940_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2));
v___x_941_ = lean_string_append(v___x_940_, v_message_937_);
lean_dec_ref(v_message_937_);
v___x_942_ = lean_mk_io_user_error(v___x_941_);
if (v_isShared_928_ == 0)
{
lean_ctor_set_tag(v___x_927_, 1);
lean_ctor_set(v___x_927_, 0, v___x_942_);
v___x_944_ = v___x_927_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
default: 
{
lean_del_object(v___x_927_);
lean_dec(v_a_925_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_a_948_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_924_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_924_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_waitForILeansId_921_ = stack[0].m_obj;
lean_object* v___y_922_ = stack[1].m_obj;
lean_object* v_res_956_;
v_res_956_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_921_, v___y_922_);
stack->m_obj
 = v_res_956_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___boxed(lean_object* v_waitForILeansId_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_957_, v___y_958_);
lean_dec_ref(v___y_958_);
lean_dec(v_waitForILeansId_957_);
return v_res_960_;
}
}
lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object* v_waitForILeansId_962_, lean_object* v_target_963_, lean_object* v_version_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_967_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v_target_963_);
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v_version_964_);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
lean_inc(v_waitForILeansId_962_);
v___x_971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_971_, 0, v_waitForILeansId_962_);
lean_ctor_set(v___x_971_, 1, v___x_967_);
lean_ctor_set(v___x_971_, 2, v___x_970_);
v___x_972_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_971_, v_a_965_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec_ref_known(v___x_972_, 1);
v___x_973_ = lean_box(0);
v___x_974_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_962_, v_a_965_);
lean_dec(v_waitForILeansId_962_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_987_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_987_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_987_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_987_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_fst_979_; 
v_fst_979_ = lean_ctor_get(v_a_975_, 0);
lean_inc(v_fst_979_);
lean_dec(v_a_975_);
if (lean_obj_tag(v_fst_979_) == 0)
{
lean_object* v___x_981_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_973_);
v___x_981_ = v___x_977_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_973_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v_val_983_; lean_object* v___x_985_; 
v_val_983_ = lean_ctor_get(v_fst_979_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v_fst_979_, 1);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v_val_983_);
v___x_985_ = v___x_977_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_val_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_a_988_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_974_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_974_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_dec(v_waitForILeansId_962_);
return v___x_972_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_waitForILeans_0interp(lean_interpreter_value* stack)
{
lean_object* v_waitForILeansId_962_ = stack[0].m_obj;
lean_object* v_target_963_ = stack[1].m_obj;
lean_object* v_version_964_ = stack[2].m_obj;
lean_object* v_a_965_ = stack[3].m_obj;
lean_object* v_res_996_;
v_res_996_ = l_Lean_Lsp_Ipc_waitForILeans(v_waitForILeansId_962_, v_target_963_, v_version_964_, v_a_965_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans___boxed(lean_object* v_waitForILeansId_997_, lean_object* v_target_998_, lean_object* v_version_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Lsp_Ipc_waitForILeans(v_waitForILeansId_997_, v_target_998_, v_version_999_, v_a_1000_);
lean_dec_ref(v_a_1000_);
return v_res_1002_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(lean_object* v_waitForILeansId_1003_, lean_object* v_inst_1004_, lean_object* v_a_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_1003_, v___y_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_waitForILeansId_1003_ = stack[0].m_obj;
lean_object* v_a_1005_ = stack[2].m_obj;
lean_object* v___y_1006_ = stack[3].m_obj;
lean_object* v_res_1009_;
v_res_1009_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(v_waitForILeansId_1003_, lean_box(0), v_a_1005_, v___y_1006_);
stack->m_obj
 = v_res_1009_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___boxed(lean_object* v_waitForILeansId_1010_, lean_object* v_inst_1011_, lean_object* v_a_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(v_waitForILeansId_1010_, v_inst_1011_, v_a_1012_, v___y_1013_);
lean_dec_ref(v___y_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_waitForILeansId_1010_);
return v_res_1015_;
}
}
lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans(lean_object* v_waitForILeansId_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1021_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_1022_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0));
lean_inc(v_waitForILeansId_1018_);
v___x_1023_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1023_, 0, v_waitForILeansId_1018_);
lean_ctor_set(v___x_1023_, 1, v___x_1021_);
lean_ctor_set(v___x_1023_, 2, v___x_1022_);
v___x_1024_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_1023_, v_a_1019_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_dec_ref_known(v___x_1024_, 1);
v___x_1025_ = lean_box(0);
v___x_1026_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_1018_, v_a_1019_);
lean_dec(v_waitForILeansId_1018_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1039_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1039_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1039_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_fst_1031_; 
v_fst_1031_ = lean_ctor_get(v_a_1027_, 0);
lean_inc(v_fst_1031_);
lean_dec(v_a_1027_);
if (lean_obj_tag(v_fst_1031_) == 0)
{
lean_object* v___x_1033_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1025_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1025_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
else
{
lean_object* v_val_1035_; lean_object* v___x_1037_; 
v_val_1035_ = lean_ctor_get(v_fst_1031_, 0);
lean_inc(v_val_1035_);
lean_dec_ref_known(v_fst_1031_, 1);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v_val_1035_);
v___x_1037_ = v___x_1029_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_val_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
v_a_1040_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1026_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1026_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_dec(v_waitForILeansId_1018_);
return v___x_1024_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_waitForWatchdogILeans_0interp(lean_interpreter_value* stack)
{
lean_object* v_waitForILeansId_1018_ = stack[0].m_obj;
lean_object* v_a_1019_ = stack[1].m_obj;
lean_object* v_res_1048_;
v_res_1048_ = l_Lean_Lsp_Ipc_waitForWatchdogILeans(v_waitForILeansId_1018_, v_a_1019_);
stack->m_obj
 = v_res_1048_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___boxed(lean_object* v_waitForILeansId_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Lsp_Ipc_waitForWatchdogILeans(v_waitForILeansId_1049_, v_a_1050_);
lean_dec_ref(v_a_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(lean_object* v_j_1053_, lean_object* v_k_1054_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = l_Lean_Json_getObjValD(v_j_1053_, v_k_1054_);
v___x_1056_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0___boxed(lean_object* v_j_1057_, lean_object* v_k_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_j_1057_, v_k_1058_);
lean_dec_ref(v_k_1058_);
return v_res_1059_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_1060_, size_t v_i_1061_, lean_object* v_bs_1062_){
_start:
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_usize_dec_lt(v_i_1061_, v_sz_1060_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v_bs_1062_);
return v___x_1064_;
}
else
{
lean_object* v_v_1065_; lean_object* v___x_1066_; 
v_v_1065_ = lean_array_uget_borrowed(v_bs_1062_, v_i_1061_);
lean_inc(v_v_1065_);
v___x_1066_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_v_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec_ref(v_bs_1062_);
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
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
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v_bs_x27_1077_; size_t v___x_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v_a_1075_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1076_ = lean_unsigned_to_nat(0u);
v_bs_x27_1077_ = lean_array_uset(v_bs_1062_, v_i_1061_, v___x_1076_);
v___x_1078_ = ((size_t)1ULL);
v___x_1079_ = lean_usize_add(v_i_1061_, v___x_1078_);
v___x_1080_ = lean_array_uset(v_bs_x27_1077_, v_i_1061_, v_a_1075_);
v_i_1061_ = v___x_1079_;
v_bs_1062_ = v___x_1080_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1060_ = stack[0].m_num;
size_t v_i_1061_ = stack[1].m_num;
lean_object* v_bs_1062_ = stack[2].m_obj;
lean_object* v_res_1082_;
v_res_1082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_1060_, v_i_1061_, v_bs_1062_);
stack->m_obj
 = v_res_1082_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1083_, lean_object* v_i_1084_, lean_object* v_bs_1085_){
_start:
{
size_t v_sz_boxed_1086_; size_t v_i_boxed_1087_; lean_object* v_res_1088_; 
v_sz_boxed_1086_ = lean_unbox_usize(v_sz_1083_);
lean_dec(v_sz_1083_);
v_i_boxed_1087_ = lean_unbox_usize(v_i_1084_);
lean_dec(v_i_1084_);
v_res_1088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_1086_, v_i_boxed_1087_, v_bs_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_1090_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 4)
{
lean_object* v_elems_1091_; size_t v_sz_1092_; size_t v___x_1093_; lean_object* v___x_1094_; 
v_elems_1091_ = lean_ctor_get(v_x_1090_, 0);
lean_inc_ref(v_elems_1091_);
lean_dec_ref_known(v_x_1090_, 1);
v_sz_1092_ = lean_array_size(v_elems_1091_);
v___x_1093_ = ((size_t)0ULL);
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_1092_, v___x_1093_, v_elems_1091_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1095_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1096_ = lean_unsigned_to_nat(80u);
v___x_1097_ = l_Lean_Json_pretty(v_x_1090_, v___x_1096_);
v___x_1098_ = lean_string_append(v___x_1095_, v___x_1097_);
lean_dec_ref(v___x_1097_);
v___x_1099_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1100_ = lean_string_append(v___x_1098_, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(lean_object* v_j_1102_, lean_object* v_k_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = l_Lean_Json_getObjValD(v_j_1102_, v_k_1103_);
v___x_1105_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1___boxed(lean_object* v_j_1106_, lean_object* v_k_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_j_1106_, v_k_1107_);
lean_dec_ref(v_k_1107_);
return v_res_1108_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = 1;
v___x_1114_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9));
v___x_1115_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = 1;
v___x_1127_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5));
v___x_1128_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_1130_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6);
v___x_1131_ = lean_string_append(v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_1133_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1134_ = lean_string_append(v___x_1133_, v___x_1132_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1136_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11);
v___x_1137_ = lean_string_append(v___x_1136_, v___x_1135_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = 1;
v___x_1142_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15));
v___x_1143_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1142_, v___x_1141_);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16);
v___x_1145_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1146_ = lean_string_append(v___x_1145_, v___x_1144_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1148_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17);
v___x_1149_ = lean_string_append(v___x_1148_, v___x_1147_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = 1;
v___x_1154_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20));
v___x_1155_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1154_, v___x_1153_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_1157_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1158_ = lean_string_append(v___x_1157_, v___x_1156_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1160_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22);
v___x_1161_ = lean_string_append(v___x_1160_, v___x_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(lean_object* v_json_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_1162_);
v___x_1164_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_json_1162_, v___x_1163_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_json_1162_);
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1169_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13);
v___x_1170_ = lean_string_append(v___x_1169_, v_a_1165_);
lean_dec(v_a_1165_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
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
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_json_1162_);
v_a_1175_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1164_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1164_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 0);
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_a_1183_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1164_, 1);
v___x_1184_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
lean_inc(v_json_1162_);
v___x_1185_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_json_1162_, v___x_1184_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_a_1183_);
lean_dec(v_json_1162_);
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
v___x_1190_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18);
v___x_1191_ = lean_string_append(v___x_1190_, v_a_1186_);
lean_dec(v_a_1186_);
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
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_a_1183_);
lean_dec(v_json_1162_);
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
lean_ctor_set_tag(v___x_1198_, 0);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_a_1204_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1205_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1206_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_json_1162_, v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v_a_1204_);
lean_dec(v_a_1183_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1216_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1216_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23);
v___x_1212_ = lean_string_append(v___x_1211_, v_a_1207_);
lean_dec(v_a_1207_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1212_);
v___x_1214_ = v___x_1209_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
else
{
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_a_1204_);
lean_dec(v_a_1183_);
v_a_1217_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1206_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1206_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set_tag(v___x_1219_, 0);
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1233_; 
v_a_1225_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1227_ = v___x_1206_;
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1206_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1183_);
lean_ctor_set(v___x_1229_, 1, v_a_1204_);
lean_ctor_set(v___x_1229_, 2, v_a_1225_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1229_);
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(size_t v_sz_1234_, size_t v_i_1235_, lean_object* v_bs_1236_){
_start:
{
uint8_t v___x_1237_; 
v___x_1237_ = lean_usize_dec_lt(v_i_1235_, v_sz_1234_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_bs_1236_);
return v___x_1238_;
}
else
{
lean_object* v_v_1239_; lean_object* v___x_1240_; 
v_v_1239_ = lean_array_uget_borrowed(v_bs_1236_, v_i_1235_);
lean_inc(v_v_1239_);
v___x_1240_ = l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(v_v_1239_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec_ref(v_bs_1236_);
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1250_; lean_object* v_bs_x27_1251_; size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v_a_1249_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1240_, 1);
v___x_1250_ = lean_unsigned_to_nat(0u);
v_bs_x27_1251_ = lean_array_uset(v_bs_1236_, v_i_1235_, v___x_1250_);
v___x_1252_ = ((size_t)1ULL);
v___x_1253_ = lean_usize_add(v_i_1235_, v___x_1252_);
v___x_1254_ = lean_array_uset(v_bs_x27_1251_, v_i_1235_, v_a_1249_);
v_i_1235_ = v___x_1253_;
v_bs_1236_ = v___x_1254_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1234_ = stack[0].m_num;
size_t v_i_1235_ = stack[1].m_num;
lean_object* v_bs_1236_ = stack[2].m_obj;
lean_object* v_res_1256_;
v_res_1256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_1234_, v_i_1235_, v_bs_1236_);
stack->m_obj
 = v_res_1256_;
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(lean_object* v_x_1257_){
_start:
{
if (lean_obj_tag(v_x_1257_) == 4)
{
lean_object* v_elems_1258_; size_t v_sz_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v_elems_1258_ = lean_ctor_get(v_x_1257_, 0);
lean_inc_ref(v_elems_1258_);
lean_dec_ref_known(v_x_1257_, 1);
v_sz_1259_ = lean_array_size(v_elems_1258_);
v___x_1260_ = ((size_t)0ULL);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_1259_, v___x_1260_, v_elems_1258_);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1262_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1263_ = lean_unsigned_to_nat(80u);
v___x_1264_ = l_Lean_Json_pretty(v_x_1257_, v___x_1263_);
v___x_1265_ = lean_string_append(v___x_1262_, v___x_1264_);
lean_dec_ref(v___x_1264_);
v___x_1266_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1267_ = lean_string_append(v___x_1265_, v___x_1266_);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(lean_object* v_j_1269_, lean_object* v_k_1270_){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = l_Lean_Json_getObjValD(v_j_1269_, v_k_1270_);
v___x_1272_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2___boxed(lean_object* v_j_1273_, lean_object* v_k_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_j_1273_, v_k_1274_);
lean_dec_ref(v_k_1274_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1276_, lean_object* v_i_1277_, lean_object* v_bs_1278_){
_start:
{
size_t v_sz_boxed_1279_; size_t v_i_boxed_1280_; lean_object* v_res_1281_; 
v_sz_boxed_1279_ = lean_unbox_usize(v_sz_1276_);
lean_dec(v_sz_1276_);
v_i_boxed_1280_ = lean_unbox_usize(v_i_1277_);
lean_dec(v_i_1277_);
v_res_1281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_boxed_1279_, v_i_boxed_1280_, v_bs_1278_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
if (lean_obj_tag(v_a_1284_) == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_array_to_list(v_a_1285_);
return v___x_1286_;
}
else
{
lean_object* v_head_1287_; lean_object* v_tail_1288_; lean_object* v___x_1289_; 
v_head_1287_ = lean_ctor_get(v_a_1284_, 0);
lean_inc(v_head_1287_);
v_tail_1288_ = lean_ctor_get(v_a_1284_, 1);
lean_inc(v_tail_1288_);
lean_dec_ref_known(v_a_1284_, 2);
v___x_1289_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1285_, v_head_1287_);
v_a_1284_ = v_tail_1288_;
v_a_1285_ = v___x_1289_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(size_t v_sz_1291_, size_t v_i_1292_, lean_object* v_bs_1293_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_usize_dec_lt(v_i_1292_, v_sz_1291_);
if (v___x_1294_ == 0)
{
return v_bs_1293_;
}
else
{
lean_object* v_v_1295_; lean_object* v___x_1296_; lean_object* v_bs_x27_1297_; lean_object* v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v_v_1295_ = lean_array_uget(v_bs_1293_, v_i_1292_);
v___x_1296_ = lean_unsigned_to_nat(0u);
v_bs_x27_1297_ = lean_array_uset(v_bs_1293_, v_i_1292_, v___x_1296_);
v___x_1298_ = l_Lean_Lsp_instToJsonRange_toJson(v_v_1295_);
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1292_, v___x_1299_);
v___x_1301_ = lean_array_uset(v_bs_x27_1297_, v_i_1292_, v___x_1298_);
v_i_1292_ = v___x_1300_;
v_bs_1293_ = v___x_1301_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1291_ = stack[0].m_num;
size_t v_i_1292_ = stack[1].m_num;
lean_object* v_bs_1293_ = stack[2].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_1291_, v_i_1292_, v_bs_1293_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1304_, lean_object* v_i_1305_, lean_object* v_bs_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1304_);
lean_dec(v_sz_1304_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_boxed_1307_, v_i_boxed_1308_, v_bs_1306_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(lean_object* v_a_1310_){
_start:
{
size_t v_sz_1311_; size_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_sz_1311_ = lean_array_size(v_a_1310_);
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_1311_, v___x_1312_, v_a_1310_);
v___x_1314_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(lean_object* v_x_1317_){
_start:
{
lean_object* v_item_1318_; lean_object* v_fromRanges_1319_; lean_object* v_children_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_item_1318_ = lean_ctor_get(v_x_1317_, 0);
lean_inc_ref(v_item_1318_);
v_fromRanges_1319_ = lean_ctor_get(v_x_1317_, 1);
lean_inc_ref(v_fromRanges_1319_);
v_children_1320_ = lean_ctor_get(v_x_1317_, 2);
lean_inc_ref(v_children_1320_);
lean_dec_ref(v_x_1317_);
v___x_1321_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_1322_ = l_Lean_Lsp_instToJsonCallHierarchyItem_toJson(v_item_1318_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1323_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
v___x_1327_ = l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(v_fromRanges_1319_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v___x_1324_);
v___x_1330_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1331_ = l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(v_children_1320_);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v___x_1324_);
v___x_1334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___x_1324_);
v___x_1335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1329_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1325_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_1338_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_1336_, v___x_1337_);
v___x_1339_ = l_Lean_Json_mkObj(v___x_1338_);
lean_dec(v___x_1338_);
return v___x_1339_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(size_t v_sz_1340_, size_t v_i_1341_, lean_object* v_bs_1342_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_lt(v_i_1341_, v_sz_1340_);
if (v___x_1343_ == 0)
{
return v_bs_1342_;
}
else
{
lean_object* v_v_1344_; lean_object* v___x_1345_; lean_object* v_bs_x27_1346_; lean_object* v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v_v_1344_ = lean_array_uget(v_bs_1342_, v_i_1341_);
v___x_1345_ = lean_unsigned_to_nat(0u);
v_bs_x27_1346_ = lean_array_uset(v_bs_1342_, v_i_1341_, v___x_1345_);
v___x_1347_ = l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(v_v_1344_);
v___x_1348_ = ((size_t)1ULL);
v___x_1349_ = lean_usize_add(v_i_1341_, v___x_1348_);
v___x_1350_ = lean_array_uset(v_bs_x27_1346_, v_i_1341_, v___x_1347_);
v_i_1341_ = v___x_1349_;
v_bs_1342_ = v___x_1350_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1340_ = stack[0].m_num;
size_t v_i_1341_ = stack[1].m_num;
lean_object* v_bs_1342_ = stack[2].m_obj;
lean_object* v_res_1352_;
v_res_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_1340_, v_i_1341_, v_bs_1342_);
stack->m_obj
 = v_res_1352_;
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(lean_object* v_a_1353_){
_start:
{
size_t v_sz_1354_; size_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v_sz_1354_ = lean_array_size(v_a_1353_);
v___x_1355_ = ((size_t)0ULL);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_1354_, v___x_1355_, v_a_1353_);
v___x_1357_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2___boxed(lean_object* v_sz_1358_, lean_object* v_i_1359_, lean_object* v_bs_1360_){
_start:
{
size_t v_sz_boxed_1361_; size_t v_i_boxed_1362_; lean_object* v_res_1363_; 
v_sz_boxed_1361_ = lean_unbox_usize(v_sz_1358_);
lean_dec(v_sz_1358_);
v_i_boxed_1362_ = lean_unbox_usize(v_i_1359_);
lean_dec(v_i_1359_);
v_res_1363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_boxed_1361_, v_i_boxed_1362_, v_bs_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(lean_object* v_k_1366_, lean_object* v_v_1367_, lean_object* v_t_1368_){
_start:
{
if (lean_obj_tag(v_t_1368_) == 0)
{
lean_object* v_size_1369_; lean_object* v_k_1370_; lean_object* v_v_1371_; lean_object* v_l_1372_; lean_object* v_r_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1653_; 
v_size_1369_ = lean_ctor_get(v_t_1368_, 0);
v_k_1370_ = lean_ctor_get(v_t_1368_, 1);
v_v_1371_ = lean_ctor_get(v_t_1368_, 2);
v_l_1372_ = lean_ctor_get(v_t_1368_, 3);
v_r_1373_ = lean_ctor_get(v_t_1368_, 4);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_t_1368_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1375_ = v_t_1368_;
v_isShared_1376_ = v_isSharedCheck_1653_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_r_1373_);
lean_inc(v_l_1372_);
lean_inc(v_v_1371_);
lean_inc(v_k_1370_);
lean_inc(v_size_1369_);
lean_dec(v_t_1368_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1653_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_string_compare(v_k_1366_, v_k_1370_);
switch(v___x_1377_)
{
case 0:
{
lean_object* v_impl_1378_; lean_object* v___x_1379_; 
lean_dec(v_size_1369_);
v_impl_1378_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1366_, v_v_1367_, v_l_1372_);
v___x_1379_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1373_) == 0)
{
lean_object* v_size_1380_; lean_object* v_size_1381_; lean_object* v_k_1382_; lean_object* v_v_1383_; lean_object* v_l_1384_; lean_object* v_r_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v_size_1380_ = lean_ctor_get(v_r_1373_, 0);
v_size_1381_ = lean_ctor_get(v_impl_1378_, 0);
v_k_1382_ = lean_ctor_get(v_impl_1378_, 1);
v_v_1383_ = lean_ctor_get(v_impl_1378_, 2);
v_l_1384_ = lean_ctor_get(v_impl_1378_, 3);
v_r_1385_ = lean_ctor_get(v_impl_1378_, 4);
lean_inc(v_r_1385_);
v___x_1386_ = lean_unsigned_to_nat(3u);
v___x_1387_ = lean_nat_mul(v___x_1386_, v_size_1380_);
v___x_1388_ = lean_nat_dec_lt(v___x_1387_, v_size_1381_);
lean_dec(v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_dec(v_r_1385_);
v___x_1389_ = lean_nat_add(v___x_1379_, v_size_1381_);
v___x_1390_ = lean_nat_add(v___x_1389_, v_size_1380_);
lean_dec(v___x_1389_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 3, v_impl_1378_);
lean_ctor_set(v___x_1375_, 0, v___x_1390_);
v___x_1392_ = v___x_1375_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_impl_1378_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_r_1373_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
else
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1459_; 
lean_inc(v_l_1384_);
lean_inc(v_v_1383_);
lean_inc(v_k_1382_);
lean_inc(v_size_1381_);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_impl_1378_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; lean_object* v_unused_1461_; lean_object* v_unused_1462_; lean_object* v_unused_1463_; lean_object* v_unused_1464_; 
v_unused_1460_ = lean_ctor_get(v_impl_1378_, 4);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_impl_1378_, 3);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_impl_1378_, 2);
lean_dec(v_unused_1462_);
v_unused_1463_ = lean_ctor_get(v_impl_1378_, 1);
lean_dec(v_unused_1463_);
v_unused_1464_ = lean_ctor_get(v_impl_1378_, 0);
lean_dec(v_unused_1464_);
v___x_1395_ = v_impl_1378_;
v_isShared_1396_ = v_isSharedCheck_1459_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v_impl_1378_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1459_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_size_1397_; lean_object* v_size_1398_; lean_object* v_k_1399_; lean_object* v_v_1400_; lean_object* v_l_1401_; lean_object* v_r_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v_size_1397_ = lean_ctor_get(v_l_1384_, 0);
v_size_1398_ = lean_ctor_get(v_r_1385_, 0);
v_k_1399_ = lean_ctor_get(v_r_1385_, 1);
v_v_1400_ = lean_ctor_get(v_r_1385_, 2);
v_l_1401_ = lean_ctor_get(v_r_1385_, 3);
v_r_1402_ = lean_ctor_get(v_r_1385_, 4);
v___x_1403_ = lean_unsigned_to_nat(2u);
v___x_1404_ = lean_nat_mul(v___x_1403_, v_size_1397_);
v___x_1405_ = lean_nat_dec_lt(v_size_1398_, v___x_1404_);
lean_dec(v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1434_; 
lean_inc(v_r_1402_);
lean_inc(v_l_1401_);
lean_inc(v_v_1400_);
lean_inc(v_k_1399_);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_r_1385_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; lean_object* v_unused_1439_; 
v_unused_1435_ = lean_ctor_get(v_r_1385_, 4);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_r_1385_, 3);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_r_1385_, 2);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_r_1385_, 1);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_r_1385_, 0);
lean_dec(v_unused_1439_);
v___x_1407_ = v_r_1385_;
v_isShared_1408_ = v_isSharedCheck_1434_;
goto v_resetjp_1406_;
}
else
{
lean_dec(v_r_1385_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1434_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___x_1422_; lean_object* v___y_1424_; 
v___x_1409_ = lean_nat_add(v___x_1379_, v_size_1381_);
lean_dec(v_size_1381_);
v___x_1410_ = lean_nat_add(v___x_1409_, v_size_1380_);
lean_dec(v___x_1409_);
v___x_1422_ = lean_nat_add(v___x_1379_, v_size_1397_);
if (lean_obj_tag(v_l_1401_) == 0)
{
lean_object* v_size_1432_; 
v_size_1432_ = lean_ctor_get(v_l_1401_, 0);
lean_inc(v_size_1432_);
v___y_1424_ = v_size_1432_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___y_1424_ = v___x_1433_;
goto v___jp_1423_;
}
v___jp_1411_:
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1415_ = lean_nat_add(v___y_1412_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec(v___y_1412_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 4, v_r_1373_);
lean_ctor_set(v___x_1407_, 3, v_r_1402_);
lean_ctor_set(v___x_1407_, 2, v_v_1371_);
lean_ctor_set(v___x_1407_, 1, v_k_1370_);
lean_ctor_set(v___x_1407_, 0, v___x_1415_);
v___x_1417_ = v___x_1407_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_r_1402_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_r_1373_);
v___x_1417_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 4, v___x_1417_);
lean_ctor_set(v___x_1395_, 3, v___y_1413_);
lean_ctor_set(v___x_1395_, 2, v_v_1400_);
lean_ctor_set(v___x_1395_, 1, v_k_1399_);
lean_ctor_set(v___x_1395_, 0, v___x_1410_);
v___x_1419_ = v___x_1395_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v___y_1413_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
v___jp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_nat_add(v___x_1422_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec(v___x_1422_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_l_1401_);
lean_ctor_set(v___x_1375_, 3, v_l_1384_);
lean_ctor_set(v___x_1375_, 2, v_v_1383_);
lean_ctor_set(v___x_1375_, 1, v_k_1382_);
lean_ctor_set(v___x_1375_, 0, v___x_1425_);
v___x_1427_ = v___x_1375_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_k_1382_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_v_1383_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_l_1384_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v_l_1401_);
v___x_1427_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_nat_add(v___x_1379_, v_size_1380_);
if (lean_obj_tag(v_r_1402_) == 0)
{
lean_object* v_size_1429_; 
v_size_1429_ = lean_ctor_get(v_r_1402_, 0);
lean_inc(v_size_1429_);
v___y_1412_ = v___x_1428_;
v___y_1413_ = v___x_1427_;
v___y_1414_ = v_size_1429_;
goto v___jp_1411_;
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_unsigned_to_nat(0u);
v___y_1412_ = v___x_1428_;
v___y_1413_ = v___x_1427_;
v___y_1414_ = v___x_1430_;
goto v___jp_1411_;
}
}
}
}
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_del_object(v___x_1375_);
v___x_1440_ = lean_nat_add(v___x_1379_, v_size_1381_);
lean_dec(v_size_1381_);
v___x_1441_ = lean_nat_add(v___x_1440_, v_size_1380_);
lean_dec(v___x_1440_);
v___x_1442_ = lean_nat_add(v___x_1379_, v_size_1380_);
v___x_1443_ = lean_nat_add(v___x_1442_, v_size_1398_);
lean_dec(v___x_1442_);
lean_inc_ref(v_r_1373_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 4, v_r_1373_);
lean_ctor_set(v___x_1395_, 3, v_r_1385_);
lean_ctor_set(v___x_1395_, 2, v_v_1371_);
lean_ctor_set(v___x_1395_, 1, v_k_1370_);
lean_ctor_set(v___x_1395_, 0, v___x_1443_);
v___x_1445_ = v___x_1395_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v_r_1385_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v_r_1373_);
v___x_1445_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
v_isSharedCheck_1452_ = !lean_is_exclusive(v_r_1373_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; lean_object* v_unused_1454_; lean_object* v_unused_1455_; lean_object* v_unused_1456_; lean_object* v_unused_1457_; 
v_unused_1453_ = lean_ctor_get(v_r_1373_, 4);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_r_1373_, 3);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_r_1373_, 2);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_r_1373_, 1);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_r_1373_, 0);
lean_dec(v_unused_1457_);
v___x_1447_ = v_r_1373_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v_r_1373_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 4, v___x_1445_);
lean_ctor_set(v___x_1447_, 3, v_l_1384_);
lean_ctor_set(v___x_1447_, 2, v_v_1383_);
lean_ctor_set(v___x_1447_, 1, v_k_1382_);
lean_ctor_set(v___x_1447_, 0, v___x_1441_);
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_k_1382_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_v_1383_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v_l_1384_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v___x_1445_);
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
}
else
{
lean_object* v_l_1465_; 
v_l_1465_ = lean_ctor_get(v_impl_1378_, 3);
if (lean_obj_tag(v_l_1465_) == 0)
{
lean_object* v_r_1466_; lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1479_; 
lean_inc_ref(v_l_1465_);
v_r_1466_ = lean_ctor_get(v_impl_1378_, 4);
v_k_1467_ = lean_ctor_get(v_impl_1378_, 1);
v_v_1468_ = lean_ctor_get(v_impl_1378_, 2);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_impl_1378_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; lean_object* v_unused_1481_; 
v_unused_1480_ = lean_ctor_get(v_impl_1378_, 3);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_impl_1378_, 0);
lean_dec(v_unused_1481_);
v___x_1470_ = v_impl_1378_;
v_isShared_1471_ = v_isSharedCheck_1479_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_r_1466_);
lean_inc(v_v_1468_);
lean_inc(v_k_1467_);
lean_dec(v_impl_1378_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1479_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1466_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 3, v_r_1466_);
lean_ctor_set(v___x_1470_, 2, v_v_1371_);
lean_ctor_set(v___x_1470_, 1, v_k_1370_);
lean_ctor_set(v___x_1470_, 0, v___x_1379_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v_r_1466_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v_r_1466_);
v___x_1474_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1476_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v___x_1474_);
lean_ctor_set(v___x_1375_, 3, v_l_1465_);
lean_ctor_set(v___x_1375_, 2, v_v_1468_);
lean_ctor_set(v___x_1375_, 1, v_k_1467_);
lean_ctor_set(v___x_1375_, 0, v___x_1472_);
v___x_1476_ = v___x_1375_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_k_1467_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1468_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_l_1465_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v_r_1482_; 
v_r_1482_ = lean_ctor_get(v_impl_1378_, 4);
lean_inc(v_r_1482_);
if (lean_obj_tag(v_r_1482_) == 0)
{
lean_object* v_k_1483_; lean_object* v_v_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1507_; 
lean_inc(v_l_1465_);
v_k_1483_ = lean_ctor_get(v_impl_1378_, 1);
v_v_1484_ = lean_ctor_get(v_impl_1378_, 2);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_impl_1378_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; lean_object* v_unused_1509_; lean_object* v_unused_1510_; 
v_unused_1508_ = lean_ctor_get(v_impl_1378_, 4);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_impl_1378_, 3);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_impl_1378_, 0);
lean_dec(v_unused_1510_);
v___x_1486_ = v_impl_1378_;
v_isShared_1487_ = v_isSharedCheck_1507_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_v_1484_);
lean_inc(v_k_1483_);
lean_dec(v_impl_1378_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1507_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_k_1488_; lean_object* v_v_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1503_; 
v_k_1488_ = lean_ctor_get(v_r_1482_, 1);
v_v_1489_ = lean_ctor_get(v_r_1482_, 2);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_r_1482_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; 
v_unused_1504_ = lean_ctor_get(v_r_1482_, 4);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_r_1482_, 3);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_r_1482_, 0);
lean_dec(v_unused_1506_);
v___x_1491_ = v_r_1482_;
v_isShared_1492_ = v_isSharedCheck_1503_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_v_1489_);
lean_inc(v_k_1488_);
lean_dec(v_r_1482_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1503_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1493_ = lean_unsigned_to_nat(3u);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 4, v_l_1465_);
lean_ctor_set(v___x_1491_, 3, v_l_1465_);
lean_ctor_set(v___x_1491_, 2, v_v_1484_);
lean_ctor_set(v___x_1491_, 1, v_k_1483_);
lean_ctor_set(v___x_1491_, 0, v___x_1379_);
v___x_1495_ = v___x_1491_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1483_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1484_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_l_1465_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_l_1465_);
v___x_1495_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1497_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v_l_1465_);
lean_ctor_set(v___x_1486_, 2, v_v_1371_);
lean_ctor_set(v___x_1486_, 1, v_k_1370_);
lean_ctor_set(v___x_1486_, 0, v___x_1379_);
v___x_1497_ = v___x_1486_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_l_1465_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_l_1465_);
v___x_1497_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v___x_1497_);
lean_ctor_set(v___x_1375_, 3, v___x_1495_);
lean_ctor_set(v___x_1375_, 2, v_v_1489_);
lean_ctor_set(v___x_1375_, 1, v_k_1488_);
lean_ctor_set(v___x_1375_, 0, v___x_1493_);
v___x_1499_ = v___x_1375_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1488_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1489_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
}
else
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = lean_unsigned_to_nat(2u);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_r_1482_);
lean_ctor_set(v___x_1375_, 3, v_impl_1378_);
lean_ctor_set(v___x_1375_, 0, v___x_1511_);
v___x_1513_ = v___x_1375_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_impl_1378_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_r_1482_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1516_; 
lean_dec(v_v_1371_);
lean_dec(v_k_1370_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 2, v_v_1367_);
lean_ctor_set(v___x_1375_, 1, v_k_1366_);
v___x_1516_ = v___x_1375_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_size_1369_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_l_1372_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_r_1373_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
default: 
{
lean_object* v_impl_1518_; lean_object* v___x_1519_; 
lean_dec(v_size_1369_);
v_impl_1518_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1366_, v_v_1367_, v_r_1373_);
v___x_1519_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1372_) == 0)
{
lean_object* v_size_1520_; lean_object* v_size_1521_; lean_object* v_k_1522_; lean_object* v_v_1523_; lean_object* v_l_1524_; lean_object* v_r_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v_size_1520_ = lean_ctor_get(v_l_1372_, 0);
v_size_1521_ = lean_ctor_get(v_impl_1518_, 0);
v_k_1522_ = lean_ctor_get(v_impl_1518_, 1);
v_v_1523_ = lean_ctor_get(v_impl_1518_, 2);
v_l_1524_ = lean_ctor_get(v_impl_1518_, 3);
lean_inc(v_l_1524_);
v_r_1525_ = lean_ctor_get(v_impl_1518_, 4);
v___x_1526_ = lean_unsigned_to_nat(3u);
v___x_1527_ = lean_nat_mul(v___x_1526_, v_size_1520_);
v___x_1528_ = lean_nat_dec_lt(v___x_1527_, v_size_1521_);
lean_dec(v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
lean_dec(v_l_1524_);
v___x_1529_ = lean_nat_add(v___x_1519_, v_size_1520_);
v___x_1530_ = lean_nat_add(v___x_1529_, v_size_1521_);
lean_dec(v___x_1529_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_impl_1518_);
lean_ctor_set(v___x_1375_, 0, v___x_1530_);
v___x_1532_ = v___x_1375_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_l_1372_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_impl_1518_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
else
{
lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1597_; 
lean_inc(v_r_1525_);
lean_inc(v_v_1523_);
lean_inc(v_k_1522_);
lean_inc(v_size_1521_);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_impl_1518_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; lean_object* v_unused_1602_; 
v_unused_1598_ = lean_ctor_get(v_impl_1518_, 4);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_impl_1518_, 3);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_impl_1518_, 2);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_impl_1518_, 1);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_impl_1518_, 0);
lean_dec(v_unused_1602_);
v___x_1535_ = v_impl_1518_;
v_isShared_1536_ = v_isSharedCheck_1597_;
goto v_resetjp_1534_;
}
else
{
lean_dec(v_impl_1518_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1597_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v_size_1537_; lean_object* v_k_1538_; lean_object* v_v_1539_; lean_object* v_l_1540_; lean_object* v_r_1541_; lean_object* v_size_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v_size_1537_ = lean_ctor_get(v_l_1524_, 0);
v_k_1538_ = lean_ctor_get(v_l_1524_, 1);
v_v_1539_ = lean_ctor_get(v_l_1524_, 2);
v_l_1540_ = lean_ctor_get(v_l_1524_, 3);
v_r_1541_ = lean_ctor_get(v_l_1524_, 4);
v_size_1542_ = lean_ctor_get(v_r_1525_, 0);
v___x_1543_ = lean_unsigned_to_nat(2u);
v___x_1544_ = lean_nat_mul(v___x_1543_, v_size_1542_);
v___x_1545_ = lean_nat_dec_lt(v_size_1537_, v___x_1544_);
lean_dec(v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1573_; 
lean_inc(v_r_1541_);
lean_inc(v_l_1540_);
lean_inc(v_v_1539_);
lean_inc(v_k_1538_);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_l_1524_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; lean_object* v_unused_1578_; 
v_unused_1574_ = lean_ctor_get(v_l_1524_, 4);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_l_1524_, 3);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_l_1524_, 2);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_l_1524_, 1);
lean_dec(v_unused_1577_);
v_unused_1578_ = lean_ctor_get(v_l_1524_, 0);
lean_dec(v_unused_1578_);
v___x_1547_ = v_l_1524_;
v_isShared_1548_ = v_isSharedCheck_1573_;
goto v_resetjp_1546_;
}
else
{
lean_dec(v_l_1524_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1573_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1563_; 
v___x_1549_ = lean_nat_add(v___x_1519_, v_size_1520_);
v___x_1550_ = lean_nat_add(v___x_1549_, v_size_1521_);
lean_dec(v_size_1521_);
if (lean_obj_tag(v_l_1540_) == 0)
{
lean_object* v_size_1571_; 
v_size_1571_ = lean_ctor_get(v_l_1540_, 0);
lean_inc(v_size_1571_);
v___y_1563_ = v_size_1571_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_unsigned_to_nat(0u);
v___y_1563_ = v___x_1572_;
goto v___jp_1562_;
}
v___jp_1551_:
{
lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1555_ = lean_nat_add(v___y_1552_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec(v___y_1552_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 4, v_r_1525_);
lean_ctor_set(v___x_1547_, 3, v_r_1541_);
lean_ctor_set(v___x_1547_, 2, v_v_1523_);
lean_ctor_set(v___x_1547_, 1, v_k_1522_);
lean_ctor_set(v___x_1547_, 0, v___x_1555_);
v___x_1557_ = v___x_1547_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_k_1522_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_v_1523_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v_r_1541_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v_r_1525_);
v___x_1557_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1559_; 
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 4, v___x_1557_);
lean_ctor_set(v___x_1535_, 3, v___y_1553_);
lean_ctor_set(v___x_1535_, 2, v_v_1539_);
lean_ctor_set(v___x_1535_, 1, v_k_1538_);
lean_ctor_set(v___x_1535_, 0, v___x_1550_);
v___x_1559_ = v___x_1535_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_k_1538_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_v_1539_);
lean_ctor_set(v_reuseFailAlloc_1560_, 3, v___y_1553_);
lean_ctor_set(v_reuseFailAlloc_1560_, 4, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
v___jp_1562_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = lean_nat_add(v___x_1549_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec(v___x_1549_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_l_1540_);
lean_ctor_set(v___x_1375_, 0, v___x_1564_);
v___x_1566_ = v___x_1375_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v_l_1372_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v_l_1540_);
v___x_1566_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_nat_add(v___x_1519_, v_size_1542_);
if (lean_obj_tag(v_r_1541_) == 0)
{
lean_object* v_size_1568_; 
v_size_1568_ = lean_ctor_get(v_r_1541_, 0);
lean_inc(v_size_1568_);
v___y_1552_ = v___x_1567_;
v___y_1553_ = v___x_1566_;
v___y_1554_ = v_size_1568_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_unsigned_to_nat(0u);
v___y_1552_ = v___x_1567_;
v___y_1553_ = v___x_1566_;
v___y_1554_ = v___x_1569_;
goto v___jp_1551_;
}
}
}
}
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
lean_del_object(v___x_1375_);
v___x_1579_ = lean_nat_add(v___x_1519_, v_size_1520_);
v___x_1580_ = lean_nat_add(v___x_1579_, v_size_1521_);
lean_dec(v_size_1521_);
v___x_1581_ = lean_nat_add(v___x_1579_, v_size_1537_);
lean_dec(v___x_1579_);
lean_inc_ref(v_l_1372_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 4, v_l_1524_);
lean_ctor_set(v___x_1535_, 3, v_l_1372_);
lean_ctor_set(v___x_1535_, 2, v_v_1371_);
lean_ctor_set(v___x_1535_, 1, v_k_1370_);
lean_ctor_set(v___x_1535_, 0, v___x_1581_);
v___x_1583_ = v___x_1535_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_l_1372_);
lean_ctor_set(v_reuseFailAlloc_1596_, 4, v_l_1524_);
v___x_1583_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
v_isSharedCheck_1590_ = !lean_is_exclusive(v_l_1372_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1591_ = lean_ctor_get(v_l_1372_, 4);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_l_1372_, 3);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_l_1372_, 2);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_l_1372_, 1);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_l_1372_, 0);
lean_dec(v_unused_1595_);
v___x_1585_ = v_l_1372_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_dec(v_l_1372_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 4, v_r_1525_);
lean_ctor_set(v___x_1585_, 3, v___x_1583_);
lean_ctor_set(v___x_1585_, 2, v_v_1523_);
lean_ctor_set(v___x_1585_, 1, v_k_1522_);
lean_ctor_set(v___x_1585_, 0, v___x_1580_);
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_k_1522_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_v_1523_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v_r_1525_);
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
}
}
else
{
lean_object* v_l_1603_; 
v_l_1603_ = lean_ctor_get(v_impl_1518_, 3);
lean_inc(v_l_1603_);
if (lean_obj_tag(v_l_1603_) == 0)
{
lean_object* v_r_1604_; lean_object* v_k_1605_; lean_object* v_v_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1629_; 
v_r_1604_ = lean_ctor_get(v_impl_1518_, 4);
v_k_1605_ = lean_ctor_get(v_impl_1518_, 1);
v_v_1606_ = lean_ctor_get(v_impl_1518_, 2);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_impl_1518_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; lean_object* v_unused_1631_; 
v_unused_1630_ = lean_ctor_get(v_impl_1518_, 3);
lean_dec(v_unused_1630_);
v_unused_1631_ = lean_ctor_get(v_impl_1518_, 0);
lean_dec(v_unused_1631_);
v___x_1608_ = v_impl_1518_;
v_isShared_1609_ = v_isSharedCheck_1629_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_r_1604_);
lean_inc(v_v_1606_);
lean_inc(v_k_1605_);
lean_dec(v_impl_1518_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1629_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v_k_1610_; lean_object* v_v_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1625_; 
v_k_1610_ = lean_ctor_get(v_l_1603_, 1);
v_v_1611_ = lean_ctor_get(v_l_1603_, 2);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_l_1603_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; lean_object* v_unused_1627_; lean_object* v_unused_1628_; 
v_unused_1626_ = lean_ctor_get(v_l_1603_, 4);
lean_dec(v_unused_1626_);
v_unused_1627_ = lean_ctor_get(v_l_1603_, 3);
lean_dec(v_unused_1627_);
v_unused_1628_ = lean_ctor_get(v_l_1603_, 0);
lean_dec(v_unused_1628_);
v___x_1613_ = v_l_1603_;
v_isShared_1614_ = v_isSharedCheck_1625_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_v_1611_);
lean_inc(v_k_1610_);
lean_dec(v_l_1603_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1625_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1604_, 2);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 4, v_r_1604_);
lean_ctor_set(v___x_1613_, 3, v_r_1604_);
lean_ctor_set(v___x_1613_, 2, v_v_1371_);
lean_ctor_set(v___x_1613_, 1, v_k_1370_);
lean_ctor_set(v___x_1613_, 0, v___x_1519_);
v___x_1617_ = v___x_1613_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v_r_1604_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v_r_1604_);
v___x_1617_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1619_; 
lean_inc(v_r_1604_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 3, v_r_1604_);
lean_ctor_set(v___x_1608_, 0, v___x_1519_);
v___x_1619_ = v___x_1608_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_k_1605_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_v_1606_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_r_1604_);
lean_ctor_set(v_reuseFailAlloc_1623_, 4, v_r_1604_);
v___x_1619_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1621_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v___x_1619_);
lean_ctor_set(v___x_1375_, 3, v___x_1617_);
lean_ctor_set(v___x_1375_, 2, v_v_1611_);
lean_ctor_set(v___x_1375_, 1, v_k_1610_);
lean_ctor_set(v___x_1375_, 0, v___x_1615_);
v___x_1621_ = v___x_1375_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_k_1610_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_v_1611_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v___x_1617_);
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
}
}
else
{
lean_object* v_r_1632_; 
v_r_1632_ = lean_ctor_get(v_impl_1518_, 4);
lean_inc(v_r_1632_);
if (lean_obj_tag(v_r_1632_) == 0)
{
lean_object* v_k_1633_; lean_object* v_v_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1645_; 
v_k_1633_ = lean_ctor_get(v_impl_1518_, 1);
v_v_1634_ = lean_ctor_get(v_impl_1518_, 2);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_impl_1518_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; lean_object* v_unused_1647_; lean_object* v_unused_1648_; 
v_unused_1646_ = lean_ctor_get(v_impl_1518_, 4);
lean_dec(v_unused_1646_);
v_unused_1647_ = lean_ctor_get(v_impl_1518_, 3);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_impl_1518_, 0);
lean_dec(v_unused_1648_);
v___x_1636_ = v_impl_1518_;
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_v_1634_);
lean_inc(v_k_1633_);
lean_dec(v_impl_1518_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1638_ = lean_unsigned_to_nat(3u);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 4, v_l_1603_);
lean_ctor_set(v___x_1636_, 2, v_v_1371_);
lean_ctor_set(v___x_1636_, 1, v_k_1370_);
lean_ctor_set(v___x_1636_, 0, v___x_1519_);
v___x_1640_ = v___x_1636_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_l_1603_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_l_1603_);
v___x_1640_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1642_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_r_1632_);
lean_ctor_set(v___x_1375_, 3, v___x_1640_);
lean_ctor_set(v___x_1375_, 2, v_v_1634_);
lean_ctor_set(v___x_1375_, 1, v_k_1633_);
lean_ctor_set(v___x_1375_, 0, v___x_1638_);
v___x_1642_ = v___x_1375_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_k_1633_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_v_1634_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v_r_1632_);
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
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = lean_unsigned_to_nat(2u);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v_impl_1518_);
lean_ctor_set(v___x_1375_, 3, v_r_1632_);
lean_ctor_set(v___x_1375_, 0, v___x_1649_);
v___x_1651_ = v___x_1375_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_k_1370_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_v_1371_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_r_1632_);
lean_ctor_set(v_reuseFailAlloc_1652_, 4, v_impl_1518_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v_k_1366_);
lean_ctor_set(v___x_1655_, 2, v_v_1367_);
lean_ctor_set(v___x_1655_, 3, v_t_1368_);
lean_ctor_set(v___x_1655_, 4, v_t_1368_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(lean_object* v_k_1656_, lean_object* v_x_1657_){
_start:
{
if (lean_obj_tag(v_x_1657_) == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref(v_k_1656_);
v___x_1658_ = lean_box(0);
return v___x_1658_;
}
else
{
lean_object* v_val_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_val_1659_ = lean_ctor_get(v_x_1657_, 0);
lean_inc(v_val_1659_);
v___x_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1660_, 0, v_k_1656_);
lean_ctor_set(v___x_1660_, 1, v_val_1659_);
v___x_1661_ = lean_box(0);
v___x_1662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4___boxed(lean_object* v_k_1663_, lean_object* v_x_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v_k_1663_, v_x_1664_);
lean_dec(v_x_1664_);
return v_res_1665_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(size_t v_sz_1666_, size_t v_i_1667_, lean_object* v_bs_1668_){
_start:
{
uint8_t v___x_1669_; 
v___x_1669_ = lean_usize_dec_lt(v_i_1667_, v_sz_1666_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_bs_1668_);
return v___x_1670_;
}
else
{
lean_object* v_v_1671_; lean_object* v___x_1672_; 
v_v_1671_ = lean_array_uget_borrowed(v_bs_1668_, v_i_1667_);
lean_inc(v_v_1671_);
v___x_1672_ = l_Lean_Lsp_instFromJsonCallHierarchyIncomingCall_fromJson(v_v_1671_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref(v_bs_1668_);
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
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
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1681_; lean_object* v___x_1682_; lean_object* v_bs_x27_1683_; size_t v___x_1684_; size_t v___x_1685_; lean_object* v___x_1686_; 
v_a_1681_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1672_, 1);
v___x_1682_ = lean_unsigned_to_nat(0u);
v_bs_x27_1683_ = lean_array_uset(v_bs_1668_, v_i_1667_, v___x_1682_);
v___x_1684_ = ((size_t)1ULL);
v___x_1685_ = lean_usize_add(v_i_1667_, v___x_1684_);
v___x_1686_ = lean_array_uset(v_bs_x27_1683_, v_i_1667_, v_a_1681_);
v_i_1667_ = v___x_1685_;
v_bs_1668_ = v___x_1686_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1666_ = stack[0].m_num;
size_t v_i_1667_ = stack[1].m_num;
lean_object* v_bs_1668_ = stack[2].m_obj;
lean_object* v_res_1688_;
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_1666_, v_i_1667_, v_bs_1668_);
stack->m_obj
 = v_res_1688_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_sz_1689_, lean_object* v_i_1690_, lean_object* v_bs_1691_){
_start:
{
size_t v_sz_boxed_1692_; size_t v_i_boxed_1693_; lean_object* v_res_1694_; 
v_sz_boxed_1692_ = lean_unbox_usize(v_sz_1689_);
lean_dec(v_sz_1689_);
v_i_boxed_1693_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_res_1694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_boxed_1692_, v_i_boxed_1693_, v_bs_1691_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(lean_object* v_x_1695_){
_start:
{
if (lean_obj_tag(v_x_1695_) == 4)
{
lean_object* v_elems_1696_; size_t v_sz_1697_; size_t v___x_1698_; lean_object* v___x_1699_; 
v_elems_1696_ = lean_ctor_get(v_x_1695_, 0);
lean_inc_ref(v_elems_1696_);
lean_dec_ref_known(v_x_1695_, 1);
v_sz_1697_ = lean_array_size(v_elems_1696_);
v___x_1698_ = ((size_t)0ULL);
v___x_1699_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_1697_, v___x_1698_, v_elems_1696_);
return v___x_1699_;
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1700_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1701_ = lean_unsigned_to_nat(80u);
v___x_1702_ = l_Lean_Json_pretty(v_x_1695_, v___x_1701_);
v___x_1703_ = lean_string_append(v___x_1700_, v___x_1702_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1705_ = lean_string_append(v___x_1703_, v___x_1704_);
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
return v___x_1706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(lean_object* v_x_1709_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 0)
{
lean_object* v___x_1710_; 
v___x_1710_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0));
return v___x_1710_;
}
else
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(v_x_1709_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1728_; 
v_a_1720_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1722_ = v___x_1711_;
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1711_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_a_1720_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1724_);
v___x_1726_ = v___x_1722_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
}
lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(lean_object* v_expectedID_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_Lsp_Ipc_stdout(v_a_1730_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1876_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1876_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1876_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_1733_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1867_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1867_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1867_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___y_1743_; lean_object* v___y_1744_; 
switch(lean_obj_tag(v_a_1738_))
{
case 2:
{
lean_object* v_id_1750_; lean_object* v_result_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1795_; 
v_id_1750_ = lean_ctor_get(v_a_1738_, 0);
v_result_1751_ = lean_ctor_get(v_a_1738_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_a_1738_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1753_ = v_a_1738_;
v_isShared_1754_ = v_isSharedCheck_1795_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_result_1751_);
lean_inc(v_id_1750_);
lean_dec(v_a_1738_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1795_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
uint8_t v___x_1755_; 
v___x_1755_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_1750_, v_expectedID_1729_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___y_1758_; 
lean_del_object(v___x_1753_);
lean_dec(v_result_1751_);
lean_del_object(v___x_1735_);
v___x_1756_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_1729_))
{
case 0:
{
lean_object* v_s_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_s_1769_ = lean_ctor_get(v_expectedID_1729_, 0);
lean_inc_ref(v_s_1769_);
lean_dec_ref_known(v_expectedID_1729_, 1);
v___x_1770_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1771_ = lean_string_append(v___x_1770_, v_s_1769_);
lean_dec_ref(v_s_1769_);
v___x_1772_ = lean_string_append(v___x_1771_, v___x_1770_);
v___y_1758_ = v___x_1772_;
goto v___jp_1757_;
}
case 1:
{
lean_object* v_n_1773_; lean_object* v___x_1774_; 
v_n_1773_ = lean_ctor_get(v_expectedID_1729_, 0);
lean_inc_ref(v_n_1773_);
lean_dec_ref_known(v_expectedID_1729_, 1);
v___x_1774_ = l_Lean_JsonNumber_toString(v_n_1773_);
v___y_1758_ = v___x_1774_;
goto v___jp_1757_;
}
default: 
{
lean_object* v___x_1775_; 
v___x_1775_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1758_ = v___x_1775_;
goto v___jp_1757_;
}
}
v___jp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = lean_string_append(v___x_1756_, v___y_1758_);
lean_dec_ref(v___y_1758_);
v___x_1760_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_1761_ = lean_string_append(v___x_1759_, v___x_1760_);
switch(lean_obj_tag(v_id_1750_))
{
case 0:
{
lean_object* v_s_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_s_1762_ = lean_ctor_get(v_id_1750_, 0);
lean_inc_ref(v_s_1762_);
lean_dec_ref_known(v_id_1750_, 1);
v___x_1763_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1764_ = lean_string_append(v___x_1763_, v_s_1762_);
lean_dec_ref(v_s_1762_);
v___x_1765_ = lean_string_append(v___x_1764_, v___x_1763_);
v___y_1743_ = v___x_1761_;
v___y_1744_ = v___x_1765_;
goto v___jp_1742_;
}
case 1:
{
lean_object* v_n_1766_; lean_object* v___x_1767_; 
v_n_1766_ = lean_ctor_get(v_id_1750_, 0);
lean_inc_ref(v_n_1766_);
lean_dec_ref_known(v_id_1750_, 1);
v___x_1767_ = l_Lean_JsonNumber_toString(v_n_1766_);
v___y_1743_ = v___x_1761_;
v___y_1744_ = v___x_1767_;
goto v___jp_1742_;
}
default: 
{
lean_object* v___x_1768_; 
v___x_1768_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1743_ = v___x_1761_;
v___y_1744_ = v___x_1768_;
goto v___jp_1742_;
}
}
}
}
else
{
lean_object* v___x_1776_; 
lean_dec(v_id_1750_);
lean_del_object(v___x_1740_);
lean_inc(v_result_1751_);
v___x_1776_ = l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(v_result_1751_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_del_object(v___x_1753_);
lean_dec(v_expectedID_1729_);
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_1779_ = l_Lean_Json_compress(v_result_1751_);
v___x_1780_ = lean_string_append(v___x_1778_, v___x_1779_);
lean_dec_ref(v___x_1779_);
v___x_1781_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_1782_ = lean_string_append(v___x_1780_, v___x_1781_);
v___x_1783_ = lean_string_append(v___x_1782_, v_a_1777_);
lean_dec(v_a_1777_);
v___x_1784_ = lean_mk_io_user_error(v___x_1783_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 1);
lean_ctor_set(v___x_1735_, 0, v___x_1784_);
v___x_1786_ = v___x_1735_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; 
lean_dec(v_result_1751_);
v_a_1788_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1776_, 1);
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 0);
lean_ctor_set(v___x_1753_, 1, v_a_1788_);
lean_ctor_set(v___x_1753_, 0, v_expectedID_1729_);
v___x_1790_ = v___x_1753_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_expectedID_1729_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_a_1788_);
v___x_1790_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1792_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1790_);
v___x_1792_ = v___x_1735_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_1796_; uint8_t v_code_1797_; lean_object* v_message_1798_; lean_object* v_data_x3f_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___x_1831_; lean_object* v___y_1833_; 
lean_del_object(v___x_1740_);
lean_dec(v_expectedID_1729_);
v_id_1796_ = lean_ctor_get(v_a_1738_, 0);
lean_inc(v_id_1796_);
v_code_1797_ = lean_ctor_get_uint8(v_a_1738_, sizeof(void*)*3);
v_message_1798_ = lean_ctor_get(v_a_1738_, 1);
lean_inc_ref(v_message_1798_);
v_data_x3f_1799_ = lean_ctor_get(v_a_1738_, 2);
lean_inc(v_data_x3f_1799_);
lean_dec_ref_known(v_a_1738_, 3);
v___x_1800_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_1801_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_1831_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_1796_))
{
case 0:
{
lean_object* v_s_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_s_1849_ = lean_ctor_get(v_id_1796_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_id_1796_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v_id_1796_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_s_1849_);
lean_dec(v_id_1796_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
lean_ctor_set_tag(v___x_1851_, 3);
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_s_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
v___y_1833_ = v___x_1854_;
goto v___jp_1832_;
}
}
}
case 1:
{
lean_object* v_n_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
v_n_1857_ = lean_ctor_get(v_id_1796_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_id_1796_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v_id_1796_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_n_1857_);
lean_dec(v_id_1796_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set_tag(v___x_1859_, 2);
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_n_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
v___y_1833_ = v___x_1862_;
goto v___jp_1832_;
}
}
}
default: 
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_box(0);
v___y_1833_ = v___x_1865_;
goto v___jp_1832_;
}
}
v___jp_1802_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
lean_inc(v___y_1806_);
lean_inc_ref(v___y_1804_);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___y_1804_);
lean_ctor_set(v___x_1807_, 1, v___y_1806_);
v___x_1808_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_1809_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1809_, 0, v_message_1798_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1807_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_1815_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_1814_, v_data_x3f_1799_);
lean_dec(v_data_x3f_1799_);
v___x_1816_ = l_List_appendTR___redArg(v___x_1813_, v___x_1815_);
v___x_1817_ = l_Lean_Json_mkObj(v___x_1816_);
lean_dec(v___x_1816_);
lean_inc_ref(v___y_1805_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___y_1805_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___x_1811_);
v___x_1820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___y_1803_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1801_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = l_Lean_Json_mkObj(v___x_1821_);
lean_dec_ref_known(v___x_1821_, 2);
v___x_1823_ = l_Lean_Json_compress(v___x_1822_);
v___x_1824_ = lean_string_append(v___x_1800_, v___x_1823_);
lean_dec_ref(v___x_1823_);
v___x_1825_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1826_ = lean_string_append(v___x_1824_, v___x_1825_);
v___x_1827_ = lean_mk_io_user_error(v___x_1826_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 1);
lean_ctor_set(v___x_1735_, 0, v___x_1827_);
v___x_1829_ = v___x_1735_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
v___jp_1832_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1831_);
lean_ctor_set(v___x_1834_, 1, v___y_1833_);
v___x_1835_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_1836_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_1797_)
{
case 0:
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1837_;
goto v___jp_1802_;
}
case 1:
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1838_;
goto v___jp_1802_;
}
case 2:
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1839_;
goto v___jp_1802_;
}
case 3:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1840_;
goto v___jp_1802_;
}
case 4:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1841_;
goto v___jp_1802_;
}
case 5:
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1842_;
goto v___jp_1802_;
}
case 6:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1843_;
goto v___jp_1802_;
}
case 7:
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1844_;
goto v___jp_1802_;
}
case 8:
{
lean_object* v___x_1845_; 
v___x_1845_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1845_;
goto v___jp_1802_;
}
case 9:
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1846_;
goto v___jp_1802_;
}
case 10:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1847_;
goto v___jp_1802_;
}
default: 
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_1803_ = v___x_1834_;
v___y_1804_ = v___x_1836_;
v___y_1805_ = v___x_1835_;
v___y_1806_ = v___x_1848_;
goto v___jp_1802_;
}
}
}
}
default: 
{
lean_del_object(v___x_1740_);
lean_dec(v_a_1738_);
lean_del_object(v___x_1735_);
goto _start;
}
}
v___jp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1745_ = lean_string_append(v___y_1743_, v___y_1744_);
lean_dec_ref(v___y_1744_);
v___x_1746_ = lean_mk_io_user_error(v___x_1745_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set_tag(v___x_1740_, 1);
lean_ctor_set(v___x_1740_, 0, v___x_1746_);
v___x_1748_ = v___x_1740_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_del_object(v___x_1735_);
lean_dec(v_expectedID_1729_);
v_a_1868_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1737_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1737_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v_expectedID_1729_);
v_a_1877_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1732_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1732_);
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
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedID_1729_ = stack[0].m_obj;
lean_object* v_a_1730_ = stack[1].m_obj;
lean_object* v_res_1885_;
v_res_1885_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v_expectedID_1729_, v_a_1730_);
stack->m_obj
 = v_res_1885_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2___boxed(lean_object* v_expectedID_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v_expectedID_1886_, v_a_1887_);
lean_dec_ref(v_a_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(lean_object* v_v_1890_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = l_Lean_Lsp_instToJsonCallHierarchyIncomingCallsParams_toJson(v_v_1890_);
v___x_1892_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1891_);
return v___x_1892_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(lean_object* v_h_1893_, lean_object* v_r_1894_){
_start:
{
lean_object* v_id_1896_; lean_object* v_method_1897_; lean_object* v_param_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1918_; 
v_id_1896_ = lean_ctor_get(v_r_1894_, 0);
v_method_1897_ = lean_ctor_get(v_r_1894_, 1);
v_param_1898_ = lean_ctor_get(v_r_1894_, 2);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_r_1894_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1900_ = v_r_1894_;
v_isShared_1901_ = v_isSharedCheck_1918_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_param_1898_);
lean_inc(v_method_1897_);
lean_inc(v_id_1896_);
lean_dec(v_r_1894_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1918_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___y_1903_; lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(v_param_1898_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v___x_1909_; 
lean_dec_ref_known(v___x_1908_, 1);
v___x_1909_ = lean_box(0);
v___y_1903_ = v___x_1909_;
goto v___jp_1902_;
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_a_1910_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1908_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1908_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
v___y_1903_ = v___x_1915_;
goto v___jp_1902_;
}
}
}
v___jp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 2, v___y_1903_);
v___x_1905_ = v___x_1900_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_id_1896_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_method_1897_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v___y_1903_);
v___x_1905_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_1893_, v___x_1905_);
return v___x_1906_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1893_ = stack[0].m_obj;
lean_object* v_r_1894_ = stack[1].m_obj;
lean_object* v_res_1919_;
v_res_1919_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_h_1893_, v_r_1894_);
stack->m_obj
 = v_res_1919_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1___boxed(lean_object* v_h_1920_, lean_object* v_r_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_h_1920_, v_r_1921_);
return v_res_1923_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(lean_object* v_r_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v___x_1927_; lean_object* v_a_1928_; lean_object* v___x_1929_; 
v___x_1927_ = l_Lean_Lsp_Ipc_stdin(v_a_1925_);
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_a_1928_, v_r_1924_);
return v___x_1929_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1924_ = stack[0].m_obj;
lean_object* v_a_1925_ = stack[1].m_obj;
lean_object* v_res_1930_;
v_res_1930_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v_r_1924_, v_a_1925_);
stack->m_obj
 = v_res_1930_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1___boxed(lean_object* v_r_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v_r_1931_, v_a_1932_);
lean_dec_ref(v_a_1932_);
return v_res_1934_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(lean_object* v_k_1935_, lean_object* v_t_1936_){
_start:
{
if (lean_obj_tag(v_t_1936_) == 0)
{
lean_object* v_k_1937_; lean_object* v_l_1938_; lean_object* v_r_1939_; uint8_t v___x_1940_; 
v_k_1937_ = lean_ctor_get(v_t_1936_, 1);
v_l_1938_ = lean_ctor_get(v_t_1936_, 3);
v_r_1939_ = lean_ctor_get(v_t_1936_, 4);
v___x_1940_ = lean_string_compare(v_k_1935_, v_k_1937_);
switch(v___x_1940_)
{
case 0:
{
v_t_1936_ = v_l_1938_;
goto _start;
}
case 1:
{
uint8_t v___x_1942_; 
v___x_1942_ = 1;
return v___x_1942_;
}
default: 
{
v_t_1936_ = v_r_1939_;
goto _start;
}
}
}
else
{
uint8_t v___x_1944_; 
v___x_1944_ = 0;
return v___x_1944_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1935_ = stack[0].m_obj;
lean_object* v_t_1936_ = stack[1].m_obj;
uint8_t v_res_1945_;
v_res_1945_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_1935_, v_t_1936_);
stack->m_num = v_res_1945_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg___boxed(lean_object* v_k_1946_, lean_object* v_t_1947_){
_start:
{
uint8_t v_res_1948_; lean_object* v_r_1949_; 
v_res_1948_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_1946_, v_t_1947_);
lean_dec(v_t_1947_);
lean_dec_ref(v_k_1946_);
v_r_1949_ = lean_box(v_res_1948_);
return v_r_1949_;
}
}
lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(lean_object* v_requestNo_1957_, lean_object* v_item_1958_, lean_object* v_fromRanges_1959_, lean_object* v_visited_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_name_1963_; uint8_t v___x_1964_; 
v_name_1963_ = lean_ctor_get(v_item_1958_, 0);
v___x_1964_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_1963_, v_visited_1960_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_inc(v_requestNo_1957_);
v___x_1965_ = l_Lean_JsonNumber_fromNat(v_requestNo_1957_);
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
v___x_1967_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_1958_);
lean_inc_ref(v___x_1966_);
v___x_1968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1966_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
lean_ctor_set(v___x_1968_, 2, v_item_1958_);
v___x_1969_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v___x_1968_, v_a_1961_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v___x_1970_; 
lean_dec_ref_known(v___x_1969_, 1);
v___x_1970_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v___x_1966_, v_a_1961_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_2008_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
if (v___x_1964_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_box(0);
lean_inc_ref(v_name_1963_);
v___x_2015_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_1963_, v___x_2014_, v_visited_1960_);
v___y_2008_ = v___x_2015_;
goto v___jp_2007_;
}
else
{
v___y_2008_ = v_visited_1960_;
goto v___jp_2007_;
}
v___jp_1972_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; size_t v_sz_1978_; size_t v___x_1979_; lean_object* v___x_1980_; 
v___x_1976_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___y_1974_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v_sz_1978_ = lean_array_size(v___y_1975_);
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___y_1973_, v___y_1975_, v_sz_1978_, v___x_1979_, v___x_1977_, v_a_1961_);
lean_dec_ref(v___y_1975_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1998_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_1998_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1998_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_fst_1985_; lean_object* v_snd_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1997_; 
v_fst_1985_ = lean_ctor_get(v_a_1981_, 0);
v_snd_1986_ = lean_ctor_get(v_a_1981_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_a_1981_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1988_ = v_a_1981_;
v_isShared_1989_ = v_isSharedCheck_1997_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_snd_1986_);
lean_inc(v_fst_1985_);
lean_dec(v_a_1981_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1997_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1990_, 0, v_item_1958_);
lean_ctor_set(v___x_1990_, 1, v_fromRanges_1959_);
lean_ctor_set(v___x_1990_, 2, v_snd_1986_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v_fst_1985_);
lean_ctor_set(v___x_1988_, 0, v___x_1990_);
v___x_1992_ = v___x_1988_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_fst_1985_);
v___x_1992_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1994_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1992_);
v___x_1994_ = v___x_1983_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v_fromRanges_1959_);
lean_dec_ref(v_item_1958_);
v_a_1999_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1980_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1980_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
v___jp_2007_:
{
lean_object* v_result_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v_result_2009_ = lean_ctor_get(v_a_1971_, 1);
lean_inc(v_result_2009_);
lean_dec(v_a_1971_);
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = lean_nat_add(v_requestNo_1957_, v___x_2010_);
lean_dec(v_requestNo_1957_);
if (lean_obj_tag(v_result_2009_) == 0)
{
lean_object* v___x_2012_; 
v___x_2012_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2));
v___y_1973_ = v___y_2008_;
v___y_1974_ = v___x_2011_;
v___y_1975_ = v___x_2012_;
goto v___jp_1972_;
}
else
{
lean_object* v_val_2013_; 
v_val_2013_ = lean_ctor_get(v_result_2009_, 0);
lean_inc(v_val_2013_);
lean_dec_ref_known(v_result_2009_, 1);
v___y_1973_ = v___y_2008_;
v___y_1974_ = v___x_2011_;
v___y_1975_ = v_val_2013_;
goto v___jp_1972_;
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_visited_1960_);
lean_dec_ref(v_fromRanges_1959_);
lean_dec_ref(v_item_1958_);
lean_dec(v_requestNo_1957_);
v_a_2016_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1970_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1970_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref_known(v___x_1966_, 1);
lean_dec(v_visited_1960_);
lean_dec_ref(v_fromRanges_1959_);
lean_dec_ref(v_item_1958_);
lean_dec(v_requestNo_1957_);
v_a_2024_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1969_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_1969_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec(v_visited_1960_);
lean_dec_ref(v_fromRanges_1959_);
v___x_2032_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2033_, 0, v_item_1958_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
lean_ctor_set(v___x_2033_, 2, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v_requestNo_1957_);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
return v___x_2035_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestNo_1957_ = stack[0].m_obj;
lean_object* v_item_1958_ = stack[1].m_obj;
lean_object* v_fromRanges_1959_ = stack[2].m_obj;
lean_object* v_visited_1960_ = stack[3].m_obj;
lean_object* v_a_1961_ = stack[4].m_obj;
lean_object* v_res_2036_;
v_res_2036_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_requestNo_1957_, v_item_1958_, v_fromRanges_1959_, v_visited_1960_, v_a_1961_);
stack->m_obj
 = v_res_2036_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(lean_object* v___x_2037_, lean_object* v_as_2038_, size_t v_sz_2039_, size_t v_i_2040_, lean_object* v_b_2041_, lean_object* v___y_2042_){
_start:
{
uint8_t v___x_2044_; 
v___x_2044_ = lean_usize_dec_lt(v_i_2040_, v_sz_2039_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; 
lean_dec(v___x_2037_);
v___x_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2045_, 0, v_b_2041_);
return v___x_2045_;
}
else
{
lean_object* v_fst_2046_; lean_object* v_snd_2047_; lean_object* v_a_2048_; lean_object* v_from_2049_; lean_object* v_fromRanges_2050_; lean_object* v___x_2051_; 
v_fst_2046_ = lean_ctor_get(v_b_2041_, 0);
lean_inc(v_fst_2046_);
v_snd_2047_ = lean_ctor_get(v_b_2041_, 1);
lean_inc(v_snd_2047_);
lean_dec_ref(v_b_2041_);
v_a_2048_ = lean_array_uget_borrowed(v_as_2038_, v_i_2040_);
v_from_2049_ = lean_ctor_get(v_a_2048_, 0);
v_fromRanges_2050_ = lean_ctor_get(v_a_2048_, 1);
lean_inc(v___x_2037_);
lean_inc_ref(v_fromRanges_2050_);
lean_inc_ref(v_from_2049_);
v___x_2051_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2046_, v_from_2049_, v_fromRanges_2050_, v___x_2037_, v___y_2042_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v_fst_2053_; lean_object* v_snd_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2065_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v_fst_2053_ = lean_ctor_get(v_a_2052_, 0);
v_snd_2054_ = lean_ctor_get(v_a_2052_, 1);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_a_2052_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2056_ = v_a_2052_;
v_isShared_2057_ = v_isSharedCheck_2065_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_snd_2054_);
lean_inc(v_fst_2053_);
lean_dec(v_a_2052_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2065_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = lean_array_push(v_snd_2047_, v_fst_2053_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v___x_2058_);
lean_ctor_set(v___x_2056_, 0, v_snd_2054_);
v___x_2060_ = v___x_2056_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_snd_2054_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
size_t v___x_2061_; size_t v___x_2062_; 
v___x_2061_ = ((size_t)1ULL);
v___x_2062_ = lean_usize_add(v_i_2040_, v___x_2061_);
v_i_2040_ = v___x_2062_;
v_b_2041_ = v___x_2060_;
goto _start;
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_snd_2047_);
lean_dec(v___x_2037_);
v_a_2066_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2051_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2051_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2037_ = stack[0].m_obj;
lean_object* v_as_2038_ = stack[1].m_obj;
size_t v_sz_2039_ = stack[2].m_num;
size_t v_i_2040_ = stack[3].m_num;
lean_object* v_b_2041_ = stack[4].m_obj;
lean_object* v___y_2042_ = stack[5].m_obj;
lean_object* v_res_2074_;
v_res_2074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___x_2037_, v_as_2038_, v_sz_2039_, v_i_2040_, v_b_2041_, v___y_2042_);
stack->m_obj
 = v_res_2074_;
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
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(lean_object* v_00_u03b2_2092_, lean_object* v_k_2093_, lean_object* v_t_2094_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_2093_, v_t_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2093_ = stack[1].m_obj;
lean_object* v_t_2094_ = stack[2].m_obj;
uint8_t v_res_2096_;
v_res_2096_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(lean_box(0), v_k_2093_, v_t_2094_);
stack->m_num = v_res_2096_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___boxed(lean_object* v_00_u03b2_2097_, lean_object* v_k_2098_, lean_object* v_t_2099_){
_start:
{
uint8_t v_res_2100_; lean_object* v_r_2101_; 
v_res_2100_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(v_00_u03b2_2097_, v_k_2098_, v_t_2099_);
lean_dec(v_t_2099_);
lean_dec_ref(v_k_2098_);
v_r_2101_ = lean_box(v_res_2100_);
return v_r_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4(lean_object* v_00_u03b2_2102_, lean_object* v_k_2103_, lean_object* v_v_2104_, lean_object* v_t_2105_, lean_object* v_hl_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_2103_, v_v_2104_, v_t_2105_);
return v___x_2107_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2108_, size_t v_i_2109_, lean_object* v_bs_2110_){
_start:
{
uint8_t v___x_2111_; 
v___x_2111_ = lean_usize_dec_lt(v_i_2109_, v_sz_2108_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_bs_2110_);
return v___x_2112_;
}
else
{
lean_object* v_v_2113_; lean_object* v___x_2114_; 
v_v_2113_ = lean_array_uget_borrowed(v_bs_2110_, v_i_2109_);
lean_inc(v_v_2113_);
v___x_2114_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v_v_2113_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v_bs_2110_);
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v_bs_x27_2125_; size_t v___x_2126_; size_t v___x_2127_; lean_object* v___x_2128_; 
v_a_2123_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2124_ = lean_unsigned_to_nat(0u);
v_bs_x27_2125_ = lean_array_uset(v_bs_2110_, v_i_2109_, v___x_2124_);
v___x_2126_ = ((size_t)1ULL);
v___x_2127_ = lean_usize_add(v_i_2109_, v___x_2126_);
v___x_2128_ = lean_array_uset(v_bs_x27_2125_, v_i_2109_, v_a_2123_);
v_i_2109_ = v___x_2127_;
v_bs_2110_ = v___x_2128_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2108_ = stack[0].m_num;
size_t v_i_2109_ = stack[1].m_num;
lean_object* v_bs_2110_ = stack[2].m_obj;
lean_object* v_res_2130_;
v_res_2130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_2108_, v_i_2109_, v_bs_2110_);
stack->m_obj
 = v_res_2130_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2131_, lean_object* v_i_2132_, lean_object* v_bs_2133_){
_start:
{
size_t v_sz_boxed_2134_; size_t v_i_boxed_2135_; lean_object* v_res_2136_; 
v_sz_boxed_2134_ = lean_unbox_usize(v_sz_2131_);
lean_dec(v_sz_2131_);
v_i_boxed_2135_ = lean_unbox_usize(v_i_2132_);
lean_dec(v_i_2132_);
v_res_2136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2134_, v_i_boxed_2135_, v_bs_2133_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(lean_object* v_x_2137_){
_start:
{
if (lean_obj_tag(v_x_2137_) == 4)
{
lean_object* v_elems_2138_; size_t v_sz_2139_; size_t v___x_2140_; lean_object* v___x_2141_; 
v_elems_2138_ = lean_ctor_get(v_x_2137_, 0);
lean_inc_ref(v_elems_2138_);
lean_dec_ref_known(v_x_2137_, 1);
v_sz_2139_ = lean_array_size(v_elems_2138_);
v___x_2140_ = ((size_t)0ULL);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_2139_, v___x_2140_, v_elems_2138_);
return v___x_2141_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2142_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2143_ = lean_unsigned_to_nat(80u);
v___x_2144_ = l_Lean_Json_pretty(v_x_2137_, v___x_2143_);
v___x_2145_ = lean_string_append(v___x_2142_, v___x_2144_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2147_ = lean_string_append(v___x_2145_, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
return v___x_2148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(lean_object* v_x_2151_){
_start:
{
if (lean_obj_tag(v_x_2151_) == 0)
{
lean_object* v___x_2152_; 
v___x_2152_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0));
return v___x_2152_;
}
else
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(v_x_2151_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2170_; 
v_a_2162_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2164_ = v___x_2153_;
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2153_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v_a_2162_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2166_);
v___x_2168_ = v___x_2164_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(lean_object* v_expectedID_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_Lsp_Ipc_stdout(v_a_2172_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2318_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2318_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2318_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_2175_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2309_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2309_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2309_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___y_2185_; lean_object* v___y_2186_; 
switch(lean_obj_tag(v_a_2180_))
{
case 2:
{
lean_object* v_id_2192_; lean_object* v_result_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2237_; 
v_id_2192_ = lean_ctor_get(v_a_2180_, 0);
v_result_2193_ = lean_ctor_get(v_a_2180_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_a_2180_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2195_ = v_a_2180_;
v_isShared_2196_ = v_isSharedCheck_2237_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_result_2193_);
lean_inc(v_id_2192_);
lean_dec(v_a_2180_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2237_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
uint8_t v___x_2197_; 
v___x_2197_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2192_, v_expectedID_2171_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v___y_2200_; 
lean_del_object(v___x_2195_);
lean_dec(v_result_2193_);
lean_del_object(v___x_2177_);
v___x_2198_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2171_))
{
case 0:
{
lean_object* v_s_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_s_2211_ = lean_ctor_get(v_expectedID_2171_, 0);
lean_inc_ref(v_s_2211_);
lean_dec_ref_known(v_expectedID_2171_, 1);
v___x_2212_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2213_ = lean_string_append(v___x_2212_, v_s_2211_);
lean_dec_ref(v_s_2211_);
v___x_2214_ = lean_string_append(v___x_2213_, v___x_2212_);
v___y_2200_ = v___x_2214_;
goto v___jp_2199_;
}
case 1:
{
lean_object* v_n_2215_; lean_object* v___x_2216_; 
v_n_2215_ = lean_ctor_get(v_expectedID_2171_, 0);
lean_inc_ref(v_n_2215_);
lean_dec_ref_known(v_expectedID_2171_, 1);
v___x_2216_ = l_Lean_JsonNumber_toString(v_n_2215_);
v___y_2200_ = v___x_2216_;
goto v___jp_2199_;
}
default: 
{
lean_object* v___x_2217_; 
v___x_2217_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2200_ = v___x_2217_;
goto v___jp_2199_;
}
}
v___jp_2199_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = lean_string_append(v___x_2198_, v___y_2200_);
lean_dec_ref(v___y_2200_);
v___x_2202_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2203_ = lean_string_append(v___x_2201_, v___x_2202_);
switch(lean_obj_tag(v_id_2192_))
{
case 0:
{
lean_object* v_s_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v_s_2204_ = lean_ctor_get(v_id_2192_, 0);
lean_inc_ref(v_s_2204_);
lean_dec_ref_known(v_id_2192_, 1);
v___x_2205_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2206_ = lean_string_append(v___x_2205_, v_s_2204_);
lean_dec_ref(v_s_2204_);
v___x_2207_ = lean_string_append(v___x_2206_, v___x_2205_);
v___y_2185_ = v___x_2203_;
v___y_2186_ = v___x_2207_;
goto v___jp_2184_;
}
case 1:
{
lean_object* v_n_2208_; lean_object* v___x_2209_; 
v_n_2208_ = lean_ctor_get(v_id_2192_, 0);
lean_inc_ref(v_n_2208_);
lean_dec_ref_known(v_id_2192_, 1);
v___x_2209_ = l_Lean_JsonNumber_toString(v_n_2208_);
v___y_2185_ = v___x_2203_;
v___y_2186_ = v___x_2209_;
goto v___jp_2184_;
}
default: 
{
lean_object* v___x_2210_; 
v___x_2210_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2185_ = v___x_2203_;
v___y_2186_ = v___x_2210_;
goto v___jp_2184_;
}
}
}
}
else
{
lean_object* v___x_2218_; 
lean_dec(v_id_2192_);
lean_del_object(v___x_2182_);
lean_inc(v_result_2193_);
v___x_2218_ = l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(v_result_2193_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
lean_del_object(v___x_2195_);
lean_dec(v_expectedID_2171_);
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___x_2220_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2221_ = l_Lean_Json_compress(v_result_2193_);
v___x_2222_ = lean_string_append(v___x_2220_, v___x_2221_);
lean_dec_ref(v___x_2221_);
v___x_2223_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2224_ = lean_string_append(v___x_2222_, v___x_2223_);
v___x_2225_ = lean_string_append(v___x_2224_, v_a_2219_);
lean_dec(v_a_2219_);
v___x_2226_ = lean_mk_io_user_error(v___x_2225_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set_tag(v___x_2177_, 1);
lean_ctor_set(v___x_2177_, 0, v___x_2226_);
v___x_2228_ = v___x_2177_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; 
lean_dec(v_result_2193_);
v_a_2230_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2218_, 1);
if (v_isShared_2196_ == 0)
{
lean_ctor_set_tag(v___x_2195_, 0);
lean_ctor_set(v___x_2195_, 1, v_a_2230_);
lean_ctor_set(v___x_2195_, 0, v_expectedID_2171_);
v___x_2232_ = v___x_2195_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_expectedID_2171_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_a_2230_);
v___x_2232_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2234_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2232_);
v___x_2234_ = v___x_2177_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2238_; uint8_t v_code_2239_; lean_object* v_message_2240_; lean_object* v_data_x3f_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___x_2273_; lean_object* v___y_2275_; 
lean_del_object(v___x_2182_);
lean_dec(v_expectedID_2171_);
v_id_2238_ = lean_ctor_get(v_a_2180_, 0);
lean_inc(v_id_2238_);
v_code_2239_ = lean_ctor_get_uint8(v_a_2180_, sizeof(void*)*3);
v_message_2240_ = lean_ctor_get(v_a_2180_, 1);
lean_inc_ref(v_message_2240_);
v_data_x3f_2241_ = lean_ctor_get(v_a_2180_, 2);
lean_inc(v_data_x3f_2241_);
lean_dec_ref_known(v_a_2180_, 3);
v___x_2242_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2243_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2273_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2238_))
{
case 0:
{
lean_object* v_s_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
v_s_2291_ = lean_ctor_get(v_id_2238_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_id_2238_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v_id_2238_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_s_2291_);
lean_dec(v_id_2238_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set_tag(v___x_2293_, 3);
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_s_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
v___y_2275_ = v___x_2296_;
goto v___jp_2274_;
}
}
}
case 1:
{
lean_object* v_n_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
v_n_2299_ = lean_ctor_get(v_id_2238_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_id_2238_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v_id_2238_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_n_2299_);
lean_dec(v_id_2238_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 2);
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_n_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
v___y_2275_ = v___x_2304_;
goto v___jp_2274_;
}
}
}
default: 
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_box(0);
v___y_2275_ = v___x_2307_;
goto v___jp_2274_;
}
}
v___jp_2244_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
lean_inc(v___y_2248_);
lean_inc_ref(v___y_2247_);
v___x_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___y_2247_);
lean_ctor_set(v___x_2249_, 1, v___y_2248_);
v___x_2250_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2251_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_message_2240_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = lean_box(0);
v___x_2254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2249_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2257_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2256_, v_data_x3f_2241_);
lean_dec(v_data_x3f_2241_);
v___x_2258_ = l_List_appendTR___redArg(v___x_2255_, v___x_2257_);
v___x_2259_ = l_Lean_Json_mkObj(v___x_2258_);
lean_dec(v___x_2258_);
lean_inc_ref(v___y_2245_);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___y_2245_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v___x_2253_);
v___x_2262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___y_2246_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2243_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = l_Lean_Json_mkObj(v___x_2263_);
lean_dec_ref_known(v___x_2263_, 2);
v___x_2265_ = l_Lean_Json_compress(v___x_2264_);
v___x_2266_ = lean_string_append(v___x_2242_, v___x_2265_);
lean_dec_ref(v___x_2265_);
v___x_2267_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2268_ = lean_string_append(v___x_2266_, v___x_2267_);
v___x_2269_ = lean_mk_io_user_error(v___x_2268_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set_tag(v___x_2177_, 1);
lean_ctor_set(v___x_2177_, 0, v___x_2269_);
v___x_2271_ = v___x_2177_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
v___jp_2274_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2273_);
lean_ctor_set(v___x_2276_, 1, v___y_2275_);
v___x_2277_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2278_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2239_)
{
case 0:
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2279_;
goto v___jp_2244_;
}
case 1:
{
lean_object* v___x_2280_; 
v___x_2280_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2280_;
goto v___jp_2244_;
}
case 2:
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2281_;
goto v___jp_2244_;
}
case 3:
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2282_;
goto v___jp_2244_;
}
case 4:
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2283_;
goto v___jp_2244_;
}
case 5:
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2284_;
goto v___jp_2244_;
}
case 6:
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2285_;
goto v___jp_2244_;
}
case 7:
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2286_;
goto v___jp_2244_;
}
case 8:
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2287_;
goto v___jp_2244_;
}
case 9:
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2288_;
goto v___jp_2244_;
}
case 10:
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2289_;
goto v___jp_2244_;
}
default: 
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2245_ = v___x_2277_;
v___y_2246_ = v___x_2276_;
v___y_2247_ = v___x_2278_;
v___y_2248_ = v___x_2290_;
goto v___jp_2244_;
}
}
}
}
default: 
{
lean_del_object(v___x_2182_);
lean_dec(v_a_2180_);
lean_del_object(v___x_2177_);
goto _start;
}
}
v___jp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2187_ = lean_string_append(v___y_2185_, v___y_2186_);
lean_dec_ref(v___y_2186_);
v___x_2188_ = lean_mk_io_user_error(v___x_2187_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 1);
lean_ctor_set(v___x_2182_, 0, v___x_2188_);
v___x_2190_ = v___x_2182_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
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
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_del_object(v___x_2177_);
lean_dec(v_expectedID_2171_);
v_a_2310_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2179_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2179_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_expectedID_2171_);
v_a_2319_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2174_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2174_);
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
LEAN_EXPORT void l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedID_2171_ = stack[0].m_obj;
lean_object* v_a_2172_ = stack[1].m_obj;
lean_object* v_res_2327_;
v_res_2327_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v_expectedID_2171_, v_a_2172_);
stack->m_obj
 = v_res_2327_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1___boxed(lean_object* v_expectedID_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v_expectedID_2328_, v_a_2329_);
lean_dec_ref(v_a_2329_);
return v_res_2331_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(lean_object* v_as_2332_, size_t v_sz_2333_, size_t v_i_2334_, lean_object* v_b_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v___x_2338_; 
v___x_2338_ = lean_usize_dec_lt(v_i_2334_, v_sz_2333_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; 
v___x_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2339_, 0, v_b_2335_);
return v___x_2339_;
}
else
{
lean_object* v_fst_2340_; lean_object* v_snd_2341_; lean_object* v_a_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_fst_2340_ = lean_ctor_get(v_b_2335_, 0);
lean_inc(v_fst_2340_);
v_snd_2341_ = lean_ctor_get(v_b_2335_, 1);
lean_inc(v_snd_2341_);
lean_dec_ref(v_b_2335_);
v_a_2342_ = lean_array_uget_borrowed(v_as_2332_, v_i_2334_);
v___x_2343_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2344_ = lean_box(1);
lean_inc(v_a_2342_);
v___x_2345_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2340_, v_a_2342_, v___x_2343_, v___x_2344_, v___y_2336_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v_fst_2347_; lean_object* v_snd_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2359_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v_fst_2347_ = lean_ctor_get(v_a_2346_, 0);
v_snd_2348_ = lean_ctor_get(v_a_2346_, 1);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_a_2346_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2350_ = v_a_2346_;
v_isShared_2351_ = v_isSharedCheck_2359_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_snd_2348_);
lean_inc(v_fst_2347_);
lean_dec(v_a_2346_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2359_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2352_ = lean_array_push(v_snd_2341_, v_fst_2347_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 1, v___x_2352_);
lean_ctor_set(v___x_2350_, 0, v_snd_2348_);
v___x_2354_ = v___x_2350_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_snd_2348_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
size_t v___x_2355_; size_t v___x_2356_; 
v___x_2355_ = ((size_t)1ULL);
v___x_2356_ = lean_usize_add(v_i_2334_, v___x_2355_);
v_i_2334_ = v___x_2356_;
v_b_2335_ = v___x_2354_;
goto _start;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_snd_2341_);
v_a_2360_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2345_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2345_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2332_ = stack[0].m_obj;
size_t v_sz_2333_ = stack[1].m_num;
size_t v_i_2334_ = stack[2].m_num;
lean_object* v_b_2335_ = stack[3].m_obj;
lean_object* v___y_2336_ = stack[4].m_obj;
lean_object* v_res_2368_;
v_res_2368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v_as_2332_, v_sz_2333_, v_i_2334_, v_b_2335_, v___y_2336_);
stack->m_obj
 = v_res_2368_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2___boxed(lean_object* v_as_2369_, lean_object* v_sz_2370_, lean_object* v_i_2371_, lean_object* v_b_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
size_t v_sz_boxed_2375_; size_t v_i_boxed_2376_; lean_object* v_res_2377_; 
v_sz_boxed_2375_ = lean_unbox_usize(v_sz_2370_);
lean_dec(v_sz_2370_);
v_i_boxed_2376_ = lean_unbox_usize(v_i_2371_);
lean_dec(v_i_2371_);
v_res_2377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v_as_2369_, v_sz_boxed_2375_, v_i_boxed_2376_, v_b_2372_, v___y_2373_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v_as_2369_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(lean_object* v_v_2378_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = l_Lean_Lsp_instToJsonCallHierarchyPrepareParams_toJson(v_v_2378_);
v___x_2380_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2379_);
return v___x_2380_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(lean_object* v_h_2381_, lean_object* v_r_2382_){
_start:
{
lean_object* v_id_2384_; lean_object* v_method_2385_; lean_object* v_param_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2406_; 
v_id_2384_ = lean_ctor_get(v_r_2382_, 0);
v_method_2385_ = lean_ctor_get(v_r_2382_, 1);
v_param_2386_ = lean_ctor_get(v_r_2382_, 2);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_r_2382_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2388_ = v_r_2382_;
v_isShared_2389_ = v_isSharedCheck_2406_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_param_2386_);
lean_inc(v_method_2385_);
lean_inc(v_id_2384_);
lean_dec(v_r_2382_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2406_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___y_2391_; lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(v_param_2386_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v___x_2397_; 
lean_dec_ref_known(v___x_2396_, 1);
v___x_2397_ = lean_box(0);
v___y_2391_ = v___x_2397_;
goto v___jp_2390_;
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
v_a_2398_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2396_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2396_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
v___y_2391_ = v___x_2403_;
goto v___jp_2390_;
}
}
}
v___jp_2390_:
{
lean_object* v___x_2393_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 2, v___y_2391_);
v___x_2393_ = v___x_2388_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_id_2384_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_method_2385_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v___y_2391_);
v___x_2393_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_2381_, v___x_2393_);
return v___x_2394_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2381_ = stack[0].m_obj;
lean_object* v_r_2382_ = stack[1].m_obj;
lean_object* v_res_2407_;
v_res_2407_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_h_2381_, v_r_2382_);
stack->m_obj
 = v_res_2407_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0___boxed(lean_object* v_h_2408_, lean_object* v_r_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_h_2408_, v_r_2409_);
return v_res_2411_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(lean_object* v_r_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v_a_2416_; lean_object* v___x_2417_; 
v___x_2415_ = l_Lean_Lsp_Ipc_stdin(v_a_2413_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref(v___x_2415_);
v___x_2417_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_a_2416_, v_r_2412_);
return v___x_2417_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_2412_ = stack[0].m_obj;
lean_object* v_a_2413_ = stack[1].m_obj;
lean_object* v_res_2418_;
v_res_2418_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v_r_2412_, v_a_2413_);
stack->m_obj
 = v_res_2418_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0___boxed(lean_object* v_r_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v_r_2419_, v_a_2420_);
lean_dec_ref(v_a_2420_);
return v_res_2422_;
}
}
lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(lean_object* v_requestNo_2426_, lean_object* v_uri_2427_, lean_object* v_pos_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_inc(v_requestNo_2426_);
v___x_2431_ = l_Lean_JsonNumber_fromNat(v_requestNo_2426_);
v___x_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
v___x_2433_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_uri_2427_);
lean_ctor_set(v___x_2434_, 1, v_pos_2428_);
lean_inc_ref(v___x_2432_);
v___x_2435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2432_);
lean_ctor_set(v___x_2435_, 1, v___x_2433_);
lean_ctor_set(v___x_2435_, 2, v___x_2434_);
v___x_2436_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2435_, v_a_2429_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2437_; 
lean_dec_ref_known(v___x_2436_, 1);
v___x_2437_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2432_, v_a_2429_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v_result_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2481_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v_result_2439_ = lean_ctor_get(v_a_2438_, 1);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_a_2438_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v_a_2438_, 0);
lean_dec(v_unused_2482_);
v___x_2441_ = v_a_2438_;
v_isShared_2442_ = v_isSharedCheck_2481_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_result_2439_);
lean_dec(v_a_2438_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2481_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___y_2446_; 
v___x_2443_ = lean_unsigned_to_nat(1u);
v___x_2444_ = lean_nat_add(v_requestNo_2426_, v___x_2443_);
lean_dec(v_requestNo_2426_);
if (lean_obj_tag(v_result_2439_) == 0)
{
lean_object* v___x_2479_; 
v___x_2479_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2446_ = v___x_2479_;
goto v___jp_2445_;
}
else
{
lean_object* v_val_2480_; 
v_val_2480_ = lean_ctor_get(v_result_2439_, 0);
lean_inc(v_val_2480_);
lean_dec_ref_known(v_result_2439_, 1);
v___y_2446_ = v_val_2480_;
goto v___jp_2445_;
}
v___jp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 1, v___x_2447_);
lean_ctor_set(v___x_2441_, 0, v___x_2444_);
v___x_2449_ = v___x_2441_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
size_t v_sz_2450_; size_t v___x_2451_; lean_object* v___x_2452_; 
v_sz_2450_ = lean_array_size(v___y_2446_);
v___x_2451_ = ((size_t)0ULL);
v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v___y_2446_, v_sz_2450_, v___x_2451_, v___x_2449_, v_a_2429_);
lean_dec_ref(v___y_2446_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2469_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2469_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2469_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_fst_2457_; lean_object* v_snd_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2468_; 
v_fst_2457_ = lean_ctor_get(v_a_2453_, 0);
v_snd_2458_ = lean_ctor_get(v_a_2453_, 1);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_a_2453_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2460_ = v_a_2453_;
v_isShared_2461_ = v_isSharedCheck_2468_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_snd_2458_);
lean_inc(v_fst_2457_);
lean_dec(v_a_2453_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2468_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 1, v_fst_2457_);
lean_ctor_set(v___x_2460_, 0, v_snd_2458_);
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_snd_2458_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_fst_2457_);
v___x_2463_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2465_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2463_);
v___x_2465_ = v___x_2455_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
v_a_2470_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2452_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2452_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_requestNo_2426_);
v_a_2483_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2437_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2437_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref_known(v___x_2432_, 1);
lean_dec(v_requestNo_2426_);
v_a_2491_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2436_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2436_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_expandIncomingCallHierarchy_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestNo_2426_ = stack[0].m_obj;
lean_object* v_uri_2427_ = stack[1].m_obj;
lean_object* v_pos_2428_ = stack[2].m_obj;
lean_object* v_a_2429_ = stack[3].m_obj;
lean_object* v_res_2499_;
v_res_2499_ = l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(v_requestNo_2426_, v_uri_2427_, v_pos_2428_, v_a_2429_);
stack->m_obj
 = v_res_2499_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___boxed(lean_object* v_requestNo_2500_, lean_object* v_uri_2501_, lean_object* v_pos_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(v_requestNo_2500_, v_uri_2501_, v_pos_2502_, v_a_2503_);
lean_dec_ref(v_a_2503_);
return v_res_2505_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2506_, size_t v_i_2507_, lean_object* v_bs_2508_){
_start:
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_usize_dec_lt(v_i_2507_, v_sz_2506_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_bs_2508_);
return v___x_2510_;
}
else
{
lean_object* v_v_2511_; lean_object* v___x_2512_; 
v_v_2511_ = lean_array_uget_borrowed(v_bs_2508_, v_i_2507_);
lean_inc(v_v_2511_);
v___x_2512_ = l_Lean_Lsp_instFromJsonCallHierarchyOutgoingCall_fromJson(v_v_2511_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v_bs_2508_);
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2522_; lean_object* v_bs_x27_2523_; size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
v_a_2521_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2512_, 1);
v___x_2522_ = lean_unsigned_to_nat(0u);
v_bs_x27_2523_ = lean_array_uset(v_bs_2508_, v_i_2507_, v___x_2522_);
v___x_2524_ = ((size_t)1ULL);
v___x_2525_ = lean_usize_add(v_i_2507_, v___x_2524_);
v___x_2526_ = lean_array_uset(v_bs_x27_2523_, v_i_2507_, v_a_2521_);
v_i_2507_ = v___x_2525_;
v_bs_2508_ = v___x_2526_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2506_ = stack[0].m_num;
size_t v_i_2507_ = stack[1].m_num;
lean_object* v_bs_2508_ = stack[2].m_obj;
lean_object* v_res_2528_;
v_res_2528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_2506_, v_i_2507_, v_bs_2508_);
stack->m_obj
 = v_res_2528_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2529_, lean_object* v_i_2530_, lean_object* v_bs_2531_){
_start:
{
size_t v_sz_boxed_2532_; size_t v_i_boxed_2533_; lean_object* v_res_2534_; 
v_sz_boxed_2532_ = lean_unbox_usize(v_sz_2529_);
lean_dec(v_sz_2529_);
v_i_boxed_2533_ = lean_unbox_usize(v_i_2530_);
lean_dec(v_i_2530_);
v_res_2534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2532_, v_i_boxed_2533_, v_bs_2531_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(lean_object* v_x_2535_){
_start:
{
if (lean_obj_tag(v_x_2535_) == 4)
{
lean_object* v_elems_2536_; size_t v_sz_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
v_elems_2536_ = lean_ctor_get(v_x_2535_, 0);
lean_inc_ref(v_elems_2536_);
lean_dec_ref_known(v_x_2535_, 1);
v_sz_2537_ = lean_array_size(v_elems_2536_);
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_2537_, v___x_2538_, v_elems_2536_);
return v___x_2539_;
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2540_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2541_ = lean_unsigned_to_nat(80u);
v___x_2542_ = l_Lean_Json_pretty(v_x_2535_, v___x_2541_);
v___x_2543_ = lean_string_append(v___x_2540_, v___x_2542_);
lean_dec_ref(v___x_2542_);
v___x_2544_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2545_ = lean_string_append(v___x_2543_, v___x_2544_);
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(lean_object* v_x_2549_){
_start:
{
if (lean_obj_tag(v_x_2549_) == 0)
{
lean_object* v___x_2550_; 
v___x_2550_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0));
return v___x_2550_;
}
else
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(v_x_2549_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2568_; 
v_a_2560_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2562_ = v___x_2551_;
v_isShared_2563_ = v_isSharedCheck_2568_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2551_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2568_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_a_2560_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___x_2564_);
v___x_2566_ = v___x_2562_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
}
lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(lean_object* v_expectedID_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_Lsp_Ipc_stdout(v_a_2570_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2716_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2716_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2716_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_2573_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2707_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2707_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2707_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___y_2583_; lean_object* v___y_2584_; 
switch(lean_obj_tag(v_a_2578_))
{
case 2:
{
lean_object* v_id_2590_; lean_object* v_result_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2635_; 
v_id_2590_ = lean_ctor_get(v_a_2578_, 0);
v_result_2591_ = lean_ctor_get(v_a_2578_, 1);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_a_2578_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2593_ = v_a_2578_;
v_isShared_2594_ = v_isSharedCheck_2635_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_result_2591_);
lean_inc(v_id_2590_);
lean_dec(v_a_2578_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2635_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
uint8_t v___x_2595_; 
v___x_2595_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2590_, v_expectedID_2569_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v___y_2598_; 
lean_del_object(v___x_2593_);
lean_dec(v_result_2591_);
lean_del_object(v___x_2575_);
v___x_2596_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2569_))
{
case 0:
{
lean_object* v_s_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_s_2609_ = lean_ctor_get(v_expectedID_2569_, 0);
lean_inc_ref(v_s_2609_);
lean_dec_ref_known(v_expectedID_2569_, 1);
v___x_2610_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2611_ = lean_string_append(v___x_2610_, v_s_2609_);
lean_dec_ref(v_s_2609_);
v___x_2612_ = lean_string_append(v___x_2611_, v___x_2610_);
v___y_2598_ = v___x_2612_;
goto v___jp_2597_;
}
case 1:
{
lean_object* v_n_2613_; lean_object* v___x_2614_; 
v_n_2613_ = lean_ctor_get(v_expectedID_2569_, 0);
lean_inc_ref(v_n_2613_);
lean_dec_ref_known(v_expectedID_2569_, 1);
v___x_2614_ = l_Lean_JsonNumber_toString(v_n_2613_);
v___y_2598_ = v___x_2614_;
goto v___jp_2597_;
}
default: 
{
lean_object* v___x_2615_; 
v___x_2615_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2598_ = v___x_2615_;
goto v___jp_2597_;
}
}
v___jp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = lean_string_append(v___x_2596_, v___y_2598_);
lean_dec_ref(v___y_2598_);
v___x_2600_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2601_ = lean_string_append(v___x_2599_, v___x_2600_);
switch(lean_obj_tag(v_id_2590_))
{
case 0:
{
lean_object* v_s_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v_s_2602_ = lean_ctor_get(v_id_2590_, 0);
lean_inc_ref(v_s_2602_);
lean_dec_ref_known(v_id_2590_, 1);
v___x_2603_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2604_ = lean_string_append(v___x_2603_, v_s_2602_);
lean_dec_ref(v_s_2602_);
v___x_2605_ = lean_string_append(v___x_2604_, v___x_2603_);
v___y_2583_ = v___x_2601_;
v___y_2584_ = v___x_2605_;
goto v___jp_2582_;
}
case 1:
{
lean_object* v_n_2606_; lean_object* v___x_2607_; 
v_n_2606_ = lean_ctor_get(v_id_2590_, 0);
lean_inc_ref(v_n_2606_);
lean_dec_ref_known(v_id_2590_, 1);
v___x_2607_ = l_Lean_JsonNumber_toString(v_n_2606_);
v___y_2583_ = v___x_2601_;
v___y_2584_ = v___x_2607_;
goto v___jp_2582_;
}
default: 
{
lean_object* v___x_2608_; 
v___x_2608_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2583_ = v___x_2601_;
v___y_2584_ = v___x_2608_;
goto v___jp_2582_;
}
}
}
}
else
{
lean_object* v___x_2616_; 
lean_dec(v_id_2590_);
lean_del_object(v___x_2580_);
lean_inc(v_result_2591_);
v___x_2616_ = l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(v_result_2591_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
lean_del_object(v___x_2593_);
lean_dec(v_expectedID_2569_);
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2619_ = l_Lean_Json_compress(v_result_2591_);
v___x_2620_ = lean_string_append(v___x_2618_, v___x_2619_);
lean_dec_ref(v___x_2619_);
v___x_2621_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2622_ = lean_string_append(v___x_2620_, v___x_2621_);
v___x_2623_ = lean_string_append(v___x_2622_, v_a_2617_);
lean_dec(v_a_2617_);
v___x_2624_ = lean_mk_io_user_error(v___x_2623_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set_tag(v___x_2575_, 1);
lean_ctor_set(v___x_2575_, 0, v___x_2624_);
v___x_2626_ = v___x_2575_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; 
lean_dec(v_result_2591_);
v_a_2628_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2616_, 1);
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 0);
lean_ctor_set(v___x_2593_, 1, v_a_2628_);
lean_ctor_set(v___x_2593_, 0, v_expectedID_2569_);
v___x_2630_ = v___x_2593_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_expectedID_2569_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v_a_2628_);
v___x_2630_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2632_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2630_);
v___x_2632_ = v___x_2575_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2636_; uint8_t v_code_2637_; lean_object* v_message_2638_; lean_object* v_data_x3f_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___x_2671_; lean_object* v___y_2673_; 
lean_del_object(v___x_2580_);
lean_dec(v_expectedID_2569_);
v_id_2636_ = lean_ctor_get(v_a_2578_, 0);
lean_inc(v_id_2636_);
v_code_2637_ = lean_ctor_get_uint8(v_a_2578_, sizeof(void*)*3);
v_message_2638_ = lean_ctor_get(v_a_2578_, 1);
lean_inc_ref(v_message_2638_);
v_data_x3f_2639_ = lean_ctor_get(v_a_2578_, 2);
lean_inc(v_data_x3f_2639_);
lean_dec_ref_known(v_a_2578_, 3);
v___x_2640_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2641_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2671_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2636_))
{
case 0:
{
lean_object* v_s_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
v_s_2689_ = lean_ctor_get(v_id_2636_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_id_2636_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v_id_2636_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_s_2689_);
lean_dec(v_id_2636_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 3);
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_s_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
v___y_2673_ = v___x_2694_;
goto v___jp_2672_;
}
}
}
case 1:
{
lean_object* v_n_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
v_n_2697_ = lean_ctor_get(v_id_2636_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_id_2636_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v_id_2636_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_n_2697_);
lean_dec(v_id_2636_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
lean_ctor_set_tag(v___x_2699_, 2);
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_n_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
v___y_2673_ = v___x_2702_;
goto v___jp_2672_;
}
}
}
default: 
{
lean_object* v___x_2705_; 
v___x_2705_ = lean_box(0);
v___y_2673_ = v___x_2705_;
goto v___jp_2672_;
}
}
v___jp_2642_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
lean_inc(v___y_2646_);
lean_inc_ref(v___y_2644_);
v___x_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___y_2644_);
lean_ctor_set(v___x_2647_, 1, v___y_2646_);
v___x_2648_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_message_2638_);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2648_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = lean_box(0);
v___x_2652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2650_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2647_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2655_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2654_, v_data_x3f_2639_);
lean_dec(v_data_x3f_2639_);
v___x_2656_ = l_List_appendTR___redArg(v___x_2653_, v___x_2655_);
v___x_2657_ = l_Lean_Json_mkObj(v___x_2656_);
lean_dec(v___x_2656_);
lean_inc_ref(v___y_2645_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___y_2645_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___x_2659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_ctor_set(v___x_2659_, 1, v___x_2651_);
v___x_2660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___y_2643_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
v___x_2661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2641_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = l_Lean_Json_mkObj(v___x_2661_);
lean_dec_ref_known(v___x_2661_, 2);
v___x_2663_ = l_Lean_Json_compress(v___x_2662_);
v___x_2664_ = lean_string_append(v___x_2640_, v___x_2663_);
lean_dec_ref(v___x_2663_);
v___x_2665_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2666_ = lean_string_append(v___x_2664_, v___x_2665_);
v___x_2667_ = lean_mk_io_user_error(v___x_2666_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set_tag(v___x_2575_, 1);
lean_ctor_set(v___x_2575_, 0, v___x_2667_);
v___x_2669_ = v___x_2575_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
v___jp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2671_);
lean_ctor_set(v___x_2674_, 1, v___y_2673_);
v___x_2675_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2676_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2637_)
{
case 0:
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2677_;
goto v___jp_2642_;
}
case 1:
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2678_;
goto v___jp_2642_;
}
case 2:
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2679_;
goto v___jp_2642_;
}
case 3:
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2680_;
goto v___jp_2642_;
}
case 4:
{
lean_object* v___x_2681_; 
v___x_2681_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2681_;
goto v___jp_2642_;
}
case 5:
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2682_;
goto v___jp_2642_;
}
case 6:
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2683_;
goto v___jp_2642_;
}
case 7:
{
lean_object* v___x_2684_; 
v___x_2684_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2684_;
goto v___jp_2642_;
}
case 8:
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2685_;
goto v___jp_2642_;
}
case 9:
{
lean_object* v___x_2686_; 
v___x_2686_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2686_;
goto v___jp_2642_;
}
case 10:
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2687_;
goto v___jp_2642_;
}
default: 
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2643_ = v___x_2674_;
v___y_2644_ = v___x_2676_;
v___y_2645_ = v___x_2675_;
v___y_2646_ = v___x_2688_;
goto v___jp_2642_;
}
}
}
}
default: 
{
lean_del_object(v___x_2580_);
lean_dec(v_a_2578_);
lean_del_object(v___x_2575_);
goto _start;
}
}
v___jp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2585_ = lean_string_append(v___y_2583_, v___y_2584_);
lean_dec_ref(v___y_2584_);
v___x_2586_ = lean_mk_io_user_error(v___x_2585_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 1);
lean_ctor_set(v___x_2580_, 0, v___x_2586_);
v___x_2588_ = v___x_2580_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_del_object(v___x_2575_);
lean_dec(v_expectedID_2569_);
v_a_2708_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2577_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2577_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v_expectedID_2569_);
v_a_2717_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2572_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2572_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedID_2569_ = stack[0].m_obj;
lean_object* v_a_2570_ = stack[1].m_obj;
lean_object* v_res_2725_;
v_res_2725_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v_expectedID_2569_, v_a_2570_);
stack->m_obj
 = v_res_2725_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1___boxed(lean_object* v_expectedID_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v_expectedID_2726_, v_a_2727_);
lean_dec_ref(v_a_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(lean_object* v_v_2730_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = l_Lean_Lsp_instToJsonCallHierarchyOutgoingCallsParams_toJson(v_v_2730_);
v___x_2732_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2731_);
return v___x_2732_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(lean_object* v_h_2733_, lean_object* v_r_2734_){
_start:
{
lean_object* v_id_2736_; lean_object* v_method_2737_; lean_object* v_param_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2758_; 
v_id_2736_ = lean_ctor_get(v_r_2734_, 0);
v_method_2737_ = lean_ctor_get(v_r_2734_, 1);
v_param_2738_ = lean_ctor_get(v_r_2734_, 2);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_r_2734_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2740_ = v_r_2734_;
v_isShared_2741_ = v_isSharedCheck_2758_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_param_2738_);
lean_inc(v_method_2737_);
lean_inc(v_id_2736_);
lean_dec(v_r_2734_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2758_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___y_2743_; lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(v_param_2738_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v___x_2749_; 
lean_dec_ref_known(v___x_2748_, 1);
v___x_2749_ = lean_box(0);
v___y_2743_ = v___x_2749_;
goto v___jp_2742_;
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
v_a_2750_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2748_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2748_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
v___y_2743_ = v___x_2755_;
goto v___jp_2742_;
}
}
}
v___jp_2742_:
{
lean_object* v___x_2745_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 2, v___y_2743_);
v___x_2745_ = v___x_2740_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_id_2736_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_method_2737_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v___y_2743_);
v___x_2745_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_2733_, v___x_2745_);
return v___x_2746_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2733_ = stack[0].m_obj;
lean_object* v_r_2734_ = stack[1].m_obj;
lean_object* v_res_2759_;
v_res_2759_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_h_2733_, v_r_2734_);
stack->m_obj
 = v_res_2759_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0___boxed(lean_object* v_h_2760_, lean_object* v_r_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_h_2760_, v_r_2761_);
return v_res_2763_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(lean_object* v_r_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v___x_2767_; lean_object* v_a_2768_; lean_object* v___x_2769_; 
v___x_2767_ = l_Lean_Lsp_Ipc_stdin(v_a_2765_);
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref(v___x_2767_);
v___x_2769_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_a_2768_, v_r_2764_);
return v___x_2769_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_2764_ = stack[0].m_obj;
lean_object* v_a_2765_ = stack[1].m_obj;
lean_object* v_res_2770_;
v_res_2770_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v_r_2764_, v_a_2765_);
stack->m_obj
 = v_res_2770_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0___boxed(lean_object* v_r_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v_r_2771_, v_a_2772_);
lean_dec_ref(v_a_2772_);
return v_res_2774_;
}
}
lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(lean_object* v_requestNo_2778_, lean_object* v_item_2779_, lean_object* v_fromRanges_2780_, lean_object* v_visited_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_name_2784_; uint8_t v___x_2785_; 
v_name_2784_ = lean_ctor_get(v_item_2779_, 0);
v___x_2785_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_2784_, v_visited_2781_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_inc(v_requestNo_2778_);
v___x_2786_ = l_Lean_JsonNumber_fromNat(v_requestNo_2778_);
v___x_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
v___x_2788_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_2779_);
lean_inc_ref(v___x_2787_);
v___x_2789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2787_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
lean_ctor_set(v___x_2789_, 2, v_item_2779_);
v___x_2790_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v___x_2789_, v_a_2782_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v___x_2791_; 
lean_dec_ref_known(v___x_2790_, 1);
v___x_2791_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v___x_2787_, v_a_2782_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2829_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
if (v___x_2785_ == 0)
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_box(0);
lean_inc_ref(v_name_2784_);
v___x_2836_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_2784_, v___x_2835_, v_visited_2781_);
v___y_2829_ = v___x_2836_;
goto v___jp_2828_;
}
else
{
v___y_2829_ = v_visited_2781_;
goto v___jp_2828_;
}
v___jp_2793_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; size_t v_sz_2799_; size_t v___x_2800_; lean_object* v___x_2801_; 
v___x_2797_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___y_2795_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v_sz_2799_ = lean_array_size(v___y_2796_);
v___x_2800_ = ((size_t)0ULL);
v___x_2801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___y_2794_, v___y_2796_, v_sz_2799_, v___x_2800_, v___x_2798_, v_a_2782_);
lean_dec_ref(v___y_2796_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2819_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2819_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2819_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v_fst_2806_; lean_object* v_snd_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2818_; 
v_fst_2806_ = lean_ctor_get(v_a_2802_, 0);
v_snd_2807_ = lean_ctor_get(v_a_2802_, 1);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_a_2802_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2809_ = v_a_2802_;
v_isShared_2810_ = v_isSharedCheck_2818_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_snd_2807_);
lean_inc(v_fst_2806_);
lean_dec(v_a_2802_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2818_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2811_, 0, v_item_2779_);
lean_ctor_set(v___x_2811_, 1, v_fromRanges_2780_);
lean_ctor_set(v___x_2811_, 2, v_snd_2807_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 1, v_fst_2806_);
lean_ctor_set(v___x_2809_, 0, v___x_2811_);
v___x_2813_ = v___x_2809_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_fst_2806_);
v___x_2813_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2815_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2813_);
v___x_2815_ = v___x_2804_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v_fromRanges_2780_);
lean_dec_ref(v_item_2779_);
v_a_2820_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2801_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2801_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
v___jp_2828_:
{
lean_object* v_result_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_result_2830_ = lean_ctor_get(v_a_2792_, 1);
lean_inc(v_result_2830_);
lean_dec(v_a_2792_);
v___x_2831_ = lean_unsigned_to_nat(1u);
v___x_2832_ = lean_nat_add(v_requestNo_2778_, v___x_2831_);
lean_dec(v_requestNo_2778_);
if (lean_obj_tag(v_result_2830_) == 0)
{
lean_object* v___x_2833_; 
v___x_2833_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1));
v___y_2794_ = v___y_2829_;
v___y_2795_ = v___x_2832_;
v___y_2796_ = v___x_2833_;
goto v___jp_2793_;
}
else
{
lean_object* v_val_2834_; 
v_val_2834_ = lean_ctor_get(v_result_2830_, 0);
lean_inc(v_val_2834_);
lean_dec_ref_known(v_result_2830_, 1);
v___y_2794_ = v___y_2829_;
v___y_2795_ = v___x_2832_;
v___y_2796_ = v_val_2834_;
goto v___jp_2793_;
}
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v_visited_2781_);
lean_dec_ref(v_fromRanges_2780_);
lean_dec_ref(v_item_2779_);
lean_dec(v_requestNo_2778_);
v_a_2837_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2791_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2791_);
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
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec_ref_known(v___x_2787_, 1);
lean_dec(v_visited_2781_);
lean_dec_ref(v_fromRanges_2780_);
lean_dec_ref(v_item_2779_);
lean_dec(v_requestNo_2778_);
v_a_2845_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2790_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2790_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_dec(v_visited_2781_);
lean_dec_ref(v_fromRanges_2780_);
v___x_2853_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2854_, 0, v_item_2779_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
lean_ctor_set(v___x_2854_, 2, v___x_2853_);
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v_requestNo_2778_);
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
return v___x_2856_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestNo_2778_ = stack[0].m_obj;
lean_object* v_item_2779_ = stack[1].m_obj;
lean_object* v_fromRanges_2780_ = stack[2].m_obj;
lean_object* v_visited_2781_ = stack[3].m_obj;
lean_object* v_a_2782_ = stack[4].m_obj;
lean_object* v_res_2857_;
v_res_2857_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_requestNo_2778_, v_item_2779_, v_fromRanges_2780_, v_visited_2781_, v_a_2782_);
stack->m_obj
 = v_res_2857_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(lean_object* v___x_2858_, lean_object* v_as_2859_, size_t v_sz_2860_, size_t v_i_2861_, lean_object* v_b_2862_, lean_object* v___y_2863_){
_start:
{
uint8_t v___x_2865_; 
v___x_2865_ = lean_usize_dec_lt(v_i_2861_, v_sz_2860_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
lean_dec(v___x_2858_);
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_b_2862_);
return v___x_2866_;
}
else
{
lean_object* v_fst_2867_; lean_object* v_snd_2868_; lean_object* v_a_2869_; lean_object* v_to_2870_; lean_object* v_fromRanges_2871_; lean_object* v___x_2872_; 
v_fst_2867_ = lean_ctor_get(v_b_2862_, 0);
lean_inc(v_fst_2867_);
v_snd_2868_ = lean_ctor_get(v_b_2862_, 1);
lean_inc(v_snd_2868_);
lean_dec_ref(v_b_2862_);
v_a_2869_ = lean_array_uget_borrowed(v_as_2859_, v_i_2861_);
v_to_2870_ = lean_ctor_get(v_a_2869_, 0);
v_fromRanges_2871_ = lean_ctor_get(v_a_2869_, 1);
lean_inc(v___x_2858_);
lean_inc_ref(v_fromRanges_2871_);
lean_inc_ref(v_to_2870_);
v___x_2872_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2867_, v_to_2870_, v_fromRanges_2871_, v___x_2858_, v___y_2863_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v_fst_2874_; lean_object* v_snd_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2886_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v_fst_2874_ = lean_ctor_get(v_a_2873_, 0);
v_snd_2875_ = lean_ctor_get(v_a_2873_, 1);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_a_2873_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2877_ = v_a_2873_;
v_isShared_2878_ = v_isSharedCheck_2886_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_snd_2875_);
lean_inc(v_fst_2874_);
lean_dec(v_a_2873_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2886_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2879_ = lean_array_push(v_snd_2868_, v_fst_2874_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 1, v___x_2879_);
lean_ctor_set(v___x_2877_, 0, v_snd_2875_);
v___x_2881_ = v___x_2877_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_snd_2875_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
size_t v___x_2882_; size_t v___x_2883_; 
v___x_2882_ = ((size_t)1ULL);
v___x_2883_ = lean_usize_add(v_i_2861_, v___x_2882_);
v_i_2861_ = v___x_2883_;
v_b_2862_ = v___x_2881_;
goto _start;
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec(v_snd_2868_);
lean_dec(v___x_2858_);
v_a_2887_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2872_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2872_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2858_ = stack[0].m_obj;
lean_object* v_as_2859_ = stack[1].m_obj;
size_t v_sz_2860_ = stack[2].m_num;
size_t v_i_2861_ = stack[3].m_num;
lean_object* v_b_2862_ = stack[4].m_obj;
lean_object* v___y_2863_ = stack[5].m_obj;
lean_object* v_res_2895_;
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___x_2858_, v_as_2859_, v_sz_2860_, v_i_2861_, v_b_2862_, v___y_2863_);
stack->m_obj
 = v_res_2895_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2___boxed(lean_object* v___x_2896_, lean_object* v_as_2897_, lean_object* v_sz_2898_, lean_object* v_i_2899_, lean_object* v_b_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
size_t v_sz_boxed_2903_; size_t v_i_boxed_2904_; lean_object* v_res_2905_; 
v_sz_boxed_2903_ = lean_unbox_usize(v_sz_2898_);
lean_dec(v_sz_2898_);
v_i_boxed_2904_ = lean_unbox_usize(v_i_2899_);
lean_dec(v_i_2899_);
v_res_2905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___x_2896_, v_as_2897_, v_sz_boxed_2903_, v_i_boxed_2904_, v_b_2900_, v___y_2901_);
lean_dec_ref(v___y_2901_);
lean_dec_ref(v_as_2897_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___boxed(lean_object* v_requestNo_2906_, lean_object* v_item_2907_, lean_object* v_fromRanges_2908_, lean_object* v_visited_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_requestNo_2906_, v_item_2907_, v_fromRanges_2908_, v_visited_2909_, v_a_2910_);
lean_dec_ref(v_a_2910_);
return v_res_2912_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(lean_object* v_as_2913_, size_t v_sz_2914_, size_t v_i_2915_, lean_object* v_b_2916_, lean_object* v___y_2917_){
_start:
{
uint8_t v___x_2919_; 
v___x_2919_ = lean_usize_dec_lt(v_i_2915_, v_sz_2914_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2920_, 0, v_b_2916_);
return v___x_2920_;
}
else
{
lean_object* v_fst_2921_; lean_object* v_snd_2922_; lean_object* v_a_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_fst_2921_ = lean_ctor_get(v_b_2916_, 0);
lean_inc(v_fst_2921_);
v_snd_2922_ = lean_ctor_get(v_b_2916_, 1);
lean_inc(v_snd_2922_);
lean_dec_ref(v_b_2916_);
v_a_2923_ = lean_array_uget_borrowed(v_as_2913_, v_i_2915_);
v___x_2924_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2925_ = lean_box(1);
lean_inc(v_a_2923_);
v___x_2926_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2921_, v_a_2923_, v___x_2924_, v___x_2925_, v___y_2917_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v_fst_2928_; lean_object* v_snd_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2940_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v_fst_2928_ = lean_ctor_get(v_a_2927_, 0);
v_snd_2929_ = lean_ctor_get(v_a_2927_, 1);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_a_2927_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2931_ = v_a_2927_;
v_isShared_2932_ = v_isSharedCheck_2940_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_snd_2929_);
lean_inc(v_fst_2928_);
lean_dec(v_a_2927_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2940_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2933_ = lean_array_push(v_snd_2922_, v_fst_2928_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 1, v___x_2933_);
lean_ctor_set(v___x_2931_, 0, v_snd_2929_);
v___x_2935_ = v___x_2931_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_snd_2929_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v___x_2933_);
v___x_2935_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
size_t v___x_2936_; size_t v___x_2937_; 
v___x_2936_ = ((size_t)1ULL);
v___x_2937_ = lean_usize_add(v_i_2915_, v___x_2936_);
v_i_2915_ = v___x_2937_;
v_b_2916_ = v___x_2935_;
goto _start;
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v_snd_2922_);
v_a_2941_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2926_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2926_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2913_ = stack[0].m_obj;
size_t v_sz_2914_ = stack[1].m_num;
size_t v_i_2915_ = stack[2].m_num;
lean_object* v_b_2916_ = stack[3].m_obj;
lean_object* v___y_2917_ = stack[4].m_obj;
lean_object* v_res_2949_;
v_res_2949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v_as_2913_, v_sz_2914_, v_i_2915_, v_b_2916_, v___y_2917_);
stack->m_obj
 = v_res_2949_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0___boxed(lean_object* v_as_2950_, lean_object* v_sz_2951_, lean_object* v_i_2952_, lean_object* v_b_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
size_t v_sz_boxed_2956_; size_t v_i_boxed_2957_; lean_object* v_res_2958_; 
v_sz_boxed_2956_ = lean_unbox_usize(v_sz_2951_);
lean_dec(v_sz_2951_);
v_i_boxed_2957_ = lean_unbox_usize(v_i_2952_);
lean_dec(v_i_2952_);
v_res_2958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v_as_2950_, v_sz_boxed_2956_, v_i_boxed_2957_, v_b_2953_, v___y_2954_);
lean_dec_ref(v___y_2954_);
lean_dec_ref(v_as_2950_);
return v_res_2958_;
}
}
lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(lean_object* v_requestNo_2959_, lean_object* v_uri_2960_, lean_object* v_pos_2961_, lean_object* v_a_2962_){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_inc(v_requestNo_2959_);
v___x_2964_ = l_Lean_JsonNumber_fromNat(v_requestNo_2959_);
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
v___x_2966_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v_uri_2960_);
lean_ctor_set(v___x_2967_, 1, v_pos_2961_);
lean_inc_ref(v___x_2965_);
v___x_2968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2965_);
lean_ctor_set(v___x_2968_, 1, v___x_2966_);
lean_ctor_set(v___x_2968_, 2, v___x_2967_);
v___x_2969_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2968_, v_a_2962_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v___x_2970_; 
lean_dec_ref_known(v___x_2969_, 1);
v___x_2970_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2965_, v_a_2962_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v_result_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_3014_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2970_, 1);
v_result_2972_ = lean_ctor_get(v_a_2971_, 1);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_a_2971_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; 
v_unused_3015_ = lean_ctor_get(v_a_2971_, 0);
lean_dec(v_unused_3015_);
v___x_2974_ = v_a_2971_;
v_isShared_2975_ = v_isSharedCheck_3014_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_result_2972_);
lean_dec(v_a_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_3014_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___y_2979_; 
v___x_2976_ = lean_unsigned_to_nat(1u);
v___x_2977_ = lean_nat_add(v_requestNo_2959_, v___x_2976_);
lean_dec(v_requestNo_2959_);
if (lean_obj_tag(v_result_2972_) == 0)
{
lean_object* v___x_3012_; 
v___x_3012_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2979_ = v___x_3012_;
goto v___jp_2978_;
}
else
{
lean_object* v_val_3013_; 
v_val_3013_ = lean_ctor_get(v_result_2972_, 0);
lean_inc(v_val_3013_);
lean_dec_ref_known(v_result_2972_, 1);
v___y_2979_ = v_val_3013_;
goto v___jp_2978_;
}
v___jp_2978_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2980_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 1, v___x_2980_);
lean_ctor_set(v___x_2974_, 0, v___x_2977_);
v___x_2982_ = v___x_2974_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_2977_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_3011_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
size_t v_sz_2983_; size_t v___x_2984_; lean_object* v___x_2985_; 
v_sz_2983_ = lean_array_size(v___y_2979_);
v___x_2984_ = ((size_t)0ULL);
v___x_2985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v___y_2979_, v_sz_2983_, v___x_2984_, v___x_2982_, v_a_2962_);
lean_dec_ref(v___y_2979_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3002_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_3002_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3002_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v_fst_2990_; lean_object* v_snd_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3001_; 
v_fst_2990_ = lean_ctor_get(v_a_2986_, 0);
v_snd_2991_ = lean_ctor_get(v_a_2986_, 1);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_a_2986_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2993_ = v_a_2986_;
v_isShared_2994_ = v_isSharedCheck_3001_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_snd_2991_);
lean_inc(v_fst_2990_);
lean_dec(v_a_2986_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3001_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v_fst_2990_);
lean_ctor_set(v___x_2993_, 0, v_snd_2991_);
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_snd_2991_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_fst_2990_);
v___x_2996_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2998_; 
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v___x_2996_);
v___x_2998_ = v___x_2988_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
v_a_3003_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2985_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2985_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec(v_requestNo_2959_);
v_a_3016_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2970_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2970_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec_ref_known(v___x_2965_, 1);
lean_dec(v_requestNo_2959_);
v_a_3024_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_2969_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_2969_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestNo_2959_ = stack[0].m_obj;
lean_object* v_uri_2960_ = stack[1].m_obj;
lean_object* v_pos_2961_ = stack[2].m_obj;
lean_object* v_a_2962_ = stack[3].m_obj;
lean_object* v_res_3032_;
v_res_3032_ = l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(v_requestNo_2959_, v_uri_2960_, v_pos_2961_, v_a_2962_);
stack->m_obj
 = v_res_3032_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy___boxed(lean_object* v_requestNo_3033_, lean_object* v_uri_3034_, lean_object* v_pos_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(v_requestNo_3033_, v_uri_3034_, v_pos_3035_, v_a_3036_);
lean_dec_ref(v_a_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(lean_object* v_j_3039_, lean_object* v_k_3040_){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = l_Lean_Json_getObjValD(v_j_3039_, v_k_3040_);
v___x_3042_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0___boxed(lean_object* v_j_3043_, lean_object* v_k_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_j_3043_, v_k_3044_);
lean_dec_ref(v_k_3044_);
return v_res_3045_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = 1;
v___x_3053_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1));
v___x_3054_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3053_, v___x_3052_);
return v___x_3054_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3055_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_3056_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2);
v___x_3057_ = lean_string_append(v___x_3056_, v___x_3055_);
return v___x_3057_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_3059_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3060_ = lean_string_append(v___x_3059_, v___x_3058_);
return v___x_3060_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3062_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4);
v___x_3063_ = lean_string_append(v___x_3062_, v___x_3061_);
return v___x_3063_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_3065_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3066_ = lean_string_append(v___x_3065_, v___x_3064_);
return v___x_3066_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3067_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3068_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6);
v___x_3069_ = lean_string_append(v___x_3068_, v___x_3067_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(lean_object* v_json_3070_){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_3070_);
v___x_3072_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_json_3070_, v___x_3071_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_json_3070_);
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3082_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3082_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
v___x_3077_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5);
v___x_3078_ = lean_string_append(v___x_3077_, v_a_3073_);
lean_dec(v_a_3073_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 0, v___x_3078_);
v___x_3080_ = v___x_3075_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3078_);
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
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_json_3070_);
v_a_3083_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3072_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3072_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set_tag(v___x_3085_, 0);
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v_a_3091_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3072_, 1);
v___x_3092_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3093_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_json_3070_, v___x_3092_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3091_);
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3103_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3103_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3098_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7);
v___x_3099_ = lean_string_append(v___x_3098_, v_a_3094_);
lean_dec(v_a_3094_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3099_);
v___x_3101_ = v___x_3096_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
else
{
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_a_3091_);
v_a_3104_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3093_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3093_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 0);
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3120_; 
v_a_3112_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3114_ = v___x_3093_;
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3093_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v_a_3091_);
lean_ctor_set(v___x_3116_, 1, v_a_3112_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3116_);
v___x_3118_ = v___x_3114_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_3121_, size_t v_i_3122_, lean_object* v_bs_3123_){
_start:
{
uint8_t v___x_3124_; 
v___x_3124_ = lean_usize_dec_lt(v_i_3122_, v_sz_3121_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_bs_3123_);
return v___x_3125_;
}
else
{
lean_object* v_v_3126_; lean_object* v___x_3127_; 
v_v_3126_ = lean_array_uget_borrowed(v_bs_3123_, v_i_3122_);
lean_inc(v_v_3126_);
v___x_3127_ = l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(v_v_3126_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec_ref(v_bs_3123_);
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3137_; lean_object* v_bs_x27_3138_; size_t v___x_3139_; size_t v___x_3140_; lean_object* v___x_3141_; 
v_a_3136_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___x_3127_, 1);
v___x_3137_ = lean_unsigned_to_nat(0u);
v_bs_x27_3138_ = lean_array_uset(v_bs_3123_, v_i_3122_, v___x_3137_);
v___x_3139_ = ((size_t)1ULL);
v___x_3140_ = lean_usize_add(v_i_3122_, v___x_3139_);
v___x_3141_ = lean_array_uset(v_bs_x27_3138_, v_i_3122_, v_a_3136_);
v_i_3122_ = v___x_3140_;
v_bs_3123_ = v___x_3141_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3121_ = stack[0].m_num;
size_t v_i_3122_ = stack[1].m_num;
lean_object* v_bs_3123_ = stack[2].m_obj;
lean_object* v_res_3143_;
v_res_3143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_3121_, v_i_3122_, v_bs_3123_);
stack->m_obj
 = v_res_3143_;
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_3144_){
_start:
{
if (lean_obj_tag(v_x_3144_) == 4)
{
lean_object* v_elems_3145_; size_t v_sz_3146_; size_t v___x_3147_; lean_object* v___x_3148_; 
v_elems_3145_ = lean_ctor_get(v_x_3144_, 0);
lean_inc_ref(v_elems_3145_);
lean_dec_ref_known(v_x_3144_, 1);
v_sz_3146_ = lean_array_size(v_elems_3145_);
v___x_3147_ = ((size_t)0ULL);
v___x_3148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_3146_, v___x_3147_, v_elems_3145_);
return v___x_3148_;
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3149_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3150_ = lean_unsigned_to_nat(80u);
v___x_3151_ = l_Lean_Json_pretty(v_x_3144_, v___x_3150_);
v___x_3152_ = lean_string_append(v___x_3149_, v___x_3151_);
lean_dec_ref(v___x_3151_);
v___x_3153_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3154_ = lean_string_append(v___x_3152_, v___x_3153_);
v___x_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
return v___x_3155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(lean_object* v_j_3156_, lean_object* v_k_3157_){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = l_Lean_Json_getObjValD(v_j_3156_, v_k_3157_);
v___x_3159_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(v___x_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1___boxed(lean_object* v_j_3160_, lean_object* v_k_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_j_3160_, v_k_3161_);
lean_dec_ref(v_k_3161_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_3163_, lean_object* v_i_3164_, lean_object* v_bs_3165_){
_start:
{
size_t v_sz_boxed_3166_; size_t v_i_boxed_3167_; lean_object* v_res_3168_; 
v_sz_boxed_3166_ = lean_unbox_usize(v_sz_3163_);
lean_dec(v_sz_3163_);
v_i_boxed_3167_ = lean_unbox_usize(v_i_3164_);
lean_dec(v_i_3164_);
v_res_3168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_3166_, v_i_boxed_3167_, v_bs_3165_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(lean_object* v_x_3171_){
_start:
{
lean_object* v_item_3172_; lean_object* v_children_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3193_; 
v_item_3172_ = lean_ctor_get(v_x_3171_, 0);
v_children_3173_ = lean_ctor_get(v_x_3171_, 1);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_x_3171_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3175_ = v_x_3171_;
v_isShared_3176_ = v_isSharedCheck_3193_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_children_3173_);
lean_inc(v_item_3172_);
lean_dec(v_x_3171_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3193_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3177_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_3178_ = l_Lean_Lsp_instToJsonLeanImport_toJson(v_item_3172_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 1, v___x_3178_);
lean_ctor_set(v___x_3175_, 0, v___x_3177_);
v___x_3180_ = v___x_3175_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3181_ = lean_box(0);
v___x_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3180_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3184_ = l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(v_children_3173_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
lean_ctor_set(v___x_3186_, 1, v___x_3181_);
v___x_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v___x_3181_);
v___x_3188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3182_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_3190_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_3188_, v___x_3189_);
v___x_3191_ = l_Lean_Json_mkObj(v___x_3190_);
lean_dec(v___x_3190_);
return v___x_3191_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(size_t v_sz_3194_, size_t v_i_3195_, lean_object* v_bs_3196_){
_start:
{
uint8_t v___x_3197_; 
v___x_3197_ = lean_usize_dec_lt(v_i_3195_, v_sz_3194_);
if (v___x_3197_ == 0)
{
return v_bs_3196_;
}
else
{
lean_object* v_v_3198_; lean_object* v___x_3199_; lean_object* v_bs_x27_3200_; lean_object* v___x_3201_; size_t v___x_3202_; size_t v___x_3203_; lean_object* v___x_3204_; 
v_v_3198_ = lean_array_uget(v_bs_3196_, v_i_3195_);
v___x_3199_ = lean_unsigned_to_nat(0u);
v_bs_x27_3200_ = lean_array_uset(v_bs_3196_, v_i_3195_, v___x_3199_);
v___x_3201_ = l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(v_v_3198_);
v___x_3202_ = ((size_t)1ULL);
v___x_3203_ = lean_usize_add(v_i_3195_, v___x_3202_);
v___x_3204_ = lean_array_uset(v_bs_x27_3200_, v_i_3195_, v___x_3201_);
v_i_3195_ = v___x_3203_;
v_bs_3196_ = v___x_3204_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3194_ = stack[0].m_num;
size_t v_i_3195_ = stack[1].m_num;
lean_object* v_bs_3196_ = stack[2].m_obj;
lean_object* v_res_3206_;
v_res_3206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_3194_, v_i_3195_, v_bs_3196_);
stack->m_obj
 = v_res_3206_;
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(lean_object* v_a_3207_){
_start:
{
size_t v_sz_3208_; size_t v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_sz_3208_ = lean_array_size(v_a_3207_);
v___x_3209_ = ((size_t)0ULL);
v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_3208_, v___x_3209_, v_a_3207_);
v___x_3211_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3212_, lean_object* v_i_3213_, lean_object* v_bs_3214_){
_start:
{
size_t v_sz_boxed_3215_; size_t v_i_boxed_3216_; lean_object* v_res_3217_; 
v_sz_boxed_3215_ = lean_unbox_usize(v_sz_3212_);
lean_dec(v_sz_3212_);
v_i_boxed_3216_ = lean_unbox_usize(v_i_3213_);
lean_dec(v_i_3213_);
v_res_3217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_boxed_3215_, v_i_boxed_3216_, v_bs_3214_);
return v_res_3217_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(size_t v_sz_3220_, size_t v_i_3221_, lean_object* v_bs_3222_){
_start:
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_usize_dec_lt(v_i_3221_, v_sz_3220_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_bs_3222_);
return v___x_3224_;
}
else
{
lean_object* v_v_3225_; lean_object* v___x_3226_; 
v_v_3225_ = lean_array_uget_borrowed(v_bs_3222_, v_i_3221_);
lean_inc(v_v_3225_);
v___x_3226_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v_v_3225_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec_ref(v_bs_3222_);
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3226_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3236_; lean_object* v_bs_x27_3237_; size_t v___x_3238_; size_t v___x_3239_; lean_object* v___x_3240_; 
v_a_3235_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3226_, 1);
v___x_3236_ = lean_unsigned_to_nat(0u);
v_bs_x27_3237_ = lean_array_uset(v_bs_3222_, v_i_3221_, v___x_3236_);
v___x_3238_ = ((size_t)1ULL);
v___x_3239_ = lean_usize_add(v_i_3221_, v___x_3238_);
v___x_3240_ = lean_array_uset(v_bs_x27_3237_, v_i_3221_, v_a_3235_);
v_i_3221_ = v___x_3239_;
v_bs_3222_ = v___x_3240_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3220_ = stack[0].m_num;
size_t v_i_3221_ = stack[1].m_num;
lean_object* v_bs_3222_ = stack[2].m_obj;
lean_object* v_res_3242_;
v_res_3242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_3220_, v_i_3221_, v_bs_3222_);
stack->m_obj
 = v_res_3242_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_3243_, lean_object* v_i_3244_, lean_object* v_bs_3245_){
_start:
{
size_t v_sz_boxed_3246_; size_t v_i_boxed_3247_; lean_object* v_res_3248_; 
v_sz_boxed_3246_ = lean_unbox_usize(v_sz_3243_);
lean_dec(v_sz_3243_);
v_i_boxed_3247_ = lean_unbox_usize(v_i_3244_);
lean_dec(v_i_3244_);
v_res_3248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_boxed_3246_, v_i_boxed_3247_, v_bs_3245_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(lean_object* v_x_3249_){
_start:
{
if (lean_obj_tag(v_x_3249_) == 4)
{
lean_object* v_elems_3250_; size_t v_sz_3251_; size_t v___x_3252_; lean_object* v___x_3253_; 
v_elems_3250_ = lean_ctor_get(v_x_3249_, 0);
lean_inc_ref(v_elems_3250_);
lean_dec_ref_known(v_x_3249_, 1);
v_sz_3251_ = lean_array_size(v_elems_3250_);
v___x_3252_ = ((size_t)0ULL);
v___x_3253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_3251_, v___x_3252_, v_elems_3250_);
return v___x_3253_;
}
else
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3254_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3255_ = lean_unsigned_to_nat(80u);
v___x_3256_ = l_Lean_Json_pretty(v_x_3249_, v___x_3255_);
v___x_3257_ = lean_string_append(v___x_3254_, v___x_3256_);
lean_dec_ref(v___x_3256_);
v___x_3258_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3259_ = lean_string_append(v___x_3257_, v___x_3258_);
v___x_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
return v___x_3260_;
}
}
}
lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(lean_object* v_expectedID_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_Lsp_Ipc_stdout(v_a_3262_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3408_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3267_ = v___x_3264_;
v_isShared_3268_ = v_isSharedCheck_3408_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3264_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3408_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_3265_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3399_; 
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3399_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3399_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___y_3275_; lean_object* v___y_3276_; 
switch(lean_obj_tag(v_a_3270_))
{
case 2:
{
lean_object* v_id_3282_; lean_object* v_result_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3327_; 
v_id_3282_ = lean_ctor_get(v_a_3270_, 0);
v_result_3283_ = lean_ctor_get(v_a_3270_, 1);
v_isSharedCheck_3327_ = !lean_is_exclusive(v_a_3270_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3285_ = v_a_3270_;
v_isShared_3286_ = v_isSharedCheck_3327_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_result_3283_);
lean_inc(v_id_3282_);
lean_dec(v_a_3270_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3327_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
uint8_t v___x_3287_; 
v___x_3287_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3282_, v_expectedID_3261_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v___y_3290_; 
lean_del_object(v___x_3285_);
lean_dec(v_result_3283_);
lean_del_object(v___x_3267_);
v___x_3288_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3261_))
{
case 0:
{
lean_object* v_s_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_s_3301_ = lean_ctor_get(v_expectedID_3261_, 0);
lean_inc_ref(v_s_3301_);
lean_dec_ref_known(v_expectedID_3261_, 1);
v___x_3302_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3303_ = lean_string_append(v___x_3302_, v_s_3301_);
lean_dec_ref(v_s_3301_);
v___x_3304_ = lean_string_append(v___x_3303_, v___x_3302_);
v___y_3290_ = v___x_3304_;
goto v___jp_3289_;
}
case 1:
{
lean_object* v_n_3305_; lean_object* v___x_3306_; 
v_n_3305_ = lean_ctor_get(v_expectedID_3261_, 0);
lean_inc_ref(v_n_3305_);
lean_dec_ref_known(v_expectedID_3261_, 1);
v___x_3306_ = l_Lean_JsonNumber_toString(v_n_3305_);
v___y_3290_ = v___x_3306_;
goto v___jp_3289_;
}
default: 
{
lean_object* v___x_3307_; 
v___x_3307_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3290_ = v___x_3307_;
goto v___jp_3289_;
}
}
v___jp_3289_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3291_ = lean_string_append(v___x_3288_, v___y_3290_);
lean_dec_ref(v___y_3290_);
v___x_3292_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3293_ = lean_string_append(v___x_3291_, v___x_3292_);
switch(lean_obj_tag(v_id_3282_))
{
case 0:
{
lean_object* v_s_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_s_3294_ = lean_ctor_get(v_id_3282_, 0);
lean_inc_ref(v_s_3294_);
lean_dec_ref_known(v_id_3282_, 1);
v___x_3295_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3296_ = lean_string_append(v___x_3295_, v_s_3294_);
lean_dec_ref(v_s_3294_);
v___x_3297_ = lean_string_append(v___x_3296_, v___x_3295_);
v___y_3275_ = v___x_3293_;
v___y_3276_ = v___x_3297_;
goto v___jp_3274_;
}
case 1:
{
lean_object* v_n_3298_; lean_object* v___x_3299_; 
v_n_3298_ = lean_ctor_get(v_id_3282_, 0);
lean_inc_ref(v_n_3298_);
lean_dec_ref_known(v_id_3282_, 1);
v___x_3299_ = l_Lean_JsonNumber_toString(v_n_3298_);
v___y_3275_ = v___x_3293_;
v___y_3276_ = v___x_3299_;
goto v___jp_3274_;
}
default: 
{
lean_object* v___x_3300_; 
v___x_3300_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3275_ = v___x_3293_;
v___y_3276_ = v___x_3300_;
goto v___jp_3274_;
}
}
}
}
else
{
lean_object* v___x_3308_; 
lean_dec(v_id_3282_);
lean_del_object(v___x_3272_);
lean_inc(v_result_3283_);
v___x_3308_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(v_result_3283_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
lean_del_object(v___x_3285_);
lean_dec(v_expectedID_3261_);
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___x_3308_, 1);
v___x_3310_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3311_ = l_Lean_Json_compress(v_result_3283_);
v___x_3312_ = lean_string_append(v___x_3310_, v___x_3311_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3314_ = lean_string_append(v___x_3312_, v___x_3313_);
v___x_3315_ = lean_string_append(v___x_3314_, v_a_3309_);
lean_dec(v_a_3309_);
v___x_3316_ = lean_mk_io_user_error(v___x_3315_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 1);
lean_ctor_set(v___x_3267_, 0, v___x_3316_);
v___x_3318_ = v___x_3267_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; 
lean_dec(v_result_3283_);
v_a_3320_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3308_, 1);
if (v_isShared_3286_ == 0)
{
lean_ctor_set_tag(v___x_3285_, 0);
lean_ctor_set(v___x_3285_, 1, v_a_3320_);
lean_ctor_set(v___x_3285_, 0, v_expectedID_3261_);
v___x_3322_ = v___x_3285_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_expectedID_3261_);
lean_ctor_set(v_reuseFailAlloc_3326_, 1, v_a_3320_);
v___x_3322_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
lean_object* v___x_3324_; 
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 0, v___x_3322_);
v___x_3324_ = v___x_3267_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3328_; uint8_t v_code_3329_; lean_object* v_message_3330_; lean_object* v_data_x3f_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___x_3363_; lean_object* v___y_3365_; 
lean_del_object(v___x_3272_);
lean_dec(v_expectedID_3261_);
v_id_3328_ = lean_ctor_get(v_a_3270_, 0);
lean_inc(v_id_3328_);
v_code_3329_ = lean_ctor_get_uint8(v_a_3270_, sizeof(void*)*3);
v_message_3330_ = lean_ctor_get(v_a_3270_, 1);
lean_inc_ref(v_message_3330_);
v_data_x3f_3331_ = lean_ctor_get(v_a_3270_, 2);
lean_inc(v_data_x3f_3331_);
lean_dec_ref_known(v_a_3270_, 3);
v___x_3332_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3333_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3363_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3328_))
{
case 0:
{
lean_object* v_s_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
v_s_3381_ = lean_ctor_get(v_id_3328_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_id_3328_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v_id_3328_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_s_3381_);
lean_dec(v_id_3328_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set_tag(v___x_3383_, 3);
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_s_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
v___y_3365_ = v___x_3386_;
goto v___jp_3364_;
}
}
}
case 1:
{
lean_object* v_n_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
v_n_3389_ = lean_ctor_get(v_id_3328_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_id_3328_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v_id_3328_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_n_3389_);
lean_dec(v_id_3328_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
lean_ctor_set_tag(v___x_3391_, 2);
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_n_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
v___y_3365_ = v___x_3394_;
goto v___jp_3364_;
}
}
}
default: 
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_box(0);
v___y_3365_ = v___x_3397_;
goto v___jp_3364_;
}
}
v___jp_3334_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3361_; 
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3336_);
v___x_3339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___y_3336_);
lean_ctor_set(v___x_3339_, 1, v___y_3338_);
v___x_3340_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_message_3330_);
v___x_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3339_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3347_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3346_, v_data_x3f_3331_);
lean_dec(v_data_x3f_3331_);
v___x_3348_ = l_List_appendTR___redArg(v___x_3345_, v___x_3347_);
v___x_3349_ = l_Lean_Json_mkObj(v___x_3348_);
lean_dec(v___x_3348_);
lean_inc_ref(v___y_3337_);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___y_3337_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
lean_ctor_set(v___x_3351_, 1, v___x_3343_);
v___x_3352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___y_3335_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3333_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = l_Lean_Json_mkObj(v___x_3353_);
lean_dec_ref_known(v___x_3353_, 2);
v___x_3355_ = l_Lean_Json_compress(v___x_3354_);
v___x_3356_ = lean_string_append(v___x_3332_, v___x_3355_);
lean_dec_ref(v___x_3355_);
v___x_3357_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3358_ = lean_string_append(v___x_3356_, v___x_3357_);
v___x_3359_ = lean_mk_io_user_error(v___x_3358_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 1);
lean_ctor_set(v___x_3267_, 0, v___x_3359_);
v___x_3361_ = v___x_3267_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
v___jp_3364_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3363_);
lean_ctor_set(v___x_3366_, 1, v___y_3365_);
v___x_3367_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3368_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3329_)
{
case 0:
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3369_;
goto v___jp_3334_;
}
case 1:
{
lean_object* v___x_3370_; 
v___x_3370_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3370_;
goto v___jp_3334_;
}
case 2:
{
lean_object* v___x_3371_; 
v___x_3371_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3371_;
goto v___jp_3334_;
}
case 3:
{
lean_object* v___x_3372_; 
v___x_3372_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3372_;
goto v___jp_3334_;
}
case 4:
{
lean_object* v___x_3373_; 
v___x_3373_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3373_;
goto v___jp_3334_;
}
case 5:
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3374_;
goto v___jp_3334_;
}
case 6:
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3375_;
goto v___jp_3334_;
}
case 7:
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3376_;
goto v___jp_3334_;
}
case 8:
{
lean_object* v___x_3377_; 
v___x_3377_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3377_;
goto v___jp_3334_;
}
case 9:
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3378_;
goto v___jp_3334_;
}
case 10:
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3379_;
goto v___jp_3334_;
}
default: 
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3335_ = v___x_3366_;
v___y_3336_ = v___x_3368_;
v___y_3337_ = v___x_3367_;
v___y_3338_ = v___x_3380_;
goto v___jp_3334_;
}
}
}
}
default: 
{
lean_del_object(v___x_3272_);
lean_dec(v_a_3270_);
lean_del_object(v___x_3267_);
goto _start;
}
}
v___jp_3274_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3277_ = lean_string_append(v___y_3275_, v___y_3276_);
lean_dec_ref(v___y_3276_);
v___x_3278_ = lean_mk_io_user_error(v___x_3277_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set_tag(v___x_3272_, 1);
lean_ctor_set(v___x_3272_, 0, v___x_3278_);
v___x_3280_ = v___x_3272_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_del_object(v___x_3267_);
lean_dec(v_expectedID_3261_);
v_a_3400_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3269_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3269_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v_expectedID_3261_);
v_a_3409_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3264_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3264_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedID_3261_ = stack[0].m_obj;
lean_object* v_a_3262_ = stack[1].m_obj;
lean_object* v_res_3417_;
v_res_3417_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v_expectedID_3261_, v_a_3262_);
stack->m_obj
 = v_res_3417_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1___boxed(lean_object* v_expectedID_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v_expectedID_3418_, v_a_3419_);
lean_dec_ref(v_a_3419_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(lean_object* v_v_3422_){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_v_3422_);
v___x_3424_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3423_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_v_3425_);
lean_dec_ref(v_v_3425_);
return v_res_3426_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(lean_object* v_h_3427_, lean_object* v_r_3428_){
_start:
{
lean_object* v_id_3430_; lean_object* v_method_3431_; lean_object* v_param_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3452_; 
v_id_3430_ = lean_ctor_get(v_r_3428_, 0);
v_method_3431_ = lean_ctor_get(v_r_3428_, 1);
v_param_3432_ = lean_ctor_get(v_r_3428_, 2);
v_isSharedCheck_3452_ = !lean_is_exclusive(v_r_3428_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3434_ = v_r_3428_;
v_isShared_3435_ = v_isSharedCheck_3452_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_param_3432_);
lean_inc(v_method_3431_);
lean_inc(v_id_3430_);
lean_dec(v_r_3428_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3452_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___y_3437_; lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_param_3432_);
lean_dec(v_param_3432_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v___x_3443_; 
lean_dec_ref_known(v___x_3442_, 1);
v___x_3443_ = lean_box(0);
v___y_3437_ = v___x_3443_;
goto v___jp_3436_;
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
v_a_3444_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3442_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3442_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
v___y_3437_ = v___x_3449_;
goto v___jp_3436_;
}
}
}
v___jp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 2, v___y_3437_);
v___x_3439_ = v___x_3434_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_id_3430_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_method_3431_);
lean_ctor_set(v_reuseFailAlloc_3441_, 2, v___y_3437_);
v___x_3439_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3440_; 
v___x_3440_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_3427_, v___x_3439_);
return v___x_3440_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3427_ = stack[0].m_obj;
lean_object* v_r_3428_ = stack[1].m_obj;
lean_object* v_res_3453_;
v_res_3453_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_h_3427_, v_r_3428_);
stack->m_obj
 = v_res_3453_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0___boxed(lean_object* v_h_3454_, lean_object* v_r_3455_, lean_object* v_a_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_h_3454_, v_r_3455_);
return v_res_3457_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(lean_object* v_r_3458_, lean_object* v_a_3459_){
_start:
{
lean_object* v___x_3461_; lean_object* v_a_3462_; lean_object* v___x_3463_; 
v___x_3461_ = l_Lean_Lsp_Ipc_stdin(v_a_3459_);
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3461_);
v___x_3463_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_a_3462_, v_r_3458_);
return v___x_3463_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_3458_ = stack[0].m_obj;
lean_object* v_a_3459_ = stack[1].m_obj;
lean_object* v_res_3464_;
v_res_3464_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v_r_3458_, v_a_3459_);
stack->m_obj
 = v_res_3464_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0___boxed(lean_object* v_r_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v_r_3465_, v_a_3466_);
lean_dec_ref(v_a_3466_);
return v_res_3468_;
}
}
lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(lean_object* v_requestNo_3472_, lean_object* v_item_3473_, lean_object* v_visited_3474_, lean_object* v_a_3475_){
_start:
{
lean_object* v_module_3477_; lean_object* v_name_3478_; uint8_t v___x_3479_; 
v_module_3477_ = lean_ctor_get(v_item_3473_, 0);
v_name_3478_ = lean_ctor_get(v_module_3477_, 0);
v___x_3479_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3478_, v_visited_3474_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_inc(v_requestNo_3472_);
v___x_3480_ = l_Lean_JsonNumber_fromNat(v_requestNo_3472_);
v___x_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
v___x_3482_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0));
lean_inc_ref(v_module_3477_);
lean_inc_ref(v___x_3481_);
v___x_3483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
lean_ctor_set(v___x_3483_, 2, v_module_3477_);
v___x_3484_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v___x_3483_, v_a_3475_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v___x_3485_; 
lean_dec_ref_known(v___x_3484_, 1);
v___x_3485_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3481_, v_a_3475_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___y_3488_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
if (v___x_3479_ == 0)
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = lean_box(0);
lean_inc_ref(v_name_3478_);
v___x_3531_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3478_, v___x_3530_, v_visited_3474_);
v___y_3488_ = v___x_3531_;
goto v___jp_3487_;
}
else
{
v___y_3488_ = v_visited_3474_;
goto v___jp_3487_;
}
v___jp_3487_:
{
lean_object* v_result_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3528_; 
v_result_3489_ = lean_ctor_get(v_a_3486_, 1);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_a_3486_);
if (v_isSharedCheck_3528_ == 0)
{
lean_object* v_unused_3529_; 
v_unused_3529_ = lean_ctor_get(v_a_3486_, 0);
lean_dec(v_unused_3529_);
v___x_3491_ = v_a_3486_;
v_isShared_3492_ = v_isSharedCheck_3528_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_result_3489_);
lean_dec(v_a_3486_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3528_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3493_ = lean_unsigned_to_nat(1u);
v___x_3494_ = lean_nat_add(v_requestNo_3472_, v___x_3493_);
lean_dec(v_requestNo_3472_);
v___x_3495_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 1, v___x_3495_);
lean_ctor_set(v___x_3491_, 0, v___x_3494_);
v___x_3497_ = v___x_3491_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3494_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
size_t v_sz_3498_; size_t v___x_3499_; lean_object* v___x_3500_; 
v_sz_3498_ = lean_array_size(v_result_3489_);
v___x_3499_ = ((size_t)0ULL);
v___x_3500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___y_3488_, v_result_3489_, v_sz_3498_, v___x_3499_, v___x_3497_, v_a_3475_);
lean_dec(v_result_3489_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3518_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3503_ = v___x_3500_;
v_isShared_3504_ = v_isSharedCheck_3518_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3518_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v_fst_3505_; lean_object* v_snd_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3517_; 
v_fst_3505_ = lean_ctor_get(v_a_3501_, 0);
v_snd_3506_ = lean_ctor_get(v_a_3501_, 1);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_a_3501_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3508_ = v_a_3501_;
v_isShared_3509_ = v_isSharedCheck_3517_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_snd_3506_);
lean_inc(v_fst_3505_);
lean_dec(v_a_3501_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3517_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3512_; 
v___x_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3510_, 0, v_item_3473_);
lean_ctor_set(v___x_3510_, 1, v_snd_3506_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v_fst_3505_);
lean_ctor_set(v___x_3508_, 0, v___x_3510_);
v___x_3512_ = v___x_3508_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_fst_3505_);
v___x_3512_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3514_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v___x_3512_);
v___x_3514_ = v___x_3503_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_dec_ref(v_item_3473_);
v_a_3519_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3500_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3500_);
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
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec(v_visited_3474_);
lean_dec_ref(v_item_3473_);
lean_dec(v_requestNo_3472_);
v_a_3532_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3485_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3485_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec_ref_known(v___x_3481_, 1);
lean_dec(v_visited_3474_);
lean_dec_ref(v_item_3473_);
lean_dec(v_requestNo_3472_);
v_a_3540_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3484_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3484_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec(v_visited_3474_);
v___x_3548_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3549_, 0, v_item_3473_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
lean_ctor_set(v___x_3550_, 1, v_requestNo_3472_);
v___x_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
return v___x_3551_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestNo_3472_ = stack[0].m_obj;
lean_object* v_item_3473_ = stack[1].m_obj;
lean_object* v_visited_3474_ = stack[2].m_obj;
lean_object* v_a_3475_ = stack[3].m_obj;
lean_object* v_res_3552_;
v_res_3552_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_requestNo_3472_, v_item_3473_, v_visited_3474_, v_a_3475_);
stack->m_obj
 = v_res_3552_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(lean_object* v___x_3553_, lean_object* v_as_3554_, size_t v_sz_3555_, size_t v_i_3556_, lean_object* v_b_3557_, lean_object* v___y_3558_){
_start:
{
uint8_t v___x_3560_; 
v___x_3560_ = lean_usize_dec_lt(v_i_3556_, v_sz_3555_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; 
lean_dec(v___x_3553_);
v___x_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3561_, 0, v_b_3557_);
return v___x_3561_;
}
else
{
lean_object* v_fst_3562_; lean_object* v_snd_3563_; lean_object* v_a_3564_; lean_object* v___x_3565_; 
v_fst_3562_ = lean_ctor_get(v_b_3557_, 0);
lean_inc(v_fst_3562_);
v_snd_3563_ = lean_ctor_get(v_b_3557_, 1);
lean_inc(v_snd_3563_);
lean_dec_ref(v_b_3557_);
v_a_3564_ = lean_array_uget_borrowed(v_as_3554_, v_i_3556_);
lean_inc(v___x_3553_);
lean_inc(v_a_3564_);
v___x_3565_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_fst_3562_, v_a_3564_, v___x_3553_, v___y_3558_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v_fst_3567_; lean_object* v_snd_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3579_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3565_, 1);
v_fst_3567_ = lean_ctor_get(v_a_3566_, 0);
v_snd_3568_ = lean_ctor_get(v_a_3566_, 1);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_a_3566_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3570_ = v_a_3566_;
v_isShared_3571_ = v_isSharedCheck_3579_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_snd_3568_);
lean_inc(v_fst_3567_);
lean_dec(v_a_3566_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3579_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3572_ = lean_array_push(v_snd_3563_, v_fst_3567_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 1, v___x_3572_);
lean_ctor_set(v___x_3570_, 0, v_snd_3568_);
v___x_3574_ = v___x_3570_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_snd_3568_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
size_t v___x_3575_; size_t v___x_3576_; 
v___x_3575_ = ((size_t)1ULL);
v___x_3576_ = lean_usize_add(v_i_3556_, v___x_3575_);
v_i_3556_ = v___x_3576_;
v_b_3557_ = v___x_3574_;
goto _start;
}
}
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec(v_snd_3563_);
lean_dec(v___x_3553_);
v_a_3580_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3565_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3565_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3553_ = stack[0].m_obj;
lean_object* v_as_3554_ = stack[1].m_obj;
size_t v_sz_3555_ = stack[2].m_num;
size_t v_i_3556_ = stack[3].m_num;
lean_object* v_b_3557_ = stack[4].m_obj;
lean_object* v___y_3558_ = stack[5].m_obj;
lean_object* v_res_3588_;
v_res_3588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___x_3553_, v_as_3554_, v_sz_3555_, v_i_3556_, v_b_3557_, v___y_3558_);
stack->m_obj
 = v_res_3588_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2___boxed(lean_object* v___x_3589_, lean_object* v_as_3590_, lean_object* v_sz_3591_, lean_object* v_i_3592_, lean_object* v_b_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
size_t v_sz_boxed_3596_; size_t v_i_boxed_3597_; lean_object* v_res_3598_; 
v_sz_boxed_3596_ = lean_unbox_usize(v_sz_3591_);
lean_dec(v_sz_3591_);
v_i_boxed_3597_ = lean_unbox_usize(v_i_3592_);
lean_dec(v_i_3592_);
v_res_3598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___x_3589_, v_as_3590_, v_sz_boxed_3596_, v_i_boxed_3597_, v_b_3593_, v___y_3594_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v_as_3590_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___boxed(lean_object* v_requestNo_3599_, lean_object* v_item_3600_, lean_object* v_visited_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_requestNo_3599_, v_item_3600_, v_visited_3601_, v_a_3602_);
lean_dec_ref(v_a_3602_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(lean_object* v_v_3605_){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(v_v_3605_);
v___x_3607_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3606_);
return v___x_3607_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(lean_object* v_h_3608_, lean_object* v_r_3609_){
_start:
{
lean_object* v_id_3611_; lean_object* v_method_3612_; lean_object* v_param_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3633_; 
v_id_3611_ = lean_ctor_get(v_r_3609_, 0);
v_method_3612_ = lean_ctor_get(v_r_3609_, 1);
v_param_3613_ = lean_ctor_get(v_r_3609_, 2);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_r_3609_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3615_ = v_r_3609_;
v_isShared_3616_ = v_isSharedCheck_3633_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_param_3613_);
lean_inc(v_method_3612_);
lean_inc(v_id_3611_);
lean_dec(v_r_3609_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3633_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___y_3618_; lean_object* v___x_3623_; 
v___x_3623_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(v_param_3613_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v___x_3624_; 
lean_dec_ref_known(v___x_3623_, 1);
v___x_3624_ = lean_box(0);
v___y_3618_ = v___x_3624_;
goto v___jp_3617_;
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
v_a_3625_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3623_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3623_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
v___y_3618_ = v___x_3630_;
goto v___jp_3617_;
}
}
}
v___jp_3617_:
{
lean_object* v___x_3620_; 
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 2, v___y_3618_);
v___x_3620_ = v___x_3615_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_id_3611_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_method_3612_);
lean_ctor_set(v_reuseFailAlloc_3622_, 2, v___y_3618_);
v___x_3620_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_3608_, v___x_3620_);
return v___x_3621_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3608_ = stack[0].m_obj;
lean_object* v_r_3609_ = stack[1].m_obj;
lean_object* v_res_3634_;
v_res_3634_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_h_3608_, v_r_3609_);
stack->m_obj
 = v_res_3634_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0___boxed(lean_object* v_h_3635_, lean_object* v_r_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_h_3635_, v_r_3636_);
return v_res_3638_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(lean_object* v_r_3639_, lean_object* v_a_3640_){
_start:
{
lean_object* v___x_3642_; lean_object* v_a_3643_; lean_object* v___x_3644_; 
v___x_3642_ = l_Lean_Lsp_Ipc_stdin(v_a_3640_);
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref(v___x_3642_);
v___x_3644_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_a_3643_, v_r_3639_);
return v___x_3644_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_3639_ = stack[0].m_obj;
lean_object* v_a_3640_ = stack[1].m_obj;
lean_object* v_res_3645_;
v_res_3645_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v_r_3639_, v_a_3640_);
stack->m_obj
 = v_res_3645_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0___boxed(lean_object* v_r_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v_res_3649_; 
v_res_3649_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v_r_3646_, v_a_3647_);
lean_dec_ref(v_a_3647_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(lean_object* v_x_3652_){
_start:
{
if (lean_obj_tag(v_x_3652_) == 0)
{
lean_object* v___x_3653_; 
v___x_3653_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0));
return v___x_3653_;
}
else
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v_x_3652_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3671_; 
v_a_3663_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3665_ = v___x_3654_;
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3654_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3671_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3667_, 0, v_a_3663_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v___x_3667_);
v___x_3669_ = v___x_3665_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
}
}
lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(lean_object* v_expectedID_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_Lsp_Ipc_stdout(v_a_3673_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3819_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3819_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3819_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_3676_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3810_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3683_ = v___x_3680_;
v_isShared_3684_ = v_isSharedCheck_3810_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3680_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3810_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___y_3686_; lean_object* v___y_3687_; 
switch(lean_obj_tag(v_a_3681_))
{
case 2:
{
lean_object* v_id_3693_; lean_object* v_result_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3738_; 
v_id_3693_ = lean_ctor_get(v_a_3681_, 0);
v_result_3694_ = lean_ctor_get(v_a_3681_, 1);
v_isSharedCheck_3738_ = !lean_is_exclusive(v_a_3681_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3696_ = v_a_3681_;
v_isShared_3697_ = v_isSharedCheck_3738_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_result_3694_);
lean_inc(v_id_3693_);
lean_dec(v_a_3681_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3738_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
uint8_t v___x_3698_; 
v___x_3698_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3693_, v_expectedID_3672_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; lean_object* v___y_3701_; 
lean_del_object(v___x_3696_);
lean_dec(v_result_3694_);
lean_del_object(v___x_3678_);
v___x_3699_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3672_))
{
case 0:
{
lean_object* v_s_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v_s_3712_ = lean_ctor_get(v_expectedID_3672_, 0);
lean_inc_ref(v_s_3712_);
lean_dec_ref_known(v_expectedID_3672_, 1);
v___x_3713_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3714_ = lean_string_append(v___x_3713_, v_s_3712_);
lean_dec_ref(v_s_3712_);
v___x_3715_ = lean_string_append(v___x_3714_, v___x_3713_);
v___y_3701_ = v___x_3715_;
goto v___jp_3700_;
}
case 1:
{
lean_object* v_n_3716_; lean_object* v___x_3717_; 
v_n_3716_ = lean_ctor_get(v_expectedID_3672_, 0);
lean_inc_ref(v_n_3716_);
lean_dec_ref_known(v_expectedID_3672_, 1);
v___x_3717_ = l_Lean_JsonNumber_toString(v_n_3716_);
v___y_3701_ = v___x_3717_;
goto v___jp_3700_;
}
default: 
{
lean_object* v___x_3718_; 
v___x_3718_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3701_ = v___x_3718_;
goto v___jp_3700_;
}
}
v___jp_3700_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3702_ = lean_string_append(v___x_3699_, v___y_3701_);
lean_dec_ref(v___y_3701_);
v___x_3703_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3704_ = lean_string_append(v___x_3702_, v___x_3703_);
switch(lean_obj_tag(v_id_3693_))
{
case 0:
{
lean_object* v_s_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v_s_3705_ = lean_ctor_get(v_id_3693_, 0);
lean_inc_ref(v_s_3705_);
lean_dec_ref_known(v_id_3693_, 1);
v___x_3706_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3707_ = lean_string_append(v___x_3706_, v_s_3705_);
lean_dec_ref(v_s_3705_);
v___x_3708_ = lean_string_append(v___x_3707_, v___x_3706_);
v___y_3686_ = v___x_3704_;
v___y_3687_ = v___x_3708_;
goto v___jp_3685_;
}
case 1:
{
lean_object* v_n_3709_; lean_object* v___x_3710_; 
v_n_3709_ = lean_ctor_get(v_id_3693_, 0);
lean_inc_ref(v_n_3709_);
lean_dec_ref_known(v_id_3693_, 1);
v___x_3710_ = l_Lean_JsonNumber_toString(v_n_3709_);
v___y_3686_ = v___x_3704_;
v___y_3687_ = v___x_3710_;
goto v___jp_3685_;
}
default: 
{
lean_object* v___x_3711_; 
v___x_3711_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3686_ = v___x_3704_;
v___y_3687_ = v___x_3711_;
goto v___jp_3685_;
}
}
}
}
else
{
lean_object* v___x_3719_; 
lean_dec(v_id_3693_);
lean_del_object(v___x_3683_);
lean_inc(v_result_3694_);
v___x_3719_ = l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(v_result_3694_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
lean_del_object(v___x_3696_);
lean_dec(v_expectedID_3672_);
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref_known(v___x_3719_, 1);
v___x_3721_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3722_ = l_Lean_Json_compress(v_result_3694_);
v___x_3723_ = lean_string_append(v___x_3721_, v___x_3722_);
lean_dec_ref(v___x_3722_);
v___x_3724_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3725_ = lean_string_append(v___x_3723_, v___x_3724_);
v___x_3726_ = lean_string_append(v___x_3725_, v_a_3720_);
lean_dec(v_a_3720_);
v___x_3727_ = lean_mk_io_user_error(v___x_3726_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set_tag(v___x_3678_, 1);
lean_ctor_set(v___x_3678_, 0, v___x_3727_);
v___x_3729_ = v___x_3678_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; 
lean_dec(v_result_3694_);
v_a_3731_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3731_);
lean_dec_ref_known(v___x_3719_, 1);
if (v_isShared_3697_ == 0)
{
lean_ctor_set_tag(v___x_3696_, 0);
lean_ctor_set(v___x_3696_, 1, v_a_3731_);
lean_ctor_set(v___x_3696_, 0, v_expectedID_3672_);
v___x_3733_ = v___x_3696_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_expectedID_3672_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_a_3731_);
v___x_3733_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3735_; 
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v___x_3733_);
v___x_3735_ = v___x_3678_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3733_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3739_; uint8_t v_code_3740_; lean_object* v_message_3741_; lean_object* v_data_x3f_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___x_3774_; lean_object* v___y_3776_; 
lean_del_object(v___x_3683_);
lean_dec(v_expectedID_3672_);
v_id_3739_ = lean_ctor_get(v_a_3681_, 0);
lean_inc(v_id_3739_);
v_code_3740_ = lean_ctor_get_uint8(v_a_3681_, sizeof(void*)*3);
v_message_3741_ = lean_ctor_get(v_a_3681_, 1);
lean_inc_ref(v_message_3741_);
v_data_x3f_3742_ = lean_ctor_get(v_a_3681_, 2);
lean_inc(v_data_x3f_3742_);
lean_dec_ref_known(v_a_3681_, 3);
v___x_3743_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3744_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3774_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3739_))
{
case 0:
{
lean_object* v_s_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
v_s_3792_ = lean_ctor_get(v_id_3739_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_id_3739_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v_id_3739_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_s_3792_);
lean_dec(v_id_3739_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
lean_ctor_set_tag(v___x_3794_, 3);
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_s_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
v___y_3776_ = v___x_3797_;
goto v___jp_3775_;
}
}
}
case 1:
{
lean_object* v_n_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
v_n_3800_ = lean_ctor_get(v_id_3739_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v_id_3739_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v_id_3739_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_n_3800_);
lean_dec(v_id_3739_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
lean_ctor_set_tag(v___x_3802_, 2);
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_n_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
v___y_3776_ = v___x_3805_;
goto v___jp_3775_;
}
}
}
default: 
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_box(0);
v___y_3776_ = v___x_3808_;
goto v___jp_3775_;
}
}
v___jp_3745_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
lean_inc(v___y_3749_);
lean_inc_ref(v___y_3746_);
v___x_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___y_3746_);
lean_ctor_set(v___x_3750_, 1, v___y_3749_);
v___x_3751_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3752_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3752_, 0, v_message_3741_);
v___x_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3751_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_box(0);
v___x_3755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3750_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3758_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3757_, v_data_x3f_3742_);
lean_dec(v_data_x3f_3742_);
v___x_3759_ = l_List_appendTR___redArg(v___x_3756_, v___x_3758_);
v___x_3760_ = l_Lean_Json_mkObj(v___x_3759_);
lean_dec(v___x_3759_);
lean_inc_ref(v___y_3748_);
v___x_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___y_3748_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set(v___x_3762_, 1, v___x_3754_);
v___x_3763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___y_3747_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3744_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = l_Lean_Json_mkObj(v___x_3764_);
lean_dec_ref_known(v___x_3764_, 2);
v___x_3766_ = l_Lean_Json_compress(v___x_3765_);
v___x_3767_ = lean_string_append(v___x_3743_, v___x_3766_);
lean_dec_ref(v___x_3766_);
v___x_3768_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3769_ = lean_string_append(v___x_3767_, v___x_3768_);
v___x_3770_ = lean_mk_io_user_error(v___x_3769_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set_tag(v___x_3678_, 1);
lean_ctor_set(v___x_3678_, 0, v___x_3770_);
v___x_3772_ = v___x_3678_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
v___jp_3775_:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3774_);
lean_ctor_set(v___x_3777_, 1, v___y_3776_);
v___x_3778_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3779_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3740_)
{
case 0:
{
lean_object* v___x_3780_; 
v___x_3780_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3780_;
goto v___jp_3745_;
}
case 1:
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3781_;
goto v___jp_3745_;
}
case 2:
{
lean_object* v___x_3782_; 
v___x_3782_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3782_;
goto v___jp_3745_;
}
case 3:
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3783_;
goto v___jp_3745_;
}
case 4:
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3784_;
goto v___jp_3745_;
}
case 5:
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3785_;
goto v___jp_3745_;
}
case 6:
{
lean_object* v___x_3786_; 
v___x_3786_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3786_;
goto v___jp_3745_;
}
case 7:
{
lean_object* v___x_3787_; 
v___x_3787_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3787_;
goto v___jp_3745_;
}
case 8:
{
lean_object* v___x_3788_; 
v___x_3788_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3788_;
goto v___jp_3745_;
}
case 9:
{
lean_object* v___x_3789_; 
v___x_3789_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3789_;
goto v___jp_3745_;
}
case 10:
{
lean_object* v___x_3790_; 
v___x_3790_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3790_;
goto v___jp_3745_;
}
default: 
{
lean_object* v___x_3791_; 
v___x_3791_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3746_ = v___x_3779_;
v___y_3747_ = v___x_3777_;
v___y_3748_ = v___x_3778_;
v___y_3749_ = v___x_3791_;
goto v___jp_3745_;
}
}
}
}
default: 
{
lean_del_object(v___x_3683_);
lean_dec(v_a_3681_);
lean_del_object(v___x_3678_);
goto _start;
}
}
v___jp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3688_ = lean_string_append(v___y_3686_, v___y_3687_);
lean_dec_ref(v___y_3687_);
v___x_3689_ = lean_mk_io_user_error(v___x_3688_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set_tag(v___x_3683_, 1);
lean_ctor_set(v___x_3683_, 0, v___x_3689_);
v___x_3691_ = v___x_3683_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_del_object(v___x_3678_);
lean_dec(v_expectedID_3672_);
v_a_3811_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3680_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3680_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
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
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec(v_expectedID_3672_);
v_a_3820_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3675_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3675_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_expectedID_3672_ = stack[0].m_obj;
lean_object* v_a_3673_ = stack[1].m_obj;
lean_object* v_res_3828_;
v_res_3828_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v_expectedID_3672_, v_a_3673_);
stack->m_obj
 = v_res_3828_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1___boxed(lean_object* v_expectedID_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v_expectedID_3829_, v_a_3830_);
lean_dec_ref(v_a_3830_);
return v_res_3832_;
}
}
lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports(lean_object* v_requestNo_3837_, lean_object* v_uri_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
lean_inc(v_requestNo_3837_);
v___x_3841_ = l_Lean_JsonNumber_fromNat(v_requestNo_3837_);
v___x_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3841_);
v___x_3843_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_3842_);
v___x_3844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3842_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
lean_ctor_set(v___x_3844_, 2, v_uri_3838_);
v___x_3845_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_3844_, v_a_3839_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v___x_3846_; 
lean_dec_ref_known(v___x_3845_, 1);
v___x_3846_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_3842_, v_a_3839_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3905_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3849_ = v___x_3846_;
v_isShared_3850_ = v_isSharedCheck_3905_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3905_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v_result_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3903_; 
v_result_3851_ = lean_ctor_get(v_a_3847_, 1);
v_isSharedCheck_3903_ = !lean_is_exclusive(v_a_3847_);
if (v_isSharedCheck_3903_ == 0)
{
lean_object* v_unused_3904_; 
v_unused_3904_ = lean_ctor_get(v_a_3847_, 0);
lean_dec(v_unused_3904_);
v___x_3853_ = v_a_3847_;
v_isShared_3854_ = v_isSharedCheck_3903_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_result_3851_);
lean_dec(v_a_3847_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3903_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3855_ = lean_unsigned_to_nat(1u);
v___x_3856_ = lean_nat_add(v_requestNo_3837_, v___x_3855_);
lean_dec(v_requestNo_3837_);
if (lean_obj_tag(v_result_3851_) == 1)
{
lean_object* v_val_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3895_; 
lean_del_object(v___x_3849_);
v_val_3857_ = lean_ctor_get(v_result_3851_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v_result_3851_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3859_ = v_result_3851_;
v_isShared_3860_ = v_isSharedCheck_3895_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_val_3857_);
lean_dec(v_result_3851_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3895_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3861_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 1, v___x_3861_);
lean_ctor_set(v___x_3853_, 0, v_val_3857_);
v___x_3863_ = v___x_3853_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_val_3857_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_box(1);
v___x_3865_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v___x_3856_, v___x_3863_, v___x_3864_, v_a_3839_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3885_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3868_ = v___x_3865_;
v_isShared_3869_ = v_isSharedCheck_3885_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3865_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3885_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v_fst_3870_; lean_object* v_snd_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3884_; 
v_fst_3870_ = lean_ctor_get(v_a_3866_, 0);
v_snd_3871_ = lean_ctor_get(v_a_3866_, 1);
v_isSharedCheck_3884_ = !lean_is_exclusive(v_a_3866_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3873_ = v_a_3866_;
v_isShared_3874_ = v_isSharedCheck_3884_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_snd_3871_);
lean_inc(v_fst_3870_);
lean_dec(v_a_3866_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3884_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3876_; 
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v_fst_3870_);
v___x_3876_ = v___x_3859_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_fst_3870_);
v___x_3876_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3878_; 
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 0, v___x_3876_);
v___x_3878_ = v___x_3873_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_snd_3871_);
v___x_3878_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3880_; 
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v___x_3878_);
v___x_3880_ = v___x_3868_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3878_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_del_object(v___x_3859_);
v_a_3886_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3865_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3865_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
}
else
{
lean_object* v___x_3896_; lean_object* v___x_3898_; 
lean_dec(v_result_3851_);
v___x_3896_ = lean_box(0);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 1, v___x_3856_);
lean_ctor_set(v___x_3853_, 0, v___x_3896_);
v___x_3898_ = v___x_3853_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v___x_3856_);
v___x_3898_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
lean_object* v___x_3900_; 
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3898_);
v___x_3900_ = v___x_3849_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3898_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec(v_requestNo_3837_);
v_a_3906_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3846_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3846_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec_ref_known(v___x_3842_, 1);
lean_dec(v_requestNo_3837_);
v_a_3914_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3845_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3845_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_expandModuleHierarchyImports_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestNo_3837_ = stack[0].m_obj;
lean_object* v_uri_3838_ = stack[1].m_obj;
lean_object* v_a_3839_ = stack[2].m_obj;
lean_object* v_res_3922_;
v_res_3922_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImports(v_requestNo_3837_, v_uri_3838_, v_a_3839_);
stack->m_obj
 = v_res_3922_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___boxed(lean_object* v_requestNo_3923_, lean_object* v_uri_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImports(v_requestNo_3923_, v_uri_3924_, v_a_3925_);
lean_dec_ref(v_a_3925_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(lean_object* v_v_3928_){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_v_3928_);
v___x_3930_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_v_3931_);
lean_dec_ref(v_v_3931_);
return v_res_3932_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(lean_object* v_h_3933_, lean_object* v_r_3934_){
_start:
{
lean_object* v_id_3936_; lean_object* v_method_3937_; lean_object* v_param_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3958_; 
v_id_3936_ = lean_ctor_get(v_r_3934_, 0);
v_method_3937_ = lean_ctor_get(v_r_3934_, 1);
v_param_3938_ = lean_ctor_get(v_r_3934_, 2);
v_isSharedCheck_3958_ = !lean_is_exclusive(v_r_3934_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3940_ = v_r_3934_;
v_isShared_3941_ = v_isSharedCheck_3958_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_param_3938_);
lean_inc(v_method_3937_);
lean_inc(v_id_3936_);
lean_dec(v_r_3934_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3958_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___y_3943_; lean_object* v___x_3948_; 
v___x_3948_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_param_3938_);
lean_dec(v_param_3938_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_object* v___x_3949_; 
lean_dec_ref_known(v___x_3948_, 1);
v___x_3949_ = lean_box(0);
v___y_3943_ = v___x_3949_;
goto v___jp_3942_;
}
else
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3957_; 
v_a_3950_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3952_ = v___x_3948_;
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v___x_3948_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3957_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3955_; 
if (v_isShared_3953_ == 0)
{
v___x_3955_ = v___x_3952_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3950_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
v___y_3943_ = v___x_3955_;
goto v___jp_3942_;
}
}
}
v___jp_3942_:
{
lean_object* v___x_3945_; 
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 2, v___y_3943_);
v___x_3945_ = v___x_3940_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_id_3936_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_method_3937_);
lean_ctor_set(v_reuseFailAlloc_3947_, 2, v___y_3943_);
v___x_3945_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_3933_, v___x_3945_);
return v___x_3946_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3933_ = stack[0].m_obj;
lean_object* v_r_3934_ = stack[1].m_obj;
lean_object* v_res_3959_;
v_res_3959_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_h_3933_, v_r_3934_);
stack->m_obj
 = v_res_3959_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0___boxed(lean_object* v_h_3960_, lean_object* v_r_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_h_3960_, v_r_3961_);
return v_res_3963_;
}
}
lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(lean_object* v_r_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v___x_3967_; lean_object* v_a_3968_; lean_object* v___x_3969_; 
v___x_3967_ = l_Lean_Lsp_Ipc_stdin(v_a_3965_);
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_a_3968_);
lean_dec_ref(v___x_3967_);
v___x_3969_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_a_3968_, v_r_3964_);
return v___x_3969_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_3964_ = stack[0].m_obj;
lean_object* v_a_3965_ = stack[1].m_obj;
lean_object* v_res_3970_;
v_res_3970_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v_r_3964_, v_a_3965_);
stack->m_obj
 = v_res_3970_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0___boxed(lean_object* v_r_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v_r_3971_, v_a_3972_);
lean_dec_ref(v_a_3972_);
return v_res_3974_;
}
}
lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(lean_object* v_requestNo_3976_, lean_object* v_item_3977_, lean_object* v_visited_3978_, lean_object* v_a_3979_){
_start:
{
lean_object* v_module_3981_; lean_object* v_name_3982_; uint8_t v___x_3983_; 
v_module_3981_ = lean_ctor_get(v_item_3977_, 0);
v_name_3982_ = lean_ctor_get(v_module_3981_, 0);
v___x_3983_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3982_, v_visited_3978_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
lean_inc(v_requestNo_3976_);
v___x_3984_ = l_Lean_JsonNumber_fromNat(v_requestNo_3976_);
v___x_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
v___x_3986_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0));
lean_inc_ref(v_module_3981_);
lean_inc_ref(v___x_3985_);
v___x_3987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3985_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
lean_ctor_set(v___x_3987_, 2, v_module_3981_);
v___x_3988_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v___x_3987_, v_a_3979_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v___x_3989_; 
lean_dec_ref_known(v___x_3988_, 1);
v___x_3989_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3985_, v_a_3979_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___y_3992_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref_known(v___x_3989_, 1);
if (v___x_3983_ == 0)
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_box(0);
lean_inc_ref(v_name_3982_);
v___x_4035_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3982_, v___x_4034_, v_visited_3978_);
v___y_3992_ = v___x_4035_;
goto v___jp_3991_;
}
else
{
v___y_3992_ = v_visited_3978_;
goto v___jp_3991_;
}
v___jp_3991_:
{
lean_object* v_result_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4032_; 
v_result_3993_ = lean_ctor_get(v_a_3990_, 1);
v_isSharedCheck_4032_ = !lean_is_exclusive(v_a_3990_);
if (v_isSharedCheck_4032_ == 0)
{
lean_object* v_unused_4033_; 
v_unused_4033_ = lean_ctor_get(v_a_3990_, 0);
lean_dec(v_unused_4033_);
v___x_3995_ = v_a_3990_;
v_isShared_3996_ = v_isSharedCheck_4032_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_result_3993_);
lean_dec(v_a_3990_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4032_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4001_; 
v___x_3997_ = lean_unsigned_to_nat(1u);
v___x_3998_ = lean_nat_add(v_requestNo_3976_, v___x_3997_);
lean_dec(v_requestNo_3976_);
v___x_3999_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 1, v___x_3999_);
lean_ctor_set(v___x_3995_, 0, v___x_3998_);
v___x_4001_ = v___x_3995_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_3998_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
size_t v_sz_4002_; size_t v___x_4003_; lean_object* v___x_4004_; 
v_sz_4002_ = lean_array_size(v_result_3993_);
v___x_4003_ = ((size_t)0ULL);
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___y_3992_, v_result_3993_, v_sz_4002_, v___x_4003_, v___x_4001_, v_a_3979_);
lean_dec(v_result_3993_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4022_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4007_ = v___x_4004_;
v_isShared_4008_ = v_isSharedCheck_4022_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_4004_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4022_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v_fst_4009_; lean_object* v_snd_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4021_; 
v_fst_4009_ = lean_ctor_get(v_a_4005_, 0);
v_snd_4010_ = lean_ctor_get(v_a_4005_, 1);
v_isSharedCheck_4021_ = !lean_is_exclusive(v_a_4005_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4012_ = v_a_4005_;
v_isShared_4013_ = v_isSharedCheck_4021_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_snd_4010_);
lean_inc(v_fst_4009_);
lean_dec(v_a_4005_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4021_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; lean_object* v___x_4016_; 
v___x_4014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4014_, 0, v_item_3977_);
lean_ctor_set(v___x_4014_, 1, v_snd_4010_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 1, v_fst_4009_);
lean_ctor_set(v___x_4012_, 0, v___x_4014_);
v___x_4016_ = v___x_4012_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v___x_4014_);
lean_ctor_set(v_reuseFailAlloc_4020_, 1, v_fst_4009_);
v___x_4016_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4018_; 
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_4016_);
v___x_4018_ = v___x_4007_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec_ref(v_item_3977_);
v_a_4023_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4004_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4004_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
lean_dec(v_visited_3978_);
lean_dec_ref(v_item_3977_);
lean_dec(v_requestNo_3976_);
v_a_4036_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_3989_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_3989_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec_ref_known(v___x_3985_, 1);
lean_dec(v_visited_3978_);
lean_dec_ref(v_item_3977_);
lean_dec(v_requestNo_3976_);
v_a_4044_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_3988_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_3988_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
else
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
lean_dec(v_visited_3978_);
v___x_4052_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4053_, 0, v_item_3977_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
lean_ctor_set(v___x_4054_, 1, v_requestNo_3976_);
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
return v___x_4055_;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestNo_3976_ = stack[0].m_obj;
lean_object* v_item_3977_ = stack[1].m_obj;
lean_object* v_visited_3978_ = stack[2].m_obj;
lean_object* v_a_3979_ = stack[3].m_obj;
lean_object* v_res_4056_;
v_res_4056_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_requestNo_3976_, v_item_3977_, v_visited_3978_, v_a_3979_);
stack->m_obj
 = v_res_4056_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(lean_object* v___x_4057_, lean_object* v_as_4058_, size_t v_sz_4059_, size_t v_i_4060_, lean_object* v_b_4061_, lean_object* v___y_4062_){
_start:
{
uint8_t v___x_4064_; 
v___x_4064_ = lean_usize_dec_lt(v_i_4060_, v_sz_4059_);
if (v___x_4064_ == 0)
{
lean_object* v___x_4065_; 
lean_dec(v___x_4057_);
v___x_4065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4065_, 0, v_b_4061_);
return v___x_4065_;
}
else
{
lean_object* v_fst_4066_; lean_object* v_snd_4067_; lean_object* v_a_4068_; lean_object* v___x_4069_; 
v_fst_4066_ = lean_ctor_get(v_b_4061_, 0);
lean_inc(v_fst_4066_);
v_snd_4067_ = lean_ctor_get(v_b_4061_, 1);
lean_inc(v_snd_4067_);
lean_dec_ref(v_b_4061_);
v_a_4068_ = lean_array_uget_borrowed(v_as_4058_, v_i_4060_);
lean_inc(v___x_4057_);
lean_inc(v_a_4068_);
v___x_4069_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_fst_4066_, v_a_4068_, v___x_4057_, v___y_4062_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v_fst_4071_; lean_object* v_snd_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4083_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4069_, 1);
v_fst_4071_ = lean_ctor_get(v_a_4070_, 0);
v_snd_4072_ = lean_ctor_get(v_a_4070_, 1);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_a_4070_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4074_ = v_a_4070_;
v_isShared_4075_ = v_isSharedCheck_4083_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_snd_4072_);
lean_inc(v_fst_4071_);
lean_dec(v_a_4070_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4083_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4076_; lean_object* v___x_4078_; 
v___x_4076_ = lean_array_push(v_snd_4067_, v_fst_4071_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 1, v___x_4076_);
lean_ctor_set(v___x_4074_, 0, v_snd_4072_);
v___x_4078_ = v___x_4074_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_snd_4072_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v___x_4076_);
v___x_4078_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
size_t v___x_4079_; size_t v___x_4080_; 
v___x_4079_ = ((size_t)1ULL);
v___x_4080_ = lean_usize_add(v_i_4060_, v___x_4079_);
v_i_4060_ = v___x_4080_;
v_b_4061_ = v___x_4078_;
goto _start;
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec(v_snd_4067_);
lean_dec(v___x_4057_);
v_a_4084_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4069_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4069_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4057_ = stack[0].m_obj;
lean_object* v_as_4058_ = stack[1].m_obj;
size_t v_sz_4059_ = stack[2].m_num;
size_t v_i_4060_ = stack[3].m_num;
lean_object* v_b_4061_ = stack[4].m_obj;
lean_object* v___y_4062_ = stack[5].m_obj;
lean_object* v_res_4092_;
v_res_4092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___x_4057_, v_as_4058_, v_sz_4059_, v_i_4060_, v_b_4061_, v___y_4062_);
stack->m_obj
 = v_res_4092_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1___boxed(lean_object* v___x_4093_, lean_object* v_as_4094_, lean_object* v_sz_4095_, lean_object* v_i_4096_, lean_object* v_b_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
size_t v_sz_boxed_4100_; size_t v_i_boxed_4101_; lean_object* v_res_4102_; 
v_sz_boxed_4100_ = lean_unbox_usize(v_sz_4095_);
lean_dec(v_sz_4095_);
v_i_boxed_4101_ = lean_unbox_usize(v_i_4096_);
lean_dec(v_i_4096_);
v_res_4102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___x_4093_, v_as_4094_, v_sz_boxed_4100_, v_i_boxed_4101_, v_b_4097_, v___y_4098_);
lean_dec_ref(v___y_4098_);
lean_dec_ref(v_as_4094_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___boxed(lean_object* v_requestNo_4103_, lean_object* v_item_4104_, lean_object* v_visited_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_requestNo_4103_, v_item_4104_, v_visited_4105_, v_a_4106_);
lean_dec_ref(v_a_4106_);
return v_res_4108_;
}
}
lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(lean_object* v_requestNo_4109_, lean_object* v_uri_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
lean_inc(v_requestNo_4109_);
v___x_4113_ = l_Lean_JsonNumber_fromNat(v_requestNo_4109_);
v___x_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
v___x_4115_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_4114_);
v___x_4116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4114_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
lean_ctor_set(v___x_4116_, 2, v_uri_4110_);
v___x_4117_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_4116_, v_a_4111_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v___x_4118_; 
lean_dec_ref_known(v___x_4117_, 1);
v___x_4118_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_4114_, v_a_4111_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4177_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4121_ = v___x_4118_;
v_isShared_4122_ = v_isSharedCheck_4177_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4118_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4177_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v_result_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4175_; 
v_result_4123_ = lean_ctor_get(v_a_4119_, 1);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_a_4119_);
if (v_isSharedCheck_4175_ == 0)
{
lean_object* v_unused_4176_; 
v_unused_4176_ = lean_ctor_get(v_a_4119_, 0);
lean_dec(v_unused_4176_);
v___x_4125_ = v_a_4119_;
v_isShared_4126_ = v_isSharedCheck_4175_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_result_4123_);
lean_dec(v_a_4119_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4175_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = lean_unsigned_to_nat(1u);
v___x_4128_ = lean_nat_add(v_requestNo_4109_, v___x_4127_);
lean_dec(v_requestNo_4109_);
if (lean_obj_tag(v_result_4123_) == 1)
{
lean_object* v_val_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4167_; 
lean_del_object(v___x_4121_);
v_val_4129_ = lean_ctor_get(v_result_4123_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v_result_4123_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4131_ = v_result_4123_;
v_isShared_4132_ = v_isSharedCheck_4167_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_val_4129_);
lean_dec(v_result_4123_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4167_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4133_; lean_object* v___x_4135_; 
v___x_4133_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 1, v___x_4133_);
lean_ctor_set(v___x_4125_, 0, v_val_4129_);
v___x_4135_ = v___x_4125_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_val_4129_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = lean_box(1);
v___x_4137_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v___x_4128_, v___x_4135_, v___x_4136_, v_a_4111_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4157_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4140_ = v___x_4137_;
v_isShared_4141_ = v_isSharedCheck_4157_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4137_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4157_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v_fst_4142_; lean_object* v_snd_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4156_; 
v_fst_4142_ = lean_ctor_get(v_a_4138_, 0);
v_snd_4143_ = lean_ctor_get(v_a_4138_, 1);
v_isSharedCheck_4156_ = !lean_is_exclusive(v_a_4138_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4145_ = v_a_4138_;
v_isShared_4146_ = v_isSharedCheck_4156_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_snd_4143_);
lean_inc(v_fst_4142_);
lean_dec(v_a_4138_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4156_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 0, v_fst_4142_);
v___x_4148_ = v___x_4131_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_fst_4142_);
v___x_4148_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
lean_object* v___x_4150_; 
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 0, v___x_4148_);
v___x_4150_ = v___x_4145_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4148_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v_snd_4143_);
v___x_4150_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
lean_object* v___x_4152_; 
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 0, v___x_4150_);
v___x_4152_ = v___x_4140_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4150_);
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
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_del_object(v___x_4131_);
v_a_4158_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4137_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4137_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
}
}
else
{
lean_object* v___x_4168_; lean_object* v___x_4170_; 
lean_dec(v_result_4123_);
v___x_4168_ = lean_box(0);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 1, v___x_4128_);
lean_ctor_set(v___x_4125_, 0, v___x_4168_);
v___x_4170_ = v___x_4125_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4168_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v___x_4128_);
v___x_4170_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
lean_object* v___x_4172_; 
if (v_isShared_4122_ == 0)
{
lean_ctor_set(v___x_4121_, 0, v___x_4170_);
v___x_4172_ = v___x_4121_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
}
else
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
lean_dec(v_requestNo_4109_);
v_a_4178_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4118_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4118_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4178_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_dec_ref_known(v___x_4114_, 1);
lean_dec(v_requestNo_4109_);
v_a_4186_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_4117_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4117_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_0interp(lean_interpreter_value* stack)
{
lean_object* v_requestNo_4109_ = stack[0].m_obj;
lean_object* v_uri_4110_ = stack[1].m_obj;
lean_object* v_a_4111_ = stack[2].m_obj;
lean_object* v_res_4194_;
v_res_4194_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(v_requestNo_4109_, v_uri_4110_, v_a_4111_);
stack->m_obj
 = v_res_4194_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy___boxed(lean_object* v_requestNo_4195_, lean_object* v_uri_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(v_requestNo_4195_, v_uri_4196_, v_a_4197_);
lean_dec_ref(v_a_4197_);
return v_res_4199_;
}
}
lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object* v_lean_4202_, lean_object* v_args_4203_, lean_object* v_test_4204_){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; uint8_t v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4206_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_4207_ = lean_box(0);
v___x_4208_ = ((lean_object*)(l_Lean_Lsp_Ipc_runWith___redArg___closed__0));
v___x_4209_ = 1;
v___x_4210_ = 0;
v___x_4211_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4211_, 0, v___x_4206_);
lean_ctor_set(v___x_4211_, 1, v_lean_4202_);
lean_ctor_set(v___x_4211_, 2, v_args_4203_);
lean_ctor_set(v___x_4211_, 3, v___x_4207_);
lean_ctor_set(v___x_4211_, 4, v___x_4208_);
lean_ctor_set_uint8(v___x_4211_, sizeof(void*)*5, v___x_4209_);
lean_ctor_set_uint8(v___x_4211_, sizeof(void*)*5 + 1, v___x_4210_);
v___x_4212_ = lean_io_process_spawn(v___x_4211_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4214_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
v___x_4214_ = lean_apply_2(v_test_4204_, v_a_4213_, lean_box(0));
return v___x_4214_;
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
lean_dec_ref(v_test_4204_);
v_a_4215_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4212_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4212_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_runWith___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lean_4202_ = stack[0].m_obj;
lean_object* v_args_4203_ = stack[1].m_obj;
lean_object* v_test_4204_ = stack[2].m_obj;
lean_object* v_res_4223_;
v_res_4223_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4202_, v_args_4203_, v_test_4204_);
stack->m_obj
 = v_res_4223_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg___boxed(lean_object* v_lean_4224_, lean_object* v_args_4225_, lean_object* v_test_4226_, lean_object* v_a_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4224_, v_args_4225_, v_test_4226_);
return v_res_4228_;
}
}
lean_object* l_Lean_Lsp_Ipc_runWith(lean_object* v_00_u03b1_4229_, lean_object* v_lean_4230_, lean_object* v_args_4231_, lean_object* v_test_4232_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4230_, v_args_4231_, v_test_4232_);
return v___x_4234_;
}
}
LEAN_EXPORT void l_Lean_Lsp_Ipc_runWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_lean_4230_ = stack[1].m_obj;
lean_object* v_args_4231_ = stack[2].m_obj;
lean_object* v_test_4232_ = stack[3].m_obj;
lean_object* v_res_4235_;
v_res_4235_ = l_Lean_Lsp_Ipc_runWith(lean_box(0), v_lean_4230_, v_args_4231_, v_test_4232_);
stack->m_obj
 = v_res_4235_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___boxed(lean_object* v_00_u03b1_4236_, lean_object* v_lean_4237_, lean_object* v_args_4238_, lean_object* v_test_4239_, lean_object* v_a_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_Lsp_Ipc_runWith(v_00_u03b1_4236_, v_lean_4237_, v_args_4238_, v_test_4239_);
return v_res_4241_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_Communication(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Ipc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
