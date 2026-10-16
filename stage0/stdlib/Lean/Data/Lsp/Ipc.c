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
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonLeanImport_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCallHierarchyIncomingCallsParams_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Data.Lsp.Ipc"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Lsp.Ipc.shutdown"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: result.isNull\n      "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Expected id "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", got id "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "exit"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
v___x_27_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_21_, v_a_26_, v_r_22_);
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
v___x_51_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_45_, v_a_50_, v_n_46_);
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
static lean_object* _init_l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1___closed__0(void){
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1(lean_object* v_msg_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; lean_object* v___f_75_; lean_object* v___x_3067__overap_76_; lean_object* v___x_77_; 
v___x_74_ = lean_obj_once(&l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1___closed__0, &l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1___closed__0_once, _init_l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1___closed__0);
v___f_75_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_75_, 0, v___x_74_);
v___x_3067__overap_76_ = lean_panic_fn_borrowed(v___f_75_, v_msg_71_);
lean_dec_ref(v___f_75_);
lean_inc_ref(v___y_72_);
v___x_77_ = lean_apply_2(v___x_3067__overap_76_, v___y_72_, lean_box(0));
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1___boxed(lean_object* v_msg_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1(v_msg_78_, v___y_79_);
lean_dec_ref(v___y_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__2(lean_object* v_h_82_, lean_object* v_n_83_){
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
lean_dec_ref_known(v___x_96_, 1);
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
v___x_94_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_82_, v___x_93_);
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__2___boxed(lean_object* v_h_107_, lean_object* v_n_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__2(v_h_107_, v_n_108_);
return v_res_110_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_114_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2));
v___x_115_ = lean_unsigned_to_nat(6u);
v___x_116_ = lean_unsigned_to_nat(57u);
v___x_117_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1));
v___x_118_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0));
v___x_119_ = l_mkPanicMessageWithDecl(v___x_118_, v___x_117_, v___x_116_, v___x_115_, v___x_114_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(lean_object* v_a_128_, lean_object* v___x_129_, lean_object* v_requestNo_130_, lean_object* v_a_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_box(0);
lean_inc_ref(v_a_128_);
v___x_135_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_128_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_194_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_194_ == 0)
{
v___x_138_ = v___x_135_;
v_isShared_139_ = v_isSharedCheck_194_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_194_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
if (lean_obj_tag(v_a_136_) == 2)
{
lean_object* v_id_140_; lean_object* v_result_141_; uint8_t v___x_142_; 
v_id_140_ = lean_ctor_get(v_a_136_, 0);
lean_inc(v_id_140_);
v_result_141_ = lean_ctor_get(v_a_136_, 1);
lean_inc(v_result_141_);
lean_dec_ref_known(v_a_136_, 2);
v___x_142_ = l_Lean_Json_isNull(v_result_141_);
lean_dec(v_result_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec(v_id_140_);
lean_del_object(v___x_138_);
v___x_143_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3);
v___x_144_ = l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__1(v___x_143_, v___y_132_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_154_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_154_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
if (lean_obj_tag(v_a_145_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_151_; 
lean_dec_ref(v_a_131_);
lean_dec(v_requestNo_130_);
lean_dec_ref(v_a_128_);
v_a_149_ = lean_ctor_get(v_a_145_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v_a_145_, 1);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v_a_149_);
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
else
{
lean_dec_ref_known(v_a_145_, 1);
lean_del_object(v___x_147_);
goto _start;
}
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec_ref(v_a_131_);
lean_dec(v_requestNo_130_);
lean_dec_ref(v_a_128_);
v_a_155_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_144_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_144_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
else
{
uint8_t v___x_163_; 
lean_dec_ref(v_a_128_);
v___x_163_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_140_, v___x_129_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___y_170_; 
lean_dec_ref(v_a_131_);
v___x_164_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4));
v___x_165_ = l_Nat_reprFast(v_requestNo_130_);
v___x_166_ = lean_string_append(v___x_164_, v___x_165_);
lean_dec_ref(v___x_165_);
v___x_167_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5));
v___x_168_ = lean_string_append(v___x_166_, v___x_167_);
switch(lean_obj_tag(v_id_140_))
{
case 0:
{
lean_object* v_s_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_s_176_ = lean_ctor_get(v_id_140_, 0);
lean_inc_ref(v_s_176_);
lean_dec_ref_known(v_id_140_, 1);
v___x_177_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_178_ = lean_string_append(v___x_177_, v_s_176_);
lean_dec_ref(v_s_176_);
v___x_179_ = lean_string_append(v___x_178_, v___x_177_);
v___y_170_ = v___x_179_;
goto v___jp_169_;
}
case 1:
{
lean_object* v_n_180_; lean_object* v___x_181_; 
v_n_180_ = lean_ctor_get(v_id_140_, 0);
lean_inc_ref(v_n_180_);
lean_dec_ref_known(v_id_140_, 1);
v___x_181_ = l_Lean_JsonNumber_toString(v_n_180_);
v___y_170_ = v___x_181_;
goto v___jp_169_;
}
default: 
{
lean_object* v___x_182_; 
v___x_182_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_170_ = v___x_182_;
goto v___jp_169_;
}
}
v___jp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_171_ = lean_string_append(v___x_168_, v___y_170_);
lean_dec_ref(v___y_170_);
v___x_172_ = lean_mk_io_user_error(v___x_171_);
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 1);
lean_ctor_set(v___x_138_, 0, v___x_172_);
v___x_174_ = v___x_138_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_id_140_);
lean_del_object(v___x_138_);
lean_dec(v_requestNo_130_);
v___x_183_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___x_184_ = l_Lean_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__2(v_a_131_, v___x_183_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_191_ == 0)
{
lean_object* v_unused_192_; 
v_unused_192_ = lean_ctor_get(v___x_184_, 0);
lean_dec(v_unused_192_);
v___x_186_ = v___x_184_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_dec(v___x_184_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_134_);
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_134_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
else
{
return v___x_184_;
}
}
}
}
else
{
lean_del_object(v___x_138_);
lean_dec(v_a_136_);
goto _start;
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec_ref(v_a_131_);
lean_dec(v_requestNo_130_);
lean_dec_ref(v_a_128_);
v_a_195_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_135_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_135_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___boxed(lean_object* v_a_203_, lean_object* v___x_204_, lean_object* v_requestNo_205_, lean_object* v_a_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_203_, v___x_204_, v_requestNo_205_, v_a_206_, v___y_207_);
lean_dec_ref(v___y_207_);
lean_dec(v___x_204_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(lean_object* v_h_210_, lean_object* v_r_211_){
_start:
{
lean_object* v_id_213_; lean_object* v_method_214_; lean_object* v_param_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_235_; 
v_id_213_ = lean_ctor_get(v_r_211_, 0);
v_method_214_ = lean_ctor_get(v_r_211_, 1);
v_param_215_ = lean_ctor_get(v_r_211_, 2);
v_isSharedCheck_235_ = !lean_is_exclusive(v_r_211_);
if (v_isSharedCheck_235_ == 0)
{
v___x_217_ = v_r_211_;
v_isShared_218_ = v_isSharedCheck_235_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_param_215_);
lean_inc(v_method_214_);
lean_inc(v_id_213_);
lean_dec(v_r_211_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_235_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___y_220_; lean_object* v___x_225_; 
v___x_225_ = l_Lean_Json_Structured_fromJson_x3f(v_param_215_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v___x_226_; 
lean_dec_ref_known(v___x_225_, 1);
v___x_226_ = lean_box(0);
v___y_220_ = v___x_226_;
goto v___jp_219_;
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_a_227_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_225_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_225_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
v___y_220_ = v___x_232_;
goto v___jp_219_;
}
}
}
v___jp_219_:
{
lean_object* v___x_222_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 2, v___y_220_);
v___x_222_ = v___x_217_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_id_213_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_method_214_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v___y_220_);
v___x_222_ = v_reuseFailAlloc_224_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_210_, v___x_222_);
return v___x_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0___boxed(lean_object* v_h_236_, lean_object* v_r_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(v_h_236_, v_r_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object* v_requestNo_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_244_; lean_object* v_a_245_; lean_object* v___x_246_; lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_269_; 
v___x_244_ = l_Lean_Lsp_Ipc_stdout(v_a_242_);
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref(v___x_244_);
v___x_246_ = l_Lean_Lsp_Ipc_stdin(v_a_242_);
v_a_247_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_269_ == 0)
{
v___x_249_ = v___x_246_;
v_isShared_250_ = v_isSharedCheck_269_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_269_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
lean_inc(v_requestNo_241_);
v___x_251_ = l_Lean_JsonNumber_fromNat(v_requestNo_241_);
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 1);
lean_ctor_set(v___x_249_, 0, v___x_251_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_268_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = ((lean_object*)(l_Lean_Lsp_Ipc_shutdown___closed__0));
v___x_255_ = lean_box(0);
lean_inc_ref(v___x_253_);
v___x_256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_256_, 0, v___x_253_);
lean_ctor_set(v___x_256_, 1, v___x_254_);
lean_ctor_set(v___x_256_, 2, v___x_255_);
lean_inc(v_a_247_);
v___x_257_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(v_a_247_, v___x_256_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref_known(v___x_257_, 1);
v___x_258_ = lean_box(0);
v___x_259_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_245_, v___x_253_, v_requestNo_241_, v_a_247_, v_a_242_);
lean_dec_ref(v___x_253_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v___x_259_, 0);
lean_dec(v_unused_267_);
v___x_261_ = v___x_259_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_dec(v___x_259_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_258_);
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_258_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
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
lean_dec_ref(v___x_253_);
lean_dec(v_a_247_);
lean_dec(v_a_245_);
lean_dec(v_requestNo_241_);
return v___x_257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown___boxed(lean_object* v_requestNo_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Lsp_Ipc_shutdown(v_requestNo_270_, v_a_271_);
lean_dec_ref(v_a_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object* v_v_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Json_Structured_fromJson_x3f(v_v_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(lean_object* v_a_276_, lean_object* v___x_277_, lean_object* v_requestNo_278_, lean_object* v_a_279_, lean_object* v_inst_280_, lean_object* v_a_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_276_, v___x_277_, v_requestNo_278_, v_a_279_, v___y_282_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___boxed(lean_object* v_a_285_, lean_object* v___x_286_, lean_object* v_requestNo_287_, lean_object* v_a_288_, lean_object* v_inst_289_, lean_object* v_a_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(v_a_285_, v___x_286_, v_requestNo_287_, v_a_288_, v_inst_289_, v_a_290_, v___y_291_);
lean_dec_ref(v___y_291_);
lean_dec(v___x_286_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object* v_a_294_){
_start:
{
lean_object* v___x_296_; lean_object* v_a_297_; lean_object* v___x_298_; 
v___x_296_ = l_Lean_Lsp_Ipc_stdout(v_a_294_);
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref(v___x_296_);
v___x_298_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage___boxed(lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Lsp_Ipc_readMessage(v_a_299_);
lean_dec_ref(v_a_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg(lean_object* v_expectedMethod_302_, lean_object* v_inst_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_a_307_; lean_object* v___x_308_; 
v___x_306_ = l_Lean_Lsp_Ipc_stdout(v_a_304_);
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref(v___x_306_);
v___x_308_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_a_307_, v_expectedMethod_302_, v_inst_303_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg___boxed(lean_object* v_expectedMethod_309_, lean_object* v_inst_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Lsp_Ipc_readRequestAs___redArg(v_expectedMethod_309_, v_inst_310_, v_a_311_);
lean_dec_ref(v_a_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object* v_expectedMethod_314_, lean_object* v_00_u03b1_315_, lean_object* v_inst_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Lsp_Ipc_readRequestAs___redArg(v_expectedMethod_314_, v_inst_316_, v_a_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___boxed(lean_object* v_expectedMethod_320_, lean_object* v_00_u03b1_321_, lean_object* v_inst_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Lsp_Ipc_readRequestAs(v_expectedMethod_320_, v_00_u03b1_321_, v_inst_322_, v_a_323_);
lean_dec_ref(v_a_323_);
return v_res_325_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(32700u);
v___x_344_ = lean_nat_to_int(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14);
v___x_346_ = lean_int_neg(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15);
v___x_348_ = l_Lean_JsonNumber_fromInt(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16);
v___x_350_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(32600u);
v___x_352_ = lean_nat_to_int(v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18);
v___x_354_ = lean_int_neg(v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19);
v___x_356_ = l_Lean_JsonNumber_fromInt(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20);
v___x_358_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(32601u);
v___x_360_ = lean_nat_to_int(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22);
v___x_362_ = lean_int_neg(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23);
v___x_364_ = l_Lean_JsonNumber_fromInt(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24);
v___x_366_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(32602u);
v___x_368_ = lean_nat_to_int(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26);
v___x_370_ = lean_int_neg(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27);
v___x_372_ = l_Lean_JsonNumber_fromInt(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28);
v___x_374_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(32603u);
v___x_376_ = lean_nat_to_int(v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30);
v___x_378_ = lean_int_neg(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31);
v___x_380_ = l_Lean_JsonNumber_fromInt(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32);
v___x_382_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(32002u);
v___x_384_ = lean_nat_to_int(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34);
v___x_386_ = lean_int_neg(v___x_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35);
v___x_388_ = l_Lean_JsonNumber_fromInt(v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36);
v___x_390_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(32001u);
v___x_392_ = lean_nat_to_int(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38);
v___x_394_ = lean_int_neg(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39);
v___x_396_ = l_Lean_JsonNumber_fromInt(v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40);
v___x_398_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_unsigned_to_nat(32801u);
v___x_400_ = lean_nat_to_int(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42);
v___x_402_ = lean_int_neg(v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43);
v___x_404_ = l_Lean_JsonNumber_fromInt(v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44);
v___x_406_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(32800u);
v___x_408_ = lean_nat_to_int(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46);
v___x_410_ = lean_int_neg(v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47);
v___x_412_ = l_Lean_JsonNumber_fromInt(v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48);
v___x_414_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(32900u);
v___x_416_ = lean_nat_to_int(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50);
v___x_418_ = lean_int_neg(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51);
v___x_420_ = l_Lean_JsonNumber_fromInt(v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52);
v___x_422_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_unsigned_to_nat(32901u);
v___x_424_ = lean_nat_to_int(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54);
v___x_426_ = lean_int_neg(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55);
v___x_428_ = l_Lean_JsonNumber_fromInt(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56);
v___x_430_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = lean_unsigned_to_nat(32902u);
v___x_432_ = lean_nat_to_int(v___x_431_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58);
v___x_434_ = lean_int_neg(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59);
v___x_436_ = l_Lean_JsonNumber_fromInt(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60);
v___x_438_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg(lean_object* v_expectedID_439_, lean_object* v_inst_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Lsp_Ipc_stdout(v_a_441_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_588_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_588_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_588_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_588_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_444_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_579_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_579_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_579_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_579_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___y_454_; lean_object* v___y_455_; 
switch(lean_obj_tag(v_a_449_))
{
case 2:
{
lean_object* v_id_461_; lean_object* v_result_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_506_; 
v_id_461_ = lean_ctor_get(v_a_449_, 0);
v_result_462_ = lean_ctor_get(v_a_449_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_a_449_);
if (v_isSharedCheck_506_ == 0)
{
v___x_464_ = v_a_449_;
v_isShared_465_ = v_isSharedCheck_506_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_result_462_);
lean_inc(v_id_461_);
lean_dec(v_a_449_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_506_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_461_, v_expectedID_439_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___y_469_; 
lean_del_object(v___x_464_);
lean_dec(v_result_462_);
lean_del_object(v___x_446_);
lean_dec_ref(v_inst_440_);
v___x_467_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4));
switch(lean_obj_tag(v_expectedID_439_))
{
case 0:
{
lean_object* v_s_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_s_480_ = lean_ctor_get(v_expectedID_439_, 0);
lean_inc_ref(v_s_480_);
lean_dec_ref_known(v_expectedID_439_, 1);
v___x_481_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_482_ = lean_string_append(v___x_481_, v_s_480_);
lean_dec_ref(v_s_480_);
v___x_483_ = lean_string_append(v___x_482_, v___x_481_);
v___y_469_ = v___x_483_;
goto v___jp_468_;
}
case 1:
{
lean_object* v_n_484_; lean_object* v___x_485_; 
v_n_484_ = lean_ctor_get(v_expectedID_439_, 0);
lean_inc_ref(v_n_484_);
lean_dec_ref_known(v_expectedID_439_, 1);
v___x_485_ = l_Lean_JsonNumber_toString(v_n_484_);
v___y_469_ = v___x_485_;
goto v___jp_468_;
}
default: 
{
lean_object* v___x_486_; 
v___x_486_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_469_ = v___x_486_;
goto v___jp_468_;
}
}
v___jp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_string_append(v___x_467_, v___y_469_);
lean_dec_ref(v___y_469_);
v___x_471_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5));
v___x_472_ = lean_string_append(v___x_470_, v___x_471_);
switch(lean_obj_tag(v_id_461_))
{
case 0:
{
lean_object* v_s_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_s_473_ = lean_ctor_get(v_id_461_, 0);
lean_inc_ref(v_s_473_);
lean_dec_ref_known(v_id_461_, 1);
v___x_474_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_475_ = lean_string_append(v___x_474_, v_s_473_);
lean_dec_ref(v_s_473_);
v___x_476_ = lean_string_append(v___x_475_, v___x_474_);
v___y_454_ = v___x_472_;
v___y_455_ = v___x_476_;
goto v___jp_453_;
}
case 1:
{
lean_object* v_n_477_; lean_object* v___x_478_; 
v_n_477_ = lean_ctor_get(v_id_461_, 0);
lean_inc_ref(v_n_477_);
lean_dec_ref_known(v_id_461_, 1);
v___x_478_ = l_Lean_JsonNumber_toString(v_n_477_);
v___y_454_ = v___x_472_;
v___y_455_ = v___x_478_;
goto v___jp_453_;
}
default: 
{
lean_object* v___x_479_; 
v___x_479_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_454_ = v___x_472_;
v___y_455_ = v___x_479_;
goto v___jp_453_;
}
}
}
}
else
{
lean_object* v___x_487_; 
lean_dec(v_id_461_);
lean_del_object(v___x_451_);
lean_inc(v_result_462_);
v___x_487_ = lean_apply_1(v_inst_440_, v_result_462_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
lean_del_object(v___x_464_);
lean_dec(v_expectedID_439_);
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
v___x_489_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_490_ = l_Lean_Json_compress(v_result_462_);
v___x_491_ = lean_string_append(v___x_489_, v___x_490_);
lean_dec_ref(v___x_490_);
v___x_492_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_493_ = lean_string_append(v___x_491_, v___x_492_);
v___x_494_ = lean_string_append(v___x_493_, v_a_488_);
lean_dec(v_a_488_);
v___x_495_ = lean_mk_io_user_error(v___x_494_);
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 1);
lean_ctor_set(v___x_446_, 0, v___x_495_);
v___x_497_ = v___x_446_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; 
lean_dec(v_result_462_);
v_a_499_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_487_, 1);
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 0);
lean_ctor_set(v___x_464_, 1, v_a_499_);
lean_ctor_set(v___x_464_, 0, v_expectedID_439_);
v___x_501_ = v___x_464_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_expectedID_439_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_a_499_);
v___x_501_ = v_reuseFailAlloc_505_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_503_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_501_);
v___x_503_ = v___x_446_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_507_; uint8_t v_code_508_; lean_object* v_message_509_; lean_object* v_data_x3f_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___x_543_; lean_object* v___y_545_; 
lean_del_object(v___x_451_);
lean_dec_ref(v_inst_440_);
lean_dec(v_expectedID_439_);
v_id_507_ = lean_ctor_get(v_a_449_, 0);
lean_inc(v_id_507_);
v_code_508_ = lean_ctor_get_uint8(v_a_449_, sizeof(void*)*3);
v_message_509_ = lean_ctor_get(v_a_449_, 1);
lean_inc_ref(v_message_509_);
v_data_x3f_510_ = lean_ctor_get(v_a_449_, 2);
lean_inc(v_data_x3f_510_);
lean_dec_ref_known(v_a_449_, 3);
v___x_511_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_512_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3));
v___x_513_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_543_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_507_))
{
case 0:
{
lean_object* v_s_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_s_561_ = lean_ctor_get(v_id_507_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_id_507_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v_id_507_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_s_561_);
lean_dec(v_id_507_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 3);
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_s_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
v___y_545_ = v___x_566_;
goto v___jp_544_;
}
}
}
case 1:
{
lean_object* v_n_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
v_n_569_ = lean_ctor_get(v_id_507_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v_id_507_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v_id_507_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_n_569_);
lean_dec(v_id_507_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 2);
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_n_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
v___y_545_ = v___x_574_;
goto v___jp_544_;
}
}
}
default: 
{
lean_object* v___x_577_; 
v___x_577_ = lean_box(0);
v___y_545_ = v___x_577_;
goto v___jp_544_;
}
}
v___jp_514_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
v___x_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_519_, 0, v___y_517_);
lean_ctor_set(v___x_519_, 1, v___y_518_);
v___x_520_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_521_, 0, v_message_509_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = lean_box(0);
v___x_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_519_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_527_ = l_Lean_Json_opt___redArg(v___x_512_, v___x_526_, v_data_x3f_510_);
v___x_528_ = l_List_appendTR___redArg(v___x_525_, v___x_527_);
v___x_529_ = l_Lean_Json_mkObj(v___x_528_);
lean_dec(v___x_528_);
lean_inc_ref(v___y_516_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___y_516_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_523_);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___y_515_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_513_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = l_Lean_Json_mkObj(v___x_533_);
lean_dec_ref_known(v___x_533_, 2);
v___x_535_ = l_Lean_Json_compress(v___x_534_);
v___x_536_ = lean_string_append(v___x_511_, v___x_535_);
lean_dec_ref(v___x_535_);
v___x_537_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_538_ = lean_string_append(v___x_536_, v___x_537_);
v___x_539_ = lean_mk_io_user_error(v___x_538_);
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 1);
lean_ctor_set(v___x_446_, 0, v___x_539_);
v___x_541_ = v___x_446_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
v___jp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_543_);
lean_ctor_set(v___x_546_, 1, v___y_545_);
v___x_547_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_548_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_508_)
{
case 0:
{
lean_object* v___x_549_; 
v___x_549_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_549_;
goto v___jp_514_;
}
case 1:
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_550_;
goto v___jp_514_;
}
case 2:
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_551_;
goto v___jp_514_;
}
case 3:
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_552_;
goto v___jp_514_;
}
case 4:
{
lean_object* v___x_553_; 
v___x_553_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_553_;
goto v___jp_514_;
}
case 5:
{
lean_object* v___x_554_; 
v___x_554_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_554_;
goto v___jp_514_;
}
case 6:
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_555_;
goto v___jp_514_;
}
case 7:
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_556_;
goto v___jp_514_;
}
case 8:
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_557_;
goto v___jp_514_;
}
case 9:
{
lean_object* v___x_558_; 
v___x_558_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_558_;
goto v___jp_514_;
}
case 10:
{
lean_object* v___x_559_; 
v___x_559_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_559_;
goto v___jp_514_;
}
default: 
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
v___y_518_ = v___x_560_;
goto v___jp_514_;
}
}
}
}
default: 
{
lean_del_object(v___x_451_);
lean_dec(v_a_449_);
lean_del_object(v___x_446_);
goto _start;
}
}
v___jp_453_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_456_ = lean_string_append(v___y_454_, v___y_455_);
lean_dec_ref(v___y_455_);
v___x_457_ = lean_mk_io_user_error(v___x_456_);
if (v_isShared_452_ == 0)
{
lean_ctor_set_tag(v___x_451_, 1);
lean_ctor_set(v___x_451_, 0, v___x_457_);
v___x_459_ = v___x_451_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_del_object(v___x_446_);
lean_dec_ref(v_inst_440_);
lean_dec(v_expectedID_439_);
v_a_580_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_448_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_448_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v_inst_440_);
lean_dec(v_expectedID_439_);
v_a_589_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_443_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_443_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___boxed(lean_object* v_expectedID_597_, lean_object* v_inst_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Lsp_Ipc_readResponseAs___redArg(v_expectedID_597_, v_inst_598_, v_a_599_);
lean_dec_ref(v_a_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object* v_expectedID_602_, lean_object* v_00_u03b1_603_, lean_object* v_inst_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Lsp_Ipc_readResponseAs___redArg(v_expectedID_602_, v_inst_604_, v_a_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___boxed(lean_object* v_expectedID_608_, lean_object* v_00_u03b1_609_, lean_object* v_inst_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Lsp_Ipc_readResponseAs(v_expectedID_608_, v_00_u03b1_609_, v_inst_610_, v_a_611_);
lean_dec_ref(v_a_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object* v_a_614_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_617_ = lean_io_process_child_wait(v___x_616_, v_a_614_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Lsp_Ipc_waitForExit(v_a_618_);
lean_dec_ref(v_a_618_);
return v_res_620_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(lean_object* v_d1_621_, lean_object* v_d2_622_){
_start:
{
uint8_t v___y_624_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d1_621_);
v___x_628_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d2_622_);
v___x_629_ = l_Lean_Lsp_instOrdRange_ord(v___x_627_, v___x_628_);
lean_dec_ref(v___x_628_);
lean_dec_ref(v___x_627_);
if (v___x_629_ == 1)
{
lean_object* v_message_630_; lean_object* v_message_631_; uint8_t v___x_632_; 
v_message_630_ = lean_ctor_get(v_d1_621_, 6);
v_message_631_ = lean_ctor_get(v_d2_622_, 6);
v___x_632_ = lean_string_compare(v_message_630_, v_message_631_);
v___y_624_ = v___x_632_;
goto v___jp_623_;
}
else
{
v___y_624_ = v___x_629_;
goto v___jp_623_;
}
v___jp_623_:
{
if (v___y_624_ == 2)
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
else
{
uint8_t v___x_626_; 
v___x_626_ = 1;
return v___x_626_;
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
lean_object* v_uri_639_; lean_object* v_version_x3f_640_; lean_object* v_isIncremental_x3f_641_; lean_object* v_diagnostics_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_653_; 
v_uri_639_ = lean_ctor_get(v_p_638_, 0);
v_version_x3f_640_ = lean_ctor_get(v_p_638_, 1);
v_isIncremental_x3f_641_ = lean_ctor_get(v_p_638_, 2);
v_diagnostics_642_ = lean_ctor_get(v_p_638_, 3);
v_isSharedCheck_653_ = !lean_is_exclusive(v_p_638_);
if (v_isSharedCheck_653_ == 0)
{
v___x_644_ = v_p_638_;
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_diagnostics_642_);
lean_inc(v_isIncremental_x3f_641_);
lean_inc(v_version_x3f_640_);
lean_inc(v_uri_639_);
lean_dec(v_p_638_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___f_646_; lean_object* v___x_647_; lean_object* v_sorted_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v___f_646_ = ((lean_object*)(l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0));
v___x_647_ = lean_array_to_list(v_diagnostics_642_);
v_sorted_648_ = l_List_mergeSort___redArg(v___x_647_, v___f_646_);
v___x_649_ = lean_array_mk(v_sorted_648_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 3, v___x_649_);
v___x_651_ = v___x_644_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_uri_639_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_version_x3f_640_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_isIncremental_x3f_641_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(lean_object* v_prev_x3f_657_, lean_object* v_next_658_){
_start:
{
lean_object* v_uri_659_; lean_object* v_version_x3f_660_; lean_object* v_isIncremental_x3f_661_; lean_object* v_diagnostics_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_685_; 
v_uri_659_ = lean_ctor_get(v_next_658_, 0);
v_version_x3f_660_ = lean_ctor_get(v_next_658_, 1);
v_isIncremental_x3f_661_ = lean_ctor_get(v_next_658_, 2);
v_diagnostics_662_ = lean_ctor_get(v_next_658_, 3);
v_isSharedCheck_685_ = !lean_is_exclusive(v_next_658_);
if (v_isSharedCheck_685_ == 0)
{
v___x_664_ = v_next_658_;
v_isShared_665_ = v_isSharedCheck_685_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_diagnostics_662_);
lean_inc(v_isIncremental_x3f_661_);
lean_inc(v_version_x3f_660_);
lean_inc(v_uri_659_);
lean_dec(v_next_658_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_685_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v_replace_668_; 
v___x_666_ = ((lean_object*)(l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams___closed__0));
lean_inc_ref(v_diagnostics_662_);
lean_inc(v_version_x3f_660_);
lean_inc_ref(v_uri_659_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 2, v___x_666_);
v_replace_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_uri_659_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_version_x3f_660_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_diagnostics_662_);
v_replace_668_ = v_reuseFailAlloc_684_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
if (lean_obj_tag(v_prev_x3f_657_) == 1)
{
if (lean_obj_tag(v_isIncremental_x3f_661_) == 0)
{
lean_dec_ref_known(v_prev_x3f_657_, 1);
lean_dec_ref(v_diagnostics_662_);
lean_dec(v_version_x3f_660_);
lean_dec_ref(v_uri_659_);
return v_replace_668_;
}
else
{
lean_object* v_val_669_; uint8_t v___x_670_; 
v_val_669_ = lean_ctor_get(v_isIncremental_x3f_661_, 0);
lean_inc(v_val_669_);
lean_dec_ref_known(v_isIncremental_x3f_661_, 1);
v___x_670_ = lean_unbox(v_val_669_);
lean_dec(v_val_669_);
if (v___x_670_ == 0)
{
lean_dec_ref_known(v_prev_x3f_657_, 1);
lean_dec_ref(v_diagnostics_662_);
lean_dec(v_version_x3f_660_);
lean_dec_ref(v_uri_659_);
return v_replace_668_;
}
else
{
lean_object* v_val_671_; lean_object* v_diagnostics_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_replace_668_);
v_val_671_ = lean_ctor_get(v_prev_x3f_657_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v_prev_x3f_657_, 1);
v_diagnostics_672_ = lean_ctor_get(v_val_671_, 3);
v_isSharedCheck_680_ = !lean_is_exclusive(v_val_671_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; lean_object* v_unused_682_; lean_object* v_unused_683_; 
v_unused_681_ = lean_ctor_get(v_val_671_, 2);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_val_671_, 1);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_val_671_, 0);
lean_dec(v_unused_683_);
v___x_674_ = v_val_671_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_diagnostics_672_);
lean_dec(v_val_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = l_Array_append___redArg(v_diagnostics_672_, v_diagnostics_662_);
lean_dec_ref(v_diagnostics_662_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 3, v___x_676_);
lean_ctor_set(v___x_674_, 2, v___x_666_);
lean_ctor_set(v___x_674_, 1, v_version_x3f_660_);
lean_ctor_set(v___x_674_, 0, v_uri_659_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_uri_659_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_version_x3f_660_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
else
{
lean_dec_ref(v_diagnostics_662_);
lean_dec(v_isIncremental_x3f_661_);
lean_dec(v_version_x3f_660_);
lean_dec_ref(v_uri_659_);
lean_dec(v_prev_x3f_657_);
return v_replace_668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object* v_waitForDiagnosticsId_689_, lean_object* v_accumulated_x3f_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Lsp_Ipc_readMessage(v_a_691_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_763_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_763_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_763_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_763_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
switch(lean_obj_tag(v_a_694_))
{
case 2:
{
lean_object* v_id_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_724_; 
v_id_698_ = lean_ctor_get(v_a_694_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_a_694_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v_a_694_, 1);
lean_dec(v_unused_725_);
v___x_700_ = v_a_694_;
v_isShared_701_ = v_isSharedCheck_724_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_id_698_);
lean_dec(v_a_694_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_724_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
uint8_t v___x_702_; 
v___x_702_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_698_, v_waitForDiagnosticsId_689_);
lean_dec(v_id_698_);
if (v___x_702_ == 0)
{
lean_del_object(v___x_700_);
lean_del_object(v___x_696_);
goto _start;
}
else
{
if (lean_obj_tag(v_accumulated_x3f_690_) == 0)
{
lean_object* v___x_704_; lean_object* v___x_706_; 
lean_del_object(v___x_700_);
v___x_704_ = lean_box(0);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_704_);
v___x_706_ = v___x_696_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
else
{
lean_object* v_val_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_723_; 
v_val_708_ = lean_ctor_get(v_accumulated_x3f_690_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_accumulated_x3f_690_);
if (v_isSharedCheck_723_ == 0)
{
v___x_710_ = v_accumulated_x3f_690_;
v_isShared_711_ = v_isSharedCheck_723_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_val_708_);
lean_dec(v_accumulated_x3f_690_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_723_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_712_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_713_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(v_val_708_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
lean_ctor_set(v___x_700_, 1, v___x_713_);
lean_ctor_set(v___x_700_, 0, v___x_712_);
v___x_715_ = v___x_700_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_713_);
v___x_715_ = v_reuseFailAlloc_722_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_715_);
v___x_717_ = v___x_710_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_717_);
v___x_719_ = v___x_696_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
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
lean_object* v_id_726_; lean_object* v_message_727_; uint8_t v___x_728_; 
v_id_726_ = lean_ctor_get(v_a_694_, 0);
lean_inc(v_id_726_);
v_message_727_ = lean_ctor_get(v_a_694_, 1);
lean_inc_ref(v_message_727_);
lean_dec_ref_known(v_a_694_, 3);
v___x_728_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_726_, v_waitForDiagnosticsId_689_);
lean_dec(v_id_726_);
if (v___x_728_ == 0)
{
lean_dec_ref(v_message_727_);
lean_del_object(v___x_696_);
goto _start;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
lean_dec(v_accumulated_x3f_690_);
v___x_730_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1));
v___x_731_ = lean_string_append(v___x_730_, v_message_727_);
lean_dec_ref(v_message_727_);
v___x_732_ = lean_mk_io_user_error(v___x_731_);
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 1);
lean_ctor_set(v___x_696_, 0, v___x_732_);
v___x_734_ = v___x_696_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
case 1:
{
lean_object* v_method_736_; lean_object* v_params_x3f_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_method_736_ = lean_ctor_get(v_a_694_, 0);
lean_inc_ref(v_method_736_);
v_params_x3f_737_ = lean_ctor_get(v_a_694_, 1);
lean_inc(v_params_x3f_737_);
lean_dec_ref_known(v_a_694_, 2);
v___x_738_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_739_ = lean_string_dec_eq(v_method_736_, v___x_738_);
lean_dec_ref(v_method_736_);
if (v___x_739_ == 0)
{
lean_dec(v_params_x3f_737_);
lean_del_object(v___x_696_);
goto _start;
}
else
{
if (lean_obj_tag(v_params_x3f_737_) == 1)
{
lean_object* v_val_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_760_; 
v_val_741_ = lean_ctor_get(v_params_x3f_737_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_params_x3f_737_);
if (v_isSharedCheck_760_ == 0)
{
v___x_743_ = v_params_x3f_737_;
v_isShared_744_ = v_isSharedCheck_760_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_val_741_);
lean_dec(v_params_x3f_737_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_760_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = l_Lean_Json_Structured_toJson(v_val_741_);
v___x_746_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(v___x_745_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
lean_del_object(v___x_743_);
lean_dec(v_accumulated_x3f_690_);
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2));
v___x_749_ = lean_string_append(v___x_748_, v_a_747_);
lean_dec(v_a_747_);
v___x_750_ = lean_mk_io_user_error(v___x_749_);
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 1);
lean_ctor_set(v___x_696_, 0, v___x_750_);
v___x_752_ = v___x_696_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
lean_del_object(v___x_696_);
v_a_754_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_746_, 1);
v___x_755_ = l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(v_accumulated_x3f_690_, v_a_754_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_755_);
v___x_757_ = v___x_743_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_759_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
v_accumulated_x3f_690_ = v___x_757_;
goto _start;
}
}
}
}
else
{
lean_dec(v_params_x3f_737_);
lean_del_object(v___x_696_);
goto _start;
}
}
}
default: 
{
lean_del_object(v___x_696_);
lean_dec(v_a_694_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_accumulated_x3f_690_);
v_a_764_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_693_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_693_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object* v_waitForDiagnosticsId_772_, lean_object* v_accumulated_x3f_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_772_, v_accumulated_x3f_773_, v_a_774_);
lean_dec_ref(v_a_774_);
lean_dec(v_waitForDiagnosticsId_772_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(lean_object* v_v_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(v_v_777_);
v___x_779_ = l_Lean_Json_Structured_fromJson_x3f(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object* v_h_780_, lean_object* v_r_781_){
_start:
{
lean_object* v_id_783_; lean_object* v_method_784_; lean_object* v_param_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_805_; 
v_id_783_ = lean_ctor_get(v_r_781_, 0);
v_method_784_ = lean_ctor_get(v_r_781_, 1);
v_param_785_ = lean_ctor_get(v_r_781_, 2);
v_isSharedCheck_805_ = !lean_is_exclusive(v_r_781_);
if (v_isSharedCheck_805_ == 0)
{
v___x_787_ = v_r_781_;
v_isShared_788_ = v_isSharedCheck_805_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_param_785_);
lean_inc(v_method_784_);
lean_inc(v_id_783_);
lean_dec(v_r_781_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_805_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___y_790_; lean_object* v___x_795_; 
v___x_795_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(v_param_785_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; 
lean_dec_ref_known(v___x_795_, 1);
v___x_796_ = lean_box(0);
v___y_790_ = v___x_796_;
goto v___jp_789_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_a_797_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_795_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
v___y_790_ = v___x_802_;
goto v___jp_789_;
}
}
}
v___jp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 2, v___y_790_);
v___x_792_ = v___x_787_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_id_783_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_method_784_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v___y_790_);
v___x_792_ = v_reuseFailAlloc_794_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_780_, v___x_792_);
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0___boxed(lean_object* v_h_806_, lean_object* v_r_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_h_806_, v_r_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object* v_r_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___x_813_; lean_object* v_a_814_; lean_object* v___x_815_; 
v___x_813_ = l_Lean_Lsp_Ipc_stdin(v_a_811_);
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref(v___x_813_);
v___x_815_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_a_814_, v_r_810_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0___boxed(lean_object* v_r_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v_r_816_, v_a_817_);
lean_dec_ref(v_a_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object* v_waitForDiagnosticsId_821_, lean_object* v_target_822_, lean_object* v_version_823_, lean_object* v_a_824_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_826_ = ((lean_object*)(l_Lean_Lsp_Ipc_collectDiagnostics___closed__0));
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v_target_822_);
lean_ctor_set(v___x_827_, 1, v_version_823_);
lean_inc(v_waitForDiagnosticsId_821_);
v___x_828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_828_, 0, v_waitForDiagnosticsId_821_);
lean_ctor_set(v___x_828_, 1, v___x_826_);
lean_ctor_set(v___x_828_, 2, v___x_827_);
v___x_829_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v___x_828_, v_a_824_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec_ref_known(v___x_829_, 1);
v___x_830_ = lean_box(0);
v___x_831_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_821_, v___x_830_, v_a_824_);
lean_dec(v_waitForDiagnosticsId_821_);
return v___x_831_;
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_waitForDiagnosticsId_821_);
v_a_832_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_829_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_829_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___boxed(lean_object* v_waitForDiagnosticsId_840_, lean_object* v_target_841_, lean_object* v_version_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Lsp_Ipc_collectDiagnostics(v_waitForDiagnosticsId_840_, v_target_841_, v_version_842_, v_a_843_);
lean_dec_ref(v_a_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(lean_object* v_v_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(v_v_846_);
v___x_848_ = l_Lean_Json_Structured_fromJson_x3f(v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object* v_h_849_, lean_object* v_r_850_){
_start:
{
lean_object* v_id_852_; lean_object* v_method_853_; lean_object* v_param_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_874_; 
v_id_852_ = lean_ctor_get(v_r_850_, 0);
v_method_853_ = lean_ctor_get(v_r_850_, 1);
v_param_854_ = lean_ctor_get(v_r_850_, 2);
v_isSharedCheck_874_ = !lean_is_exclusive(v_r_850_);
if (v_isSharedCheck_874_ == 0)
{
v___x_856_ = v_r_850_;
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_param_854_);
lean_inc(v_method_853_);
lean_inc(v_id_852_);
lean_dec(v_r_850_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_874_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___y_859_; lean_object* v___x_864_; 
v___x_864_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(v_param_854_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v___x_865_; 
lean_dec_ref_known(v___x_864_, 1);
v___x_865_ = lean_box(0);
v___y_859_ = v___x_865_;
goto v___jp_858_;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_a_866_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_864_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_864_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
v___y_859_ = v___x_871_;
goto v___jp_858_;
}
}
}
v___jp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 2, v___y_859_);
v___x_861_ = v___x_856_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_id_852_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_method_853_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v___y_859_);
v___x_861_ = v_reuseFailAlloc_863_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_849_, v___x_861_);
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0___boxed(lean_object* v_h_875_, lean_object* v_r_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_h_875_, v_r_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object* v_r_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; lean_object* v_a_883_; lean_object* v___x_884_; 
v___x_882_ = l_Lean_Lsp_Ipc_stdin(v_a_880_);
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v___x_882_);
v___x_884_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_a_883_, v_r_879_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0___boxed(lean_object* v_r_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v_r_885_, v_a_886_);
lean_dec_ref(v_a_886_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(lean_object* v_waitForILeansId_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_Lsp_Ipc_readMessage(v___y_896_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_921_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_921_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_921_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_921_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
switch(lean_obj_tag(v_a_899_))
{
case 2:
{
lean_object* v_id_903_; uint8_t v___x_904_; 
v_id_903_ = lean_ctor_get(v_a_899_, 0);
lean_inc(v_id_903_);
lean_dec_ref_known(v_a_899_, 2);
v___x_904_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_903_, v_waitForILeansId_895_);
lean_dec(v_id_903_);
if (v___x_904_ == 0)
{
lean_del_object(v___x_901_);
goto _start;
}
else
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1));
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_906_);
v___x_908_ = v___x_901_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
case 3:
{
lean_object* v_id_910_; lean_object* v_message_911_; uint8_t v___x_912_; 
v_id_910_ = lean_ctor_get(v_a_899_, 0);
lean_inc(v_id_910_);
v_message_911_ = lean_ctor_get(v_a_899_, 1);
lean_inc_ref(v_message_911_);
lean_dec_ref_known(v_a_899_, 3);
v___x_912_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_910_, v_waitForILeansId_895_);
lean_dec(v_id_910_);
if (v___x_912_ == 0)
{
lean_dec_ref(v_message_911_);
lean_del_object(v___x_901_);
goto _start;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_914_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2));
v___x_915_ = lean_string_append(v___x_914_, v_message_911_);
lean_dec_ref(v_message_911_);
v___x_916_ = lean_mk_io_user_error(v___x_915_);
if (v_isShared_902_ == 0)
{
lean_ctor_set_tag(v___x_901_, 1);
lean_ctor_set(v___x_901_, 0, v___x_916_);
v___x_918_ = v___x_901_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
default: 
{
lean_del_object(v___x_901_);
lean_dec(v_a_899_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
v_a_922_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_898_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_898_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___boxed(lean_object* v_waitForILeansId_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_930_, v___y_931_);
lean_dec_ref(v___y_931_);
lean_dec(v_waitForILeansId_930_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object* v_waitForILeansId_935_, lean_object* v_target_936_, lean_object* v_version_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_940_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v_target_936_);
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v_version_937_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
lean_inc(v_waitForILeansId_935_);
v___x_944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_944_, 0, v_waitForILeansId_935_);
lean_ctor_set(v___x_944_, 1, v___x_940_);
lean_ctor_set(v___x_944_, 2, v___x_943_);
v___x_945_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_944_, v_a_938_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec_ref_known(v___x_945_, 1);
v___x_946_ = lean_box(0);
v___x_947_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_935_, v_a_938_);
lean_dec(v_waitForILeansId_935_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_960_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_960_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_960_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_960_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_fst_952_; 
v_fst_952_ = lean_ctor_get(v_a_948_, 0);
lean_inc(v_fst_952_);
lean_dec(v_a_948_);
if (lean_obj_tag(v_fst_952_) == 0)
{
lean_object* v___x_954_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_946_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_946_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
else
{
lean_object* v_val_956_; lean_object* v___x_958_; 
v_val_956_ = lean_ctor_get(v_fst_952_, 0);
lean_inc(v_val_956_);
lean_dec_ref_known(v_fst_952_, 1);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v_val_956_);
v___x_958_ = v___x_950_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_val_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_a_961_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_947_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_947_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_dec(v_waitForILeansId_935_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans___boxed(lean_object* v_waitForILeansId_969_, lean_object* v_target_970_, lean_object* v_version_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Lsp_Ipc_waitForILeans(v_waitForILeansId_969_, v_target_970_, v_version_971_, v_a_972_);
lean_dec_ref(v_a_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(lean_object* v_waitForILeansId_975_, lean_object* v_inst_976_, lean_object* v_a_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_975_, v___y_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___boxed(lean_object* v_waitForILeansId_981_, lean_object* v_inst_982_, lean_object* v_a_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(v_waitForILeansId_981_, v_inst_982_, v_a_983_, v___y_984_);
lean_dec_ref(v___y_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_waitForILeansId_981_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans(lean_object* v_waitForILeansId_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_992_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_993_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0));
lean_inc(v_waitForILeansId_989_);
v___x_994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_994_, 0, v_waitForILeansId_989_);
lean_ctor_set(v___x_994_, 1, v___x_992_);
lean_ctor_set(v___x_994_, 2, v___x_993_);
v___x_995_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_994_, v_a_990_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec_ref_known(v___x_995_, 1);
v___x_996_ = lean_box(0);
v___x_997_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_989_, v_a_990_);
lean_dec(v_waitForILeansId_989_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1010_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1010_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1010_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v_fst_1002_; 
v_fst_1002_ = lean_ctor_get(v_a_998_, 0);
lean_inc(v_fst_1002_);
lean_dec(v_a_998_);
if (lean_obj_tag(v_fst_1002_) == 0)
{
lean_object* v___x_1004_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_996_);
v___x_1004_ = v___x_1000_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_996_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1008_; 
v_val_1006_ = lean_ctor_get(v_fst_1002_, 0);
lean_inc(v_val_1006_);
lean_dec_ref_known(v_fst_1002_, 1);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v_val_1006_);
v___x_1008_ = v___x_1000_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_val_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_997_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_997_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
else
{
lean_dec(v_waitForILeansId_989_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___boxed(lean_object* v_waitForILeansId_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Lsp_Ipc_waitForWatchdogILeans(v_waitForILeansId_1019_, v_a_1020_);
lean_dec_ref(v_a_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(lean_object* v_j_1023_, lean_object* v_k_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = l_Lean_Json_getObjValD(v_j_1023_, v_k_1024_);
v___x_1026_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0___boxed(lean_object* v_j_1027_, lean_object* v_k_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_j_1027_, v_k_1028_);
lean_dec_ref(v_k_1028_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_1030_, size_t v_i_1031_, lean_object* v_bs_1032_){
_start:
{
uint8_t v___x_1033_; 
v___x_1033_ = lean_usize_dec_lt(v_i_1031_, v_sz_1030_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v_bs_1032_);
return v___x_1034_;
}
else
{
lean_object* v_v_1035_; lean_object* v___x_1036_; 
v_v_1035_ = lean_array_uget_borrowed(v_bs_1032_, v_i_1031_);
lean_inc(v_v_1035_);
v___x_1036_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_v_1035_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_bs_1032_);
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1046_; lean_object* v_bs_x27_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
v_a_1045_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1046_ = lean_unsigned_to_nat(0u);
v_bs_x27_1047_ = lean_array_uset(v_bs_1032_, v_i_1031_, v___x_1046_);
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_add(v_i_1031_, v___x_1048_);
v___x_1050_ = lean_array_uset(v_bs_x27_1047_, v_i_1031_, v_a_1045_);
v_i_1031_ = v___x_1049_;
v_bs_1032_ = v___x_1050_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1052_, lean_object* v_i_1053_, lean_object* v_bs_1054_){
_start:
{
size_t v_sz_boxed_1055_; size_t v_i_boxed_1056_; lean_object* v_res_1057_; 
v_sz_boxed_1055_ = lean_unbox_usize(v_sz_1052_);
lean_dec(v_sz_1052_);
v_i_boxed_1056_ = lean_unbox_usize(v_i_1053_);
lean_dec(v_i_1053_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_1055_, v_i_boxed_1056_, v_bs_1054_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_1059_){
_start:
{
if (lean_obj_tag(v_x_1059_) == 4)
{
lean_object* v_elems_1060_; size_t v_sz_1061_; size_t v___x_1062_; lean_object* v___x_1063_; 
v_elems_1060_ = lean_ctor_get(v_x_1059_, 0);
lean_inc_ref(v_elems_1060_);
lean_dec_ref_known(v_x_1059_, 1);
v_sz_1061_ = lean_array_size(v_elems_1060_);
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_1061_, v___x_1062_, v_elems_1060_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1064_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1065_ = lean_unsigned_to_nat(80u);
v___x_1066_ = l_Lean_Json_pretty(v_x_1059_, v___x_1065_);
v___x_1067_ = lean_string_append(v___x_1064_, v___x_1066_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1069_ = lean_string_append(v___x_1067_, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(lean_object* v_j_1071_, lean_object* v_k_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = l_Lean_Json_getObjValD(v_j_1071_, v_k_1072_);
v___x_1074_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1___boxed(lean_object* v_j_1075_, lean_object* v_k_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_j_1075_, v_k_1076_);
lean_dec_ref(v_k_1076_);
return v_res_1077_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = 1;
v___x_1083_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9));
v___x_1084_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1083_, v___x_1082_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = 1;
v___x_1096_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5));
v___x_1097_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1096_, v___x_1095_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_1099_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6);
v___x_1100_ = lean_string_append(v___x_1099_, v___x_1098_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_1102_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1103_ = lean_string_append(v___x_1102_, v___x_1101_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1105_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11);
v___x_1106_ = lean_string_append(v___x_1105_, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = 1;
v___x_1111_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15));
v___x_1112_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1111_, v___x_1110_);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16);
v___x_1114_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1115_ = lean_string_append(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1117_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17);
v___x_1118_ = lean_string_append(v___x_1117_, v___x_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1122_ = 1;
v___x_1123_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20));
v___x_1124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1123_, v___x_1122_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_1126_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1127_ = lean_string_append(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1129_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22);
v___x_1130_ = lean_string_append(v___x_1129_, v___x_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(lean_object* v_json_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_1131_);
v___x_1133_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_json_1131_, v___x_1132_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_json_1131_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1143_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1143_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1138_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13);
v___x_1139_ = lean_string_append(v___x_1138_, v_a_1134_);
lean_dec(v_a_1134_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1139_);
v___x_1141_ = v___x_1136_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_a_1144_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1145_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
lean_inc(v_json_1131_);
v___x_1146_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_json_1131_, v___x_1145_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v_a_1144_);
lean_dec(v_json_1131_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1156_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1156_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1151_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18);
v___x_1152_ = lean_string_append(v___x_1151_, v_a_1147_);
lean_dec(v_a_1147_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1152_);
v___x_1154_ = v___x_1149_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_a_1157_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1158_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1159_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_json_1131_, v___x_1158_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_a_1157_);
lean_dec(v_a_1144_);
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1169_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1169_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1164_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23);
v___x_1165_ = lean_string_append(v___x_1164_, v_a_1160_);
lean_dec(v_a_1160_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1165_);
v___x_1167_ = v___x_1162_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1178_; 
v_a_1170_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1172_ = v___x_1159_;
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1159_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1174_, 0, v_a_1144_);
lean_ctor_set(v___x_1174_, 1, v_a_1157_);
lean_ctor_set(v___x_1174_, 2, v_a_1170_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1174_);
v___x_1176_ = v___x_1172_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(size_t v_sz_1179_, size_t v_i_1180_, lean_object* v_bs_1181_){
_start:
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_usize_dec_lt(v_i_1180_, v_sz_1179_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_bs_1181_);
return v___x_1183_;
}
else
{
lean_object* v_v_1184_; lean_object* v___x_1185_; 
v_v_1184_ = lean_array_uget_borrowed(v_bs_1181_, v_i_1180_);
lean_inc(v_v_1184_);
v___x_1185_ = l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(v_v_1184_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v_bs_1181_);
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1195_; lean_object* v_bs_x27_1196_; size_t v___x_1197_; size_t v___x_1198_; lean_object* v___x_1199_; 
v_a_1194_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1195_ = lean_unsigned_to_nat(0u);
v_bs_x27_1196_ = lean_array_uset(v_bs_1181_, v_i_1180_, v___x_1195_);
v___x_1197_ = ((size_t)1ULL);
v___x_1198_ = lean_usize_add(v_i_1180_, v___x_1197_);
v___x_1199_ = lean_array_uset(v_bs_x27_1196_, v_i_1180_, v_a_1194_);
v_i_1180_ = v___x_1198_;
v_bs_1181_ = v___x_1199_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(lean_object* v_x_1201_){
_start:
{
if (lean_obj_tag(v_x_1201_) == 4)
{
lean_object* v_elems_1202_; size_t v_sz_1203_; size_t v___x_1204_; lean_object* v___x_1205_; 
v_elems_1202_ = lean_ctor_get(v_x_1201_, 0);
lean_inc_ref(v_elems_1202_);
lean_dec_ref_known(v_x_1201_, 1);
v_sz_1203_ = lean_array_size(v_elems_1202_);
v___x_1204_ = ((size_t)0ULL);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_1203_, v___x_1204_, v_elems_1202_);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1206_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1207_ = lean_unsigned_to_nat(80u);
v___x_1208_ = l_Lean_Json_pretty(v_x_1201_, v___x_1207_);
v___x_1209_ = lean_string_append(v___x_1206_, v___x_1208_);
lean_dec_ref(v___x_1208_);
v___x_1210_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1211_ = lean_string_append(v___x_1209_, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(lean_object* v_j_1213_, lean_object* v_k_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = l_Lean_Json_getObjValD(v_j_1213_, v_k_1214_);
v___x_1216_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2___boxed(lean_object* v_j_1217_, lean_object* v_k_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_j_1217_, v_k_1218_);
lean_dec_ref(v_k_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1220_, lean_object* v_i_1221_, lean_object* v_bs_1222_){
_start:
{
size_t v_sz_boxed_1223_; size_t v_i_boxed_1224_; lean_object* v_res_1225_; 
v_sz_boxed_1223_ = lean_unbox_usize(v_sz_1220_);
lean_dec(v_sz_1220_);
v_i_boxed_1224_ = lean_unbox_usize(v_i_1221_);
lean_dec(v_i_1221_);
v_res_1225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_boxed_1223_, v_i_boxed_1224_, v_bs_1222_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
if (lean_obj_tag(v_a_1228_) == 0)
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_array_to_list(v_a_1229_);
return v___x_1230_;
}
else
{
lean_object* v_head_1231_; lean_object* v_tail_1232_; lean_object* v___x_1233_; 
v_head_1231_ = lean_ctor_get(v_a_1228_, 0);
lean_inc(v_head_1231_);
v_tail_1232_ = lean_ctor_get(v_a_1228_, 1);
lean_inc(v_tail_1232_);
lean_dec_ref_known(v_a_1228_, 2);
v___x_1233_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1229_, v_head_1231_);
v_a_1228_ = v_tail_1232_;
v_a_1229_ = v___x_1233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(size_t v_sz_1235_, size_t v_i_1236_, lean_object* v_bs_1237_){
_start:
{
uint8_t v___x_1238_; 
v___x_1238_ = lean_usize_dec_lt(v_i_1236_, v_sz_1235_);
if (v___x_1238_ == 0)
{
return v_bs_1237_;
}
else
{
lean_object* v_v_1239_; lean_object* v___x_1240_; lean_object* v_bs_x27_1241_; lean_object* v___x_1242_; size_t v___x_1243_; size_t v___x_1244_; lean_object* v___x_1245_; 
v_v_1239_ = lean_array_uget(v_bs_1237_, v_i_1236_);
v___x_1240_ = lean_unsigned_to_nat(0u);
v_bs_x27_1241_ = lean_array_uset(v_bs_1237_, v_i_1236_, v___x_1240_);
v___x_1242_ = l_Lean_Lsp_instToJsonRange_toJson(v_v_1239_);
v___x_1243_ = ((size_t)1ULL);
v___x_1244_ = lean_usize_add(v_i_1236_, v___x_1243_);
v___x_1245_ = lean_array_uset(v_bs_x27_1241_, v_i_1236_, v___x_1242_);
v_i_1236_ = v___x_1244_;
v_bs_1237_ = v___x_1245_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1247_, lean_object* v_i_1248_, lean_object* v_bs_1249_){
_start:
{
size_t v_sz_boxed_1250_; size_t v_i_boxed_1251_; lean_object* v_res_1252_; 
v_sz_boxed_1250_ = lean_unbox_usize(v_sz_1247_);
lean_dec(v_sz_1247_);
v_i_boxed_1251_ = lean_unbox_usize(v_i_1248_);
lean_dec(v_i_1248_);
v_res_1252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_boxed_1250_, v_i_boxed_1251_, v_bs_1249_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(lean_object* v_a_1253_){
_start:
{
size_t v_sz_1254_; size_t v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_sz_1254_ = lean_array_size(v_a_1253_);
v___x_1255_ = ((size_t)0ULL);
v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_1254_, v___x_1255_, v_a_1253_);
v___x_1257_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(lean_object* v_x_1260_){
_start:
{
lean_object* v_item_1261_; lean_object* v_fromRanges_1262_; lean_object* v_children_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_item_1261_ = lean_ctor_get(v_x_1260_, 0);
lean_inc_ref(v_item_1261_);
v_fromRanges_1262_ = lean_ctor_get(v_x_1260_, 1);
lean_inc_ref(v_fromRanges_1262_);
v_children_1263_ = lean_ctor_get(v_x_1260_, 2);
lean_inc_ref(v_children_1263_);
lean_dec_ref(v_x_1260_);
v___x_1264_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_1265_ = l_Lean_Lsp_instToJsonCallHierarchyItem_toJson(v_item_1261_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
v___x_1270_ = l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(v_fromRanges_1262_);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v___x_1267_);
v___x_1273_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1274_ = l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(v_children_1263_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v___x_1267_);
v___x_1277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v___x_1267_);
v___x_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1272_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1268_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_1281_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_1279_, v___x_1280_);
v___x_1282_ = l_Lean_Json_mkObj(v___x_1281_);
lean_dec(v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(size_t v_sz_1283_, size_t v_i_1284_, lean_object* v_bs_1285_){
_start:
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_usize_dec_lt(v_i_1284_, v_sz_1283_);
if (v___x_1286_ == 0)
{
return v_bs_1285_;
}
else
{
lean_object* v_v_1287_; lean_object* v___x_1288_; lean_object* v_bs_x27_1289_; lean_object* v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
v_v_1287_ = lean_array_uget(v_bs_1285_, v_i_1284_);
v___x_1288_ = lean_unsigned_to_nat(0u);
v_bs_x27_1289_ = lean_array_uset(v_bs_1285_, v_i_1284_, v___x_1288_);
v___x_1290_ = l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(v_v_1287_);
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = lean_usize_add(v_i_1284_, v___x_1291_);
v___x_1293_ = lean_array_uset(v_bs_x27_1289_, v_i_1284_, v___x_1290_);
v_i_1284_ = v___x_1292_;
v_bs_1285_ = v___x_1293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(lean_object* v_a_1295_){
_start:
{
size_t v_sz_1296_; size_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_sz_1296_ = lean_array_size(v_a_1295_);
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_1296_, v___x_1297_, v_a_1295_);
v___x_1299_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2___boxed(lean_object* v_sz_1300_, lean_object* v_i_1301_, lean_object* v_bs_1302_){
_start:
{
size_t v_sz_boxed_1303_; size_t v_i_boxed_1304_; lean_object* v_res_1305_; 
v_sz_boxed_1303_ = lean_unbox_usize(v_sz_1300_);
lean_dec(v_sz_1300_);
v_i_boxed_1304_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_res_1305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_boxed_1303_, v_i_boxed_1304_, v_bs_1302_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(lean_object* v_k_1308_, lean_object* v_v_1309_, lean_object* v_t_1310_){
_start:
{
if (lean_obj_tag(v_t_1310_) == 0)
{
lean_object* v_size_1311_; lean_object* v_k_1312_; lean_object* v_v_1313_; lean_object* v_l_1314_; lean_object* v_r_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1595_; 
v_size_1311_ = lean_ctor_get(v_t_1310_, 0);
v_k_1312_ = lean_ctor_get(v_t_1310_, 1);
v_v_1313_ = lean_ctor_get(v_t_1310_, 2);
v_l_1314_ = lean_ctor_get(v_t_1310_, 3);
v_r_1315_ = lean_ctor_get(v_t_1310_, 4);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_t_1310_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1317_ = v_t_1310_;
v_isShared_1318_ = v_isSharedCheck_1595_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_r_1315_);
lean_inc(v_l_1314_);
lean_inc(v_v_1313_);
lean_inc(v_k_1312_);
lean_inc(v_size_1311_);
lean_dec(v_t_1310_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1595_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_string_compare(v_k_1308_, v_k_1312_);
switch(v___x_1319_)
{
case 0:
{
lean_object* v_impl_1320_; lean_object* v___x_1321_; 
lean_dec(v_size_1311_);
v_impl_1320_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1308_, v_v_1309_, v_l_1314_);
v___x_1321_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1315_) == 0)
{
lean_object* v_size_1322_; lean_object* v_size_1323_; lean_object* v_k_1324_; lean_object* v_v_1325_; lean_object* v_l_1326_; lean_object* v_r_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_size_1322_ = lean_ctor_get(v_r_1315_, 0);
v_size_1323_ = lean_ctor_get(v_impl_1320_, 0);
v_k_1324_ = lean_ctor_get(v_impl_1320_, 1);
v_v_1325_ = lean_ctor_get(v_impl_1320_, 2);
v_l_1326_ = lean_ctor_get(v_impl_1320_, 3);
v_r_1327_ = lean_ctor_get(v_impl_1320_, 4);
lean_inc(v_r_1327_);
v___x_1328_ = lean_unsigned_to_nat(3u);
v___x_1329_ = lean_nat_mul(v___x_1328_, v_size_1322_);
v___x_1330_ = lean_nat_dec_lt(v___x_1329_, v_size_1323_);
lean_dec(v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
lean_dec(v_r_1327_);
v___x_1331_ = lean_nat_add(v___x_1321_, v_size_1323_);
v___x_1332_ = lean_nat_add(v___x_1331_, v_size_1322_);
lean_dec(v___x_1331_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 3, v_impl_1320_);
lean_ctor_set(v___x_1317_, 0, v___x_1332_);
v___x_1334_ = v___x_1317_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v_impl_1320_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v_r_1315_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1401_; 
lean_inc(v_l_1326_);
lean_inc(v_v_1325_);
lean_inc(v_k_1324_);
lean_inc(v_size_1323_);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_impl_1320_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; lean_object* v_unused_1403_; lean_object* v_unused_1404_; lean_object* v_unused_1405_; lean_object* v_unused_1406_; 
v_unused_1402_ = lean_ctor_get(v_impl_1320_, 4);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_impl_1320_, 3);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_impl_1320_, 2);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_impl_1320_, 1);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_impl_1320_, 0);
lean_dec(v_unused_1406_);
v___x_1337_ = v_impl_1320_;
v_isShared_1338_ = v_isSharedCheck_1401_;
goto v_resetjp_1336_;
}
else
{
lean_dec(v_impl_1320_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1401_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_size_1339_; lean_object* v_size_1340_; lean_object* v_k_1341_; lean_object* v_v_1342_; lean_object* v_l_1343_; lean_object* v_r_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v_size_1339_ = lean_ctor_get(v_l_1326_, 0);
v_size_1340_ = lean_ctor_get(v_r_1327_, 0);
v_k_1341_ = lean_ctor_get(v_r_1327_, 1);
v_v_1342_ = lean_ctor_get(v_r_1327_, 2);
v_l_1343_ = lean_ctor_get(v_r_1327_, 3);
v_r_1344_ = lean_ctor_get(v_r_1327_, 4);
v___x_1345_ = lean_unsigned_to_nat(2u);
v___x_1346_ = lean_nat_mul(v___x_1345_, v_size_1339_);
v___x_1347_ = lean_nat_dec_lt(v_size_1340_, v___x_1346_);
lean_dec(v___x_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1376_; 
lean_inc(v_r_1344_);
lean_inc(v_l_1343_);
lean_inc(v_v_1342_);
lean_inc(v_k_1341_);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_r_1327_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; lean_object* v_unused_1378_; lean_object* v_unused_1379_; lean_object* v_unused_1380_; lean_object* v_unused_1381_; 
v_unused_1377_ = lean_ctor_get(v_r_1327_, 4);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_r_1327_, 3);
lean_dec(v_unused_1378_);
v_unused_1379_ = lean_ctor_get(v_r_1327_, 2);
lean_dec(v_unused_1379_);
v_unused_1380_ = lean_ctor_get(v_r_1327_, 1);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v_r_1327_, 0);
lean_dec(v_unused_1381_);
v___x_1349_ = v_r_1327_;
v_isShared_1350_ = v_isSharedCheck_1376_;
goto v_resetjp_1348_;
}
else
{
lean_dec(v_r_1327_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1376_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___x_1364_; lean_object* v___y_1366_; 
v___x_1351_ = lean_nat_add(v___x_1321_, v_size_1323_);
lean_dec(v_size_1323_);
v___x_1352_ = lean_nat_add(v___x_1351_, v_size_1322_);
lean_dec(v___x_1351_);
v___x_1364_ = lean_nat_add(v___x_1321_, v_size_1339_);
if (lean_obj_tag(v_l_1343_) == 0)
{
lean_object* v_size_1374_; 
v_size_1374_ = lean_ctor_get(v_l_1343_, 0);
lean_inc(v_size_1374_);
v___y_1366_ = v_size_1374_;
goto v___jp_1365_;
}
else
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_unsigned_to_nat(0u);
v___y_1366_ = v___x_1375_;
goto v___jp_1365_;
}
v___jp_1353_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_nat_add(v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec(v___y_1355_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 4, v_r_1315_);
lean_ctor_set(v___x_1349_, 3, v_r_1344_);
lean_ctor_set(v___x_1349_, 2, v_v_1313_);
lean_ctor_set(v___x_1349_, 1, v_k_1312_);
lean_ctor_set(v___x_1349_, 0, v___x_1357_);
v___x_1359_ = v___x_1349_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_r_1344_);
lean_ctor_set(v_reuseFailAlloc_1363_, 4, v_r_1315_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1361_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 4, v___x_1359_);
lean_ctor_set(v___x_1337_, 3, v___y_1354_);
lean_ctor_set(v___x_1337_, 2, v_v_1342_);
lean_ctor_set(v___x_1337_, 1, v_k_1341_);
lean_ctor_set(v___x_1337_, 0, v___x_1352_);
v___x_1361_ = v___x_1337_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_k_1341_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_v_1342_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v___y_1354_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
v___jp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1367_ = lean_nat_add(v___x_1364_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec(v___x_1364_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v_l_1343_);
lean_ctor_set(v___x_1317_, 3, v_l_1326_);
lean_ctor_set(v___x_1317_, 2, v_v_1325_);
lean_ctor_set(v___x_1317_, 1, v_k_1324_);
lean_ctor_set(v___x_1317_, 0, v___x_1367_);
v___x_1369_ = v___x_1317_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1324_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1325_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_l_1326_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_l_1343_);
v___x_1369_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_nat_add(v___x_1321_, v_size_1322_);
if (lean_obj_tag(v_r_1344_) == 0)
{
lean_object* v_size_1371_; 
v_size_1371_ = lean_ctor_get(v_r_1344_, 0);
lean_inc(v_size_1371_);
v___y_1354_ = v___x_1369_;
v___y_1355_ = v___x_1370_;
v___y_1356_ = v_size_1371_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_unsigned_to_nat(0u);
v___y_1354_ = v___x_1369_;
v___y_1355_ = v___x_1370_;
v___y_1356_ = v___x_1372_;
goto v___jp_1353_;
}
}
}
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_del_object(v___x_1317_);
v___x_1382_ = lean_nat_add(v___x_1321_, v_size_1323_);
lean_dec(v_size_1323_);
v___x_1383_ = lean_nat_add(v___x_1382_, v_size_1322_);
lean_dec(v___x_1382_);
v___x_1384_ = lean_nat_add(v___x_1321_, v_size_1322_);
v___x_1385_ = lean_nat_add(v___x_1384_, v_size_1340_);
lean_dec(v___x_1384_);
lean_inc_ref(v_r_1315_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 4, v_r_1315_);
lean_ctor_set(v___x_1337_, 3, v_r_1327_);
lean_ctor_set(v___x_1337_, 2, v_v_1313_);
lean_ctor_set(v___x_1337_, 1, v_k_1312_);
lean_ctor_set(v___x_1337_, 0, v___x_1385_);
v___x_1387_ = v___x_1337_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_r_1327_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_r_1315_);
v___x_1387_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_isSharedCheck_1394_ = !lean_is_exclusive(v_r_1315_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; lean_object* v_unused_1396_; lean_object* v_unused_1397_; lean_object* v_unused_1398_; lean_object* v_unused_1399_; 
v_unused_1395_ = lean_ctor_get(v_r_1315_, 4);
lean_dec(v_unused_1395_);
v_unused_1396_ = lean_ctor_get(v_r_1315_, 3);
lean_dec(v_unused_1396_);
v_unused_1397_ = lean_ctor_get(v_r_1315_, 2);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_r_1315_, 1);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_r_1315_, 0);
lean_dec(v_unused_1399_);
v___x_1389_ = v_r_1315_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_dec(v_r_1315_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 4, v___x_1387_);
lean_ctor_set(v___x_1389_, 3, v_l_1326_);
lean_ctor_set(v___x_1389_, 2, v_v_1325_);
lean_ctor_set(v___x_1389_, 1, v_k_1324_);
lean_ctor_set(v___x_1389_, 0, v___x_1383_);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_k_1324_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_v_1325_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_l_1326_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v___x_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1407_; 
v_l_1407_ = lean_ctor_get(v_impl_1320_, 3);
if (lean_obj_tag(v_l_1407_) == 0)
{
lean_object* v_r_1408_; lean_object* v_k_1409_; lean_object* v_v_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1421_; 
lean_inc_ref(v_l_1407_);
v_r_1408_ = lean_ctor_get(v_impl_1320_, 4);
v_k_1409_ = lean_ctor_get(v_impl_1320_, 1);
v_v_1410_ = lean_ctor_get(v_impl_1320_, 2);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_impl_1320_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; lean_object* v_unused_1423_; 
v_unused_1422_ = lean_ctor_get(v_impl_1320_, 3);
lean_dec(v_unused_1422_);
v_unused_1423_ = lean_ctor_get(v_impl_1320_, 0);
lean_dec(v_unused_1423_);
v___x_1412_ = v_impl_1320_;
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_r_1408_);
lean_inc(v_v_1410_);
lean_inc(v_k_1409_);
lean_dec(v_impl_1320_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1421_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1408_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 3, v_r_1408_);
lean_ctor_set(v___x_1412_, 2, v_v_1313_);
lean_ctor_set(v___x_1412_, 1, v_k_1312_);
lean_ctor_set(v___x_1412_, 0, v___x_1321_);
v___x_1416_ = v___x_1412_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_r_1408_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_r_1408_);
v___x_1416_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v___x_1416_);
lean_ctor_set(v___x_1317_, 3, v_l_1407_);
lean_ctor_set(v___x_1317_, 2, v_v_1410_);
lean_ctor_set(v___x_1317_, 1, v_k_1409_);
lean_ctor_set(v___x_1317_, 0, v___x_1414_);
v___x_1418_ = v___x_1317_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_k_1409_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_v_1410_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_l_1407_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v_r_1424_; 
v_r_1424_ = lean_ctor_get(v_impl_1320_, 4);
lean_inc(v_r_1424_);
if (lean_obj_tag(v_r_1424_) == 0)
{
lean_object* v_k_1425_; lean_object* v_v_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1449_; 
lean_inc(v_l_1407_);
v_k_1425_ = lean_ctor_get(v_impl_1320_, 1);
v_v_1426_ = lean_ctor_get(v_impl_1320_, 2);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_impl_1320_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1450_ = lean_ctor_get(v_impl_1320_, 4);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_impl_1320_, 3);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_impl_1320_, 0);
lean_dec(v_unused_1452_);
v___x_1428_ = v_impl_1320_;
v_isShared_1429_ = v_isSharedCheck_1449_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_v_1426_);
lean_inc(v_k_1425_);
lean_dec(v_impl_1320_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1449_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v_k_1430_; lean_object* v_v_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1445_; 
v_k_1430_ = lean_ctor_get(v_r_1424_, 1);
v_v_1431_ = lean_ctor_get(v_r_1424_, 2);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_r_1424_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; lean_object* v_unused_1447_; lean_object* v_unused_1448_; 
v_unused_1446_ = lean_ctor_get(v_r_1424_, 4);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_r_1424_, 3);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_r_1424_, 0);
lean_dec(v_unused_1448_);
v___x_1433_ = v_r_1424_;
v_isShared_1434_ = v_isSharedCheck_1445_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_v_1431_);
lean_inc(v_k_1430_);
lean_dec(v_r_1424_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1445_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = lean_unsigned_to_nat(3u);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 4, v_l_1407_);
lean_ctor_set(v___x_1433_, 3, v_l_1407_);
lean_ctor_set(v___x_1433_, 2, v_v_1426_);
lean_ctor_set(v___x_1433_, 1, v_k_1425_);
lean_ctor_set(v___x_1433_, 0, v___x_1321_);
v___x_1437_ = v___x_1433_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1425_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1426_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_l_1407_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_l_1407_);
v___x_1437_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1439_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 4, v_l_1407_);
lean_ctor_set(v___x_1428_, 2, v_v_1313_);
lean_ctor_set(v___x_1428_, 1, v_k_1312_);
lean_ctor_set(v___x_1428_, 0, v___x_1321_);
v___x_1439_ = v___x_1428_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_l_1407_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_l_1407_);
v___x_1439_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1441_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v___x_1439_);
lean_ctor_set(v___x_1317_, 3, v___x_1437_);
lean_ctor_set(v___x_1317_, 2, v_v_1431_);
lean_ctor_set(v___x_1317_, 1, v_k_1430_);
lean_ctor_set(v___x_1317_, 0, v___x_1435_);
v___x_1441_ = v___x_1317_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_k_1430_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_v_1431_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1442_, 4, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = lean_unsigned_to_nat(2u);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v_r_1424_);
lean_ctor_set(v___x_1317_, 3, v_impl_1320_);
lean_ctor_set(v___x_1317_, 0, v___x_1453_);
v___x_1455_ = v___x_1317_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v_impl_1320_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v_r_1424_);
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
case 1:
{
lean_object* v___x_1458_; 
lean_dec(v_v_1313_);
lean_dec(v_k_1312_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 2, v_v_1309_);
lean_ctor_set(v___x_1317_, 1, v_k_1308_);
v___x_1458_ = v___x_1317_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_size_1311_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_k_1308_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_v_1309_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_l_1314_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v_r_1315_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
default: 
{
lean_object* v_impl_1460_; lean_object* v___x_1461_; 
lean_dec(v_size_1311_);
v_impl_1460_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1308_, v_v_1309_, v_r_1315_);
v___x_1461_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1314_) == 0)
{
lean_object* v_size_1462_; lean_object* v_size_1463_; lean_object* v_k_1464_; lean_object* v_v_1465_; lean_object* v_l_1466_; lean_object* v_r_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v_size_1462_ = lean_ctor_get(v_l_1314_, 0);
v_size_1463_ = lean_ctor_get(v_impl_1460_, 0);
v_k_1464_ = lean_ctor_get(v_impl_1460_, 1);
v_v_1465_ = lean_ctor_get(v_impl_1460_, 2);
v_l_1466_ = lean_ctor_get(v_impl_1460_, 3);
lean_inc(v_l_1466_);
v_r_1467_ = lean_ctor_get(v_impl_1460_, 4);
v___x_1468_ = lean_unsigned_to_nat(3u);
v___x_1469_ = lean_nat_mul(v___x_1468_, v_size_1462_);
v___x_1470_ = lean_nat_dec_lt(v___x_1469_, v_size_1463_);
lean_dec(v___x_1469_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_dec(v_l_1466_);
v___x_1471_ = lean_nat_add(v___x_1461_, v_size_1462_);
v___x_1472_ = lean_nat_add(v___x_1471_, v_size_1463_);
lean_dec(v___x_1471_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v_impl_1460_);
lean_ctor_set(v___x_1317_, 0, v___x_1472_);
v___x_1474_ = v___x_1317_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_l_1314_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_impl_1460_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
else
{
lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1539_; 
lean_inc(v_r_1467_);
lean_inc(v_v_1465_);
lean_inc(v_k_1464_);
lean_inc(v_size_1463_);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_impl_1460_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; lean_object* v_unused_1541_; lean_object* v_unused_1542_; lean_object* v_unused_1543_; lean_object* v_unused_1544_; 
v_unused_1540_ = lean_ctor_get(v_impl_1460_, 4);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v_impl_1460_, 3);
lean_dec(v_unused_1541_);
v_unused_1542_ = lean_ctor_get(v_impl_1460_, 2);
lean_dec(v_unused_1542_);
v_unused_1543_ = lean_ctor_get(v_impl_1460_, 1);
lean_dec(v_unused_1543_);
v_unused_1544_ = lean_ctor_get(v_impl_1460_, 0);
lean_dec(v_unused_1544_);
v___x_1477_ = v_impl_1460_;
v_isShared_1478_ = v_isSharedCheck_1539_;
goto v_resetjp_1476_;
}
else
{
lean_dec(v_impl_1460_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1539_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_size_1479_; lean_object* v_k_1480_; lean_object* v_v_1481_; lean_object* v_l_1482_; lean_object* v_r_1483_; lean_object* v_size_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v_size_1479_ = lean_ctor_get(v_l_1466_, 0);
v_k_1480_ = lean_ctor_get(v_l_1466_, 1);
v_v_1481_ = lean_ctor_get(v_l_1466_, 2);
v_l_1482_ = lean_ctor_get(v_l_1466_, 3);
v_r_1483_ = lean_ctor_get(v_l_1466_, 4);
v_size_1484_ = lean_ctor_get(v_r_1467_, 0);
v___x_1485_ = lean_unsigned_to_nat(2u);
v___x_1486_ = lean_nat_mul(v___x_1485_, v_size_1484_);
v___x_1487_ = lean_nat_dec_lt(v_size_1479_, v___x_1486_);
lean_dec(v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1515_; 
lean_inc(v_r_1483_);
lean_inc(v_l_1482_);
lean_inc(v_v_1481_);
lean_inc(v_k_1480_);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_l_1466_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; lean_object* v_unused_1520_; 
v_unused_1516_ = lean_ctor_get(v_l_1466_, 4);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_l_1466_, 3);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_l_1466_, 2);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_l_1466_, 1);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_l_1466_, 0);
lean_dec(v_unused_1520_);
v___x_1489_ = v_l_1466_;
v_isShared_1490_ = v_isSharedCheck_1515_;
goto v_resetjp_1488_;
}
else
{
lean_dec(v_l_1466_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1515_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1505_; 
v___x_1491_ = lean_nat_add(v___x_1461_, v_size_1462_);
v___x_1492_ = lean_nat_add(v___x_1491_, v_size_1463_);
lean_dec(v_size_1463_);
if (lean_obj_tag(v_l_1482_) == 0)
{
lean_object* v_size_1513_; 
v_size_1513_ = lean_ctor_get(v_l_1482_, 0);
lean_inc(v_size_1513_);
v___y_1505_ = v_size_1513_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_unsigned_to_nat(0u);
v___y_1505_ = v___x_1514_;
goto v___jp_1504_;
}
v___jp_1493_:
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1497_ = lean_nat_add(v___y_1494_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec(v___y_1494_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 4, v_r_1467_);
lean_ctor_set(v___x_1489_, 3, v_r_1483_);
lean_ctor_set(v___x_1489_, 2, v_v_1465_);
lean_ctor_set(v___x_1489_, 1, v_k_1464_);
lean_ctor_set(v___x_1489_, 0, v___x_1497_);
v___x_1499_ = v___x_1489_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_k_1464_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_v_1465_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_r_1483_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v_r_1467_);
v___x_1499_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 4, v___x_1499_);
lean_ctor_set(v___x_1477_, 3, v___y_1495_);
lean_ctor_set(v___x_1477_, 2, v_v_1481_);
lean_ctor_set(v___x_1477_, 1, v_k_1480_);
lean_ctor_set(v___x_1477_, 0, v___x_1492_);
v___x_1501_ = v___x_1477_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1480_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1481_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v___y_1495_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
v___jp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = lean_nat_add(v___x_1491_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec(v___x_1491_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v_l_1482_);
lean_ctor_set(v___x_1317_, 0, v___x_1506_);
v___x_1508_ = v___x_1317_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v_l_1314_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v_l_1482_);
v___x_1508_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_nat_add(v___x_1461_, v_size_1484_);
if (lean_obj_tag(v_r_1483_) == 0)
{
lean_object* v_size_1510_; 
v_size_1510_ = lean_ctor_get(v_r_1483_, 0);
lean_inc(v_size_1510_);
v___y_1494_ = v___x_1509_;
v___y_1495_ = v___x_1508_;
v___y_1496_ = v_size_1510_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_unsigned_to_nat(0u);
v___y_1494_ = v___x_1509_;
v___y_1495_ = v___x_1508_;
v___y_1496_ = v___x_1511_;
goto v___jp_1493_;
}
}
}
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
lean_del_object(v___x_1317_);
v___x_1521_ = lean_nat_add(v___x_1461_, v_size_1462_);
v___x_1522_ = lean_nat_add(v___x_1521_, v_size_1463_);
lean_dec(v_size_1463_);
v___x_1523_ = lean_nat_add(v___x_1521_, v_size_1479_);
lean_dec(v___x_1521_);
lean_inc_ref(v_l_1314_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 4, v_l_1466_);
lean_ctor_set(v___x_1477_, 3, v_l_1314_);
lean_ctor_set(v___x_1477_, 2, v_v_1313_);
lean_ctor_set(v___x_1477_, 1, v_k_1312_);
lean_ctor_set(v___x_1477_, 0, v___x_1523_);
v___x_1525_ = v___x_1477_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_l_1314_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_l_1466_);
v___x_1525_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
v_isSharedCheck_1532_ = !lean_is_exclusive(v_l_1314_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; lean_object* v_unused_1537_; 
v_unused_1533_ = lean_ctor_get(v_l_1314_, 4);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_l_1314_, 3);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_l_1314_, 2);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_l_1314_, 1);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v_l_1314_, 0);
lean_dec(v_unused_1537_);
v___x_1527_ = v_l_1314_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_dec(v_l_1314_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 4, v_r_1467_);
lean_ctor_set(v___x_1527_, 3, v___x_1525_);
lean_ctor_set(v___x_1527_, 2, v_v_1465_);
lean_ctor_set(v___x_1527_, 1, v_k_1464_);
lean_ctor_set(v___x_1527_, 0, v___x_1522_);
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1464_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1465_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_r_1467_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1545_; 
v_l_1545_ = lean_ctor_get(v_impl_1460_, 3);
lean_inc(v_l_1545_);
if (lean_obj_tag(v_l_1545_) == 0)
{
lean_object* v_r_1546_; lean_object* v_k_1547_; lean_object* v_v_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1571_; 
v_r_1546_ = lean_ctor_get(v_impl_1460_, 4);
v_k_1547_ = lean_ctor_get(v_impl_1460_, 1);
v_v_1548_ = lean_ctor_get(v_impl_1460_, 2);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_impl_1460_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; lean_object* v_unused_1573_; 
v_unused_1572_ = lean_ctor_get(v_impl_1460_, 3);
lean_dec(v_unused_1572_);
v_unused_1573_ = lean_ctor_get(v_impl_1460_, 0);
lean_dec(v_unused_1573_);
v___x_1550_ = v_impl_1460_;
v_isShared_1551_ = v_isSharedCheck_1571_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_r_1546_);
lean_inc(v_v_1548_);
lean_inc(v_k_1547_);
lean_dec(v_impl_1460_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1571_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_k_1552_; lean_object* v_v_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1567_; 
v_k_1552_ = lean_ctor_get(v_l_1545_, 1);
v_v_1553_ = lean_ctor_get(v_l_1545_, 2);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_l_1545_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; lean_object* v_unused_1569_; lean_object* v_unused_1570_; 
v_unused_1568_ = lean_ctor_get(v_l_1545_, 4);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_l_1545_, 3);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_l_1545_, 0);
lean_dec(v_unused_1570_);
v___x_1555_ = v_l_1545_;
v_isShared_1556_ = v_isSharedCheck_1567_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_v_1553_);
lean_inc(v_k_1552_);
lean_dec(v_l_1545_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1567_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1546_, 2);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 4, v_r_1546_);
lean_ctor_set(v___x_1555_, 3, v_r_1546_);
lean_ctor_set(v___x_1555_, 2, v_v_1313_);
lean_ctor_set(v___x_1555_, 1, v_k_1312_);
lean_ctor_set(v___x_1555_, 0, v___x_1461_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v_r_1546_);
lean_ctor_set(v_reuseFailAlloc_1566_, 4, v_r_1546_);
v___x_1559_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1561_; 
lean_inc(v_r_1546_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 3, v_r_1546_);
lean_ctor_set(v___x_1550_, 0, v___x_1461_);
v___x_1561_ = v___x_1550_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_k_1547_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_v_1548_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_r_1546_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_r_1546_);
v___x_1561_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1563_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v___x_1561_);
lean_ctor_set(v___x_1317_, 3, v___x_1559_);
lean_ctor_set(v___x_1317_, 2, v_v_1553_);
lean_ctor_set(v___x_1317_, 1, v_k_1552_);
lean_ctor_set(v___x_1317_, 0, v___x_1557_);
v___x_1563_ = v___x_1317_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_k_1552_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_v_1553_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v___x_1561_);
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
}
}
else
{
lean_object* v_r_1574_; 
v_r_1574_ = lean_ctor_get(v_impl_1460_, 4);
lean_inc(v_r_1574_);
if (lean_obj_tag(v_r_1574_) == 0)
{
lean_object* v_k_1575_; lean_object* v_v_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1587_; 
v_k_1575_ = lean_ctor_get(v_impl_1460_, 1);
v_v_1576_ = lean_ctor_get(v_impl_1460_, 2);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_impl_1460_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; lean_object* v_unused_1589_; lean_object* v_unused_1590_; 
v_unused_1588_ = lean_ctor_get(v_impl_1460_, 4);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_impl_1460_, 3);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_impl_1460_, 0);
lean_dec(v_unused_1590_);
v___x_1578_ = v_impl_1460_;
v_isShared_1579_ = v_isSharedCheck_1587_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_v_1576_);
lean_inc(v_k_1575_);
lean_dec(v_impl_1460_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1587_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1580_ = lean_unsigned_to_nat(3u);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 4, v_l_1545_);
lean_ctor_set(v___x_1578_, 2, v_v_1313_);
lean_ctor_set(v___x_1578_, 1, v_k_1312_);
lean_ctor_set(v___x_1578_, 0, v___x_1461_);
v___x_1582_ = v___x_1578_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1586_, 3, v_l_1545_);
lean_ctor_set(v_reuseFailAlloc_1586_, 4, v_l_1545_);
v___x_1582_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v_r_1574_);
lean_ctor_set(v___x_1317_, 3, v___x_1582_);
lean_ctor_set(v___x_1317_, 2, v_v_1576_);
lean_ctor_set(v___x_1317_, 1, v_k_1575_);
lean_ctor_set(v___x_1317_, 0, v___x_1580_);
v___x_1584_ = v___x_1317_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1575_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1576_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_r_1574_);
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
lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1591_ = lean_unsigned_to_nat(2u);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v_impl_1460_);
lean_ctor_set(v___x_1317_, 3, v_r_1574_);
lean_ctor_set(v___x_1317_, 0, v___x_1591_);
v___x_1593_ = v___x_1317_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_r_1574_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_impl_1460_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
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
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = lean_unsigned_to_nat(1u);
v___x_1597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
lean_ctor_set(v___x_1597_, 1, v_k_1308_);
lean_ctor_set(v___x_1597_, 2, v_v_1309_);
lean_ctor_set(v___x_1597_, 3, v_t_1310_);
lean_ctor_set(v___x_1597_, 4, v_t_1310_);
return v___x_1597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(lean_object* v_k_1598_, lean_object* v_x_1599_){
_start:
{
if (lean_obj_tag(v_x_1599_) == 0)
{
lean_object* v___x_1600_; 
lean_dec_ref(v_k_1598_);
v___x_1600_ = lean_box(0);
return v___x_1600_;
}
else
{
lean_object* v_val_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_val_1601_ = lean_ctor_get(v_x_1599_, 0);
lean_inc(v_val_1601_);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_k_1598_);
lean_ctor_set(v___x_1602_, 1, v_val_1601_);
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4___boxed(lean_object* v_k_1605_, lean_object* v_x_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v_k_1605_, v_x_1606_);
lean_dec(v_x_1606_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(size_t v_sz_1608_, size_t v_i_1609_, lean_object* v_bs_1610_){
_start:
{
uint8_t v___x_1611_; 
v___x_1611_ = lean_usize_dec_lt(v_i_1609_, v_sz_1608_);
if (v___x_1611_ == 0)
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1612_, 0, v_bs_1610_);
return v___x_1612_;
}
else
{
lean_object* v_v_1613_; lean_object* v___x_1614_; 
v_v_1613_ = lean_array_uget_borrowed(v_bs_1610_, v_i_1609_);
lean_inc(v_v_1613_);
v___x_1614_ = l_Lean_Lsp_instFromJsonCallHierarchyIncomingCall_fromJson(v_v_1613_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v_bs_1610_);
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1624_; lean_object* v_bs_x27_1625_; size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
v_a_1623_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1624_ = lean_unsigned_to_nat(0u);
v_bs_x27_1625_ = lean_array_uset(v_bs_1610_, v_i_1609_, v___x_1624_);
v___x_1626_ = ((size_t)1ULL);
v___x_1627_ = lean_usize_add(v_i_1609_, v___x_1626_);
v___x_1628_ = lean_array_uset(v_bs_x27_1625_, v_i_1609_, v_a_1623_);
v_i_1609_ = v___x_1627_;
v_bs_1610_ = v___x_1628_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_sz_1630_, lean_object* v_i_1631_, lean_object* v_bs_1632_){
_start:
{
size_t v_sz_boxed_1633_; size_t v_i_boxed_1634_; lean_object* v_res_1635_; 
v_sz_boxed_1633_ = lean_unbox_usize(v_sz_1630_);
lean_dec(v_sz_1630_);
v_i_boxed_1634_ = lean_unbox_usize(v_i_1631_);
lean_dec(v_i_1631_);
v_res_1635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_boxed_1633_, v_i_boxed_1634_, v_bs_1632_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(lean_object* v_x_1636_){
_start:
{
if (lean_obj_tag(v_x_1636_) == 4)
{
lean_object* v_elems_1637_; size_t v_sz_1638_; size_t v___x_1639_; lean_object* v___x_1640_; 
v_elems_1637_ = lean_ctor_get(v_x_1636_, 0);
lean_inc_ref(v_elems_1637_);
lean_dec_ref_known(v_x_1636_, 1);
v_sz_1638_ = lean_array_size(v_elems_1637_);
v___x_1639_ = ((size_t)0ULL);
v___x_1640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_1638_, v___x_1639_, v_elems_1637_);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1641_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1642_ = lean_unsigned_to_nat(80u);
v___x_1643_ = l_Lean_Json_pretty(v_x_1636_, v___x_1642_);
v___x_1644_ = lean_string_append(v___x_1641_, v___x_1643_);
lean_dec_ref(v___x_1643_);
v___x_1645_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1646_ = lean_string_append(v___x_1644_, v___x_1645_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(lean_object* v_x_1650_){
_start:
{
if (lean_obj_tag(v_x_1650_) == 0)
{
lean_object* v___x_1651_; 
v___x_1651_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0));
return v___x_1651_;
}
else
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(v_x_1650_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1669_; 
v_a_1661_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1663_ = v___x_1652_;
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1652_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1665_, 0, v_a_1661_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1665_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(lean_object* v_expectedID_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Lsp_Ipc_stdout(v_a_1671_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1817_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1817_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1817_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_1674_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1808_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1808_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1808_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___y_1684_; lean_object* v___y_1685_; 
switch(lean_obj_tag(v_a_1679_))
{
case 2:
{
lean_object* v_id_1691_; lean_object* v_result_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1736_; 
v_id_1691_ = lean_ctor_get(v_a_1679_, 0);
v_result_1692_ = lean_ctor_get(v_a_1679_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_a_1679_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1694_ = v_a_1679_;
v_isShared_1695_ = v_isSharedCheck_1736_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_result_1692_);
lean_inc(v_id_1691_);
lean_dec(v_a_1679_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1736_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
uint8_t v___x_1696_; 
v___x_1696_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_1691_, v_expectedID_1670_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___y_1699_; 
lean_del_object(v___x_1694_);
lean_dec(v_result_1692_);
lean_del_object(v___x_1676_);
v___x_1697_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4));
switch(lean_obj_tag(v_expectedID_1670_))
{
case 0:
{
lean_object* v_s_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_s_1710_ = lean_ctor_get(v_expectedID_1670_, 0);
lean_inc_ref(v_s_1710_);
lean_dec_ref_known(v_expectedID_1670_, 1);
v___x_1711_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_1712_ = lean_string_append(v___x_1711_, v_s_1710_);
lean_dec_ref(v_s_1710_);
v___x_1713_ = lean_string_append(v___x_1712_, v___x_1711_);
v___y_1699_ = v___x_1713_;
goto v___jp_1698_;
}
case 1:
{
lean_object* v_n_1714_; lean_object* v___x_1715_; 
v_n_1714_ = lean_ctor_get(v_expectedID_1670_, 0);
lean_inc_ref(v_n_1714_);
lean_dec_ref_known(v_expectedID_1670_, 1);
v___x_1715_ = l_Lean_JsonNumber_toString(v_n_1714_);
v___y_1699_ = v___x_1715_;
goto v___jp_1698_;
}
default: 
{
lean_object* v___x_1716_; 
v___x_1716_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_1699_ = v___x_1716_;
goto v___jp_1698_;
}
}
v___jp_1698_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1700_ = lean_string_append(v___x_1697_, v___y_1699_);
lean_dec_ref(v___y_1699_);
v___x_1701_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5));
v___x_1702_ = lean_string_append(v___x_1700_, v___x_1701_);
switch(lean_obj_tag(v_id_1691_))
{
case 0:
{
lean_object* v_s_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_s_1703_ = lean_ctor_get(v_id_1691_, 0);
lean_inc_ref(v_s_1703_);
lean_dec_ref_known(v_id_1691_, 1);
v___x_1704_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_1705_ = lean_string_append(v___x_1704_, v_s_1703_);
lean_dec_ref(v_s_1703_);
v___x_1706_ = lean_string_append(v___x_1705_, v___x_1704_);
v___y_1684_ = v___x_1702_;
v___y_1685_ = v___x_1706_;
goto v___jp_1683_;
}
case 1:
{
lean_object* v_n_1707_; lean_object* v___x_1708_; 
v_n_1707_ = lean_ctor_get(v_id_1691_, 0);
lean_inc_ref(v_n_1707_);
lean_dec_ref_known(v_id_1691_, 1);
v___x_1708_ = l_Lean_JsonNumber_toString(v_n_1707_);
v___y_1684_ = v___x_1702_;
v___y_1685_ = v___x_1708_;
goto v___jp_1683_;
}
default: 
{
lean_object* v___x_1709_; 
v___x_1709_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_1684_ = v___x_1702_;
v___y_1685_ = v___x_1709_;
goto v___jp_1683_;
}
}
}
}
else
{
lean_object* v___x_1717_; 
lean_dec(v_id_1691_);
lean_del_object(v___x_1681_);
lean_inc(v_result_1692_);
v___x_1717_ = l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(v_result_1692_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1727_; 
lean_del_object(v___x_1694_);
lean_dec(v_expectedID_1670_);
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_1720_ = l_Lean_Json_compress(v_result_1692_);
v___x_1721_ = lean_string_append(v___x_1719_, v___x_1720_);
lean_dec_ref(v___x_1720_);
v___x_1722_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_1723_ = lean_string_append(v___x_1721_, v___x_1722_);
v___x_1724_ = lean_string_append(v___x_1723_, v_a_1718_);
lean_dec(v_a_1718_);
v___x_1725_ = lean_mk_io_user_error(v___x_1724_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 1);
lean_ctor_set(v___x_1676_, 0, v___x_1725_);
v___x_1727_ = v___x_1676_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; 
lean_dec(v_result_1692_);
v_a_1729_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1717_, 1);
if (v_isShared_1695_ == 0)
{
lean_ctor_set_tag(v___x_1694_, 0);
lean_ctor_set(v___x_1694_, 1, v_a_1729_);
lean_ctor_set(v___x_1694_, 0, v_expectedID_1670_);
v___x_1731_ = v___x_1694_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_expectedID_1670_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_a_1729_);
v___x_1731_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1733_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v___x_1731_);
v___x_1733_ = v___x_1676_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_1737_; uint8_t v_code_1738_; lean_object* v_message_1739_; lean_object* v_data_x3f_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___x_1772_; lean_object* v___y_1774_; 
lean_del_object(v___x_1681_);
lean_dec(v_expectedID_1670_);
v_id_1737_ = lean_ctor_get(v_a_1679_, 0);
lean_inc(v_id_1737_);
v_code_1738_ = lean_ctor_get_uint8(v_a_1679_, sizeof(void*)*3);
v_message_1739_ = lean_ctor_get(v_a_1679_, 1);
lean_inc_ref(v_message_1739_);
v_data_x3f_1740_ = lean_ctor_get(v_a_1679_, 2);
lean_inc(v_data_x3f_1740_);
lean_dec_ref_known(v_a_1679_, 3);
v___x_1741_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_1742_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_1772_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_1737_))
{
case 0:
{
lean_object* v_s_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_s_1790_ = lean_ctor_get(v_id_1737_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_id_1737_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v_id_1737_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_s_1790_);
lean_dec(v_id_1737_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set_tag(v___x_1792_, 3);
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_s_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
v___y_1774_ = v___x_1795_;
goto v___jp_1773_;
}
}
}
case 1:
{
lean_object* v_n_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
v_n_1798_ = lean_ctor_get(v_id_1737_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_id_1737_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v_id_1737_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_n_1798_);
lean_dec(v_id_1737_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 2);
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_n_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
v___y_1774_ = v___x_1803_;
goto v___jp_1773_;
}
}
}
default: 
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_box(0);
v___y_1774_ = v___x_1806_;
goto v___jp_1773_;
}
}
v___jp_1743_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
lean_inc(v___y_1747_);
lean_inc_ref(v___y_1746_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___y_1746_);
lean_ctor_set(v___x_1748_, 1, v___y_1747_);
v___x_1749_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_1750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_message_1739_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1749_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1751_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1748_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_1756_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_1755_, v_data_x3f_1740_);
lean_dec(v_data_x3f_1740_);
v___x_1757_ = l_List_appendTR___redArg(v___x_1754_, v___x_1756_);
v___x_1758_ = l_Lean_Json_mkObj(v___x_1757_);
lean_dec(v___x_1757_);
lean_inc_ref(v___y_1745_);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___y_1745_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
lean_ctor_set(v___x_1760_, 1, v___x_1752_);
v___x_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___y_1744_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1742_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = l_Lean_Json_mkObj(v___x_1762_);
lean_dec_ref_known(v___x_1762_, 2);
v___x_1764_ = l_Lean_Json_compress(v___x_1763_);
v___x_1765_ = lean_string_append(v___x_1741_, v___x_1764_);
lean_dec_ref(v___x_1764_);
v___x_1766_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1767_ = lean_string_append(v___x_1765_, v___x_1766_);
v___x_1768_ = lean_mk_io_user_error(v___x_1767_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 1);
lean_ctor_set(v___x_1676_, 0, v___x_1768_);
v___x_1770_ = v___x_1676_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
v___jp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1772_);
lean_ctor_set(v___x_1775_, 1, v___y_1774_);
v___x_1776_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_1777_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_1738_)
{
case 0:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1778_;
goto v___jp_1743_;
}
case 1:
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1779_;
goto v___jp_1743_;
}
case 2:
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1780_;
goto v___jp_1743_;
}
case 3:
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1781_;
goto v___jp_1743_;
}
case 4:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1782_;
goto v___jp_1743_;
}
case 5:
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1783_;
goto v___jp_1743_;
}
case 6:
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1784_;
goto v___jp_1743_;
}
case 7:
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1785_;
goto v___jp_1743_;
}
case 8:
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1786_;
goto v___jp_1743_;
}
case 9:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1787_;
goto v___jp_1743_;
}
case 10:
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1788_;
goto v___jp_1743_;
}
default: 
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_1744_ = v___x_1775_;
v___y_1745_ = v___x_1776_;
v___y_1746_ = v___x_1777_;
v___y_1747_ = v___x_1789_;
goto v___jp_1743_;
}
}
}
}
default: 
{
lean_del_object(v___x_1681_);
lean_dec(v_a_1679_);
lean_del_object(v___x_1676_);
goto _start;
}
}
v___jp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1686_ = lean_string_append(v___y_1684_, v___y_1685_);
lean_dec_ref(v___y_1685_);
v___x_1687_ = lean_mk_io_user_error(v___x_1686_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 1);
lean_ctor_set(v___x_1681_, 0, v___x_1687_);
v___x_1689_ = v___x_1681_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_del_object(v___x_1676_);
lean_dec(v_expectedID_1670_);
v_a_1809_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1678_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1678_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_expectedID_1670_);
v_a_1818_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1673_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1673_);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2___boxed(lean_object* v_expectedID_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v_expectedID_1826_, v_a_1827_);
lean_dec_ref(v_a_1827_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(lean_object* v_v_1830_){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = l_Lean_Lsp_instToJsonCallHierarchyIncomingCallsParams_toJson(v_v_1830_);
v___x_1832_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(lean_object* v_h_1833_, lean_object* v_r_1834_){
_start:
{
lean_object* v_id_1836_; lean_object* v_method_1837_; lean_object* v_param_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1858_; 
v_id_1836_ = lean_ctor_get(v_r_1834_, 0);
v_method_1837_ = lean_ctor_get(v_r_1834_, 1);
v_param_1838_ = lean_ctor_get(v_r_1834_, 2);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_r_1834_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1840_ = v_r_1834_;
v_isShared_1841_ = v_isSharedCheck_1858_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_param_1838_);
lean_inc(v_method_1837_);
lean_inc(v_id_1836_);
lean_dec(v_r_1834_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1858_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___y_1843_; lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(v_param_1838_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v___x_1849_; 
lean_dec_ref_known(v___x_1848_, 1);
v___x_1849_ = lean_box(0);
v___y_1843_ = v___x_1849_;
goto v___jp_1842_;
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1848_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1848_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
v___y_1843_ = v___x_1855_;
goto v___jp_1842_;
}
}
}
v___jp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 2, v___y_1843_);
v___x_1845_ = v___x_1840_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_id_1836_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_method_1837_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v___y_1843_);
v___x_1845_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_1833_, v___x_1845_);
return v___x_1846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1___boxed(lean_object* v_h_1859_, lean_object* v_r_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_h_1859_, v_r_1860_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(lean_object* v_r_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v_a_1867_; lean_object* v___x_1868_; 
v___x_1866_ = l_Lean_Lsp_Ipc_stdin(v_a_1864_);
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref(v___x_1866_);
v___x_1868_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_a_1867_, v_r_1863_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1___boxed(lean_object* v_r_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v_r_1869_, v_a_1870_);
lean_dec_ref(v_a_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(lean_object* v_k_1873_, lean_object* v_t_1874_){
_start:
{
if (lean_obj_tag(v_t_1874_) == 0)
{
lean_object* v_k_1875_; lean_object* v_l_1876_; lean_object* v_r_1877_; uint8_t v___x_1878_; 
v_k_1875_ = lean_ctor_get(v_t_1874_, 1);
v_l_1876_ = lean_ctor_get(v_t_1874_, 3);
v_r_1877_ = lean_ctor_get(v_t_1874_, 4);
v___x_1878_ = lean_string_compare(v_k_1873_, v_k_1875_);
switch(v___x_1878_)
{
case 0:
{
v_t_1874_ = v_l_1876_;
goto _start;
}
case 1:
{
uint8_t v___x_1880_; 
v___x_1880_ = 1;
return v___x_1880_;
}
default: 
{
v_t_1874_ = v_r_1877_;
goto _start;
}
}
}
else
{
uint8_t v___x_1882_; 
v___x_1882_ = 0;
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg___boxed(lean_object* v_k_1883_, lean_object* v_t_1884_){
_start:
{
uint8_t v_res_1885_; lean_object* v_r_1886_; 
v_res_1885_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_1883_, v_t_1884_);
lean_dec(v_t_1884_);
lean_dec_ref(v_k_1883_);
v_r_1886_ = lean_box(v_res_1885_);
return v_r_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(lean_object* v_requestNo_1894_, lean_object* v_item_1895_, lean_object* v_fromRanges_1896_, lean_object* v_visited_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_name_1900_; uint8_t v___x_1901_; 
v_name_1900_ = lean_ctor_get(v_item_1895_, 0);
v___x_1901_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_1900_, v_visited_1897_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_inc(v_requestNo_1894_);
v___x_1902_ = l_Lean_JsonNumber_fromNat(v_requestNo_1894_);
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
v___x_1904_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_1895_);
lean_inc_ref(v___x_1903_);
v___x_1905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
lean_ctor_set(v___x_1905_, 2, v_item_1895_);
v___x_1906_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v___x_1905_, v_a_1898_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v___x_1907_; 
lean_dec_ref_known(v___x_1906_, 1);
v___x_1907_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v___x_1903_, v_a_1898_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v_result_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1954_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v_result_1909_ = lean_ctor_get(v_a_1908_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_a_1908_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v_a_1908_, 0);
lean_dec(v_unused_1955_);
v___x_1911_ = v_a_1908_;
v_isShared_1912_ = v_isSharedCheck_1954_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_result_1909_);
lean_dec(v_a_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1954_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___y_1918_; 
v___x_1913_ = lean_box(0);
lean_inc_ref(v_name_1900_);
v___x_1914_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_1900_, v___x_1913_, v_visited_1897_);
v___x_1915_ = lean_unsigned_to_nat(1u);
v___x_1916_ = lean_nat_add(v_requestNo_1894_, v___x_1915_);
lean_dec(v_requestNo_1894_);
if (lean_obj_tag(v_result_1909_) == 0)
{
lean_object* v___x_1952_; 
v___x_1952_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2));
v___y_1918_ = v___x_1952_;
goto v___jp_1917_;
}
else
{
lean_object* v_val_1953_; 
v_val_1953_ = lean_ctor_get(v_result_1909_, 0);
lean_inc(v_val_1953_);
lean_dec_ref_known(v_result_1909_, 1);
v___y_1918_ = v_val_1953_;
goto v___jp_1917_;
}
v___jp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1919_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 1, v___x_1919_);
lean_ctor_set(v___x_1911_, 0, v___x_1916_);
v___x_1921_ = v___x_1911_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
size_t v_sz_1922_; size_t v___x_1923_; lean_object* v___x_1924_; 
v_sz_1922_ = lean_array_size(v___y_1918_);
v___x_1923_ = ((size_t)0ULL);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___x_1914_, v___y_1918_, v_sz_1922_, v___x_1923_, v___x_1921_, v_a_1898_);
lean_dec_ref(v___y_1918_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1942_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1942_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1942_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1941_; 
v_fst_1929_ = lean_ctor_get(v_a_1925_, 0);
v_snd_1930_ = lean_ctor_get(v_a_1925_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_a_1925_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1932_ = v_a_1925_;
v_isShared_1933_ = v_isSharedCheck_1941_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_snd_1930_);
lean_inc(v_fst_1929_);
lean_dec(v_a_1925_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1941_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1934_, 0, v_item_1895_);
lean_ctor_set(v___x_1934_, 1, v_fromRanges_1896_);
lean_ctor_set(v___x_1934_, 2, v_snd_1930_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 1, v_fst_1929_);
lean_ctor_set(v___x_1932_, 0, v___x_1934_);
v___x_1936_ = v___x_1932_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_fst_1929_);
v___x_1936_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1938_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1936_);
v___x_1938_ = v___x_1927_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec_ref(v_fromRanges_1896_);
lean_dec_ref(v_item_1895_);
v_a_1943_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1924_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1924_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v_visited_1897_);
lean_dec_ref(v_fromRanges_1896_);
lean_dec_ref(v_item_1895_);
lean_dec(v_requestNo_1894_);
v_a_1956_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1907_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1907_);
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
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref_known(v___x_1903_, 1);
lean_dec(v_visited_1897_);
lean_dec_ref(v_fromRanges_1896_);
lean_dec_ref(v_item_1895_);
lean_dec(v_requestNo_1894_);
v_a_1964_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1906_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1906_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_dec(v_visited_1897_);
lean_dec_ref(v_fromRanges_1896_);
v___x_1972_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_1973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1973_, 0, v_item_1895_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
lean_ctor_set(v___x_1973_, 2, v___x_1972_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v_requestNo_1894_);
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(lean_object* v___x_1976_, lean_object* v_as_1977_, size_t v_sz_1978_, size_t v_i_1979_, lean_object* v_b_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_usize_dec_lt(v_i_1979_, v_sz_1978_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_dec(v___x_1976_);
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v_b_1980_);
return v___x_1984_;
}
else
{
lean_object* v_fst_1985_; lean_object* v_snd_1986_; lean_object* v_a_1987_; lean_object* v_from_1988_; lean_object* v_fromRanges_1989_; lean_object* v___x_1990_; 
v_fst_1985_ = lean_ctor_get(v_b_1980_, 0);
lean_inc(v_fst_1985_);
v_snd_1986_ = lean_ctor_get(v_b_1980_, 1);
lean_inc(v_snd_1986_);
lean_dec_ref(v_b_1980_);
v_a_1987_ = lean_array_uget_borrowed(v_as_1977_, v_i_1979_);
v_from_1988_ = lean_ctor_get(v_a_1987_, 0);
v_fromRanges_1989_ = lean_ctor_get(v_a_1987_, 1);
lean_inc(v___x_1976_);
lean_inc_ref(v_fromRanges_1989_);
lean_inc_ref(v_from_1988_);
v___x_1990_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_1985_, v_from_1988_, v_fromRanges_1989_, v___x_1976_, v___y_1981_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v_fst_1992_; lean_object* v_snd_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2004_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v_fst_1992_ = lean_ctor_get(v_a_1991_, 0);
v_snd_1993_ = lean_ctor_get(v_a_1991_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_a_1991_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1995_ = v_a_1991_;
v_isShared_1996_ = v_isSharedCheck_2004_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_snd_1993_);
lean_inc(v_fst_1992_);
lean_dec(v_a_1991_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2004_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1997_ = lean_array_push(v_snd_1986_, v_fst_1992_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 1, v___x_1997_);
lean_ctor_set(v___x_1995_, 0, v_snd_1993_);
v___x_1999_ = v___x_1995_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_snd_1993_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
size_t v___x_2000_; size_t v___x_2001_; 
v___x_2000_ = ((size_t)1ULL);
v___x_2001_ = lean_usize_add(v_i_1979_, v___x_2000_);
v_i_1979_ = v___x_2001_;
v_b_1980_ = v___x_1999_;
goto _start;
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_snd_1986_);
lean_dec(v___x_1976_);
v_a_2005_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1990_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1990_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3___boxed(lean_object* v___x_2013_, lean_object* v_as_2014_, lean_object* v_sz_2015_, lean_object* v_i_2016_, lean_object* v_b_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
size_t v_sz_boxed_2020_; size_t v_i_boxed_2021_; lean_object* v_res_2022_; 
v_sz_boxed_2020_ = lean_unbox_usize(v_sz_2015_);
lean_dec(v_sz_2015_);
v_i_boxed_2021_ = lean_unbox_usize(v_i_2016_);
lean_dec(v_i_2016_);
v_res_2022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___x_2013_, v_as_2014_, v_sz_boxed_2020_, v_i_boxed_2021_, v_b_2017_, v___y_2018_);
lean_dec_ref(v___y_2018_);
lean_dec_ref(v_as_2014_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___boxed(lean_object* v_requestNo_2023_, lean_object* v_item_2024_, lean_object* v_fromRanges_2025_, lean_object* v_visited_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_requestNo_2023_, v_item_2024_, v_fromRanges_2025_, v_visited_2026_, v_a_2027_);
lean_dec_ref(v_a_2027_);
return v_res_2029_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(lean_object* v_00_u03b2_2030_, lean_object* v_k_2031_, lean_object* v_t_2032_){
_start:
{
uint8_t v___x_2033_; 
v___x_2033_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_2031_, v_t_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___boxed(lean_object* v_00_u03b2_2034_, lean_object* v_k_2035_, lean_object* v_t_2036_){
_start:
{
uint8_t v_res_2037_; lean_object* v_r_2038_; 
v_res_2037_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(v_00_u03b2_2034_, v_k_2035_, v_t_2036_);
lean_dec(v_t_2036_);
lean_dec_ref(v_k_2035_);
v_r_2038_ = lean_box(v_res_2037_);
return v_r_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4(lean_object* v_00_u03b2_2039_, lean_object* v_k_2040_, lean_object* v_v_2041_, lean_object* v_t_2042_, lean_object* v_hl_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_2040_, v_v_2041_, v_t_2042_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2045_, size_t v_i_2046_, lean_object* v_bs_2047_){
_start:
{
uint8_t v___x_2048_; 
v___x_2048_ = lean_usize_dec_lt(v_i_2046_, v_sz_2045_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
v___x_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_bs_2047_);
return v___x_2049_;
}
else
{
lean_object* v_v_2050_; lean_object* v___x_2051_; 
v_v_2050_ = lean_array_uget_borrowed(v_bs_2047_, v_i_2046_);
lean_inc(v_v_2050_);
v___x_2051_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v_v_2050_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v_bs_2047_);
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2061_; lean_object* v_bs_x27_2062_; size_t v___x_2063_; size_t v___x_2064_; lean_object* v___x_2065_; 
v_a_2060_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2061_ = lean_unsigned_to_nat(0u);
v_bs_x27_2062_ = lean_array_uset(v_bs_2047_, v_i_2046_, v___x_2061_);
v___x_2063_ = ((size_t)1ULL);
v___x_2064_ = lean_usize_add(v_i_2046_, v___x_2063_);
v___x_2065_ = lean_array_uset(v_bs_x27_2062_, v_i_2046_, v_a_2060_);
v_i_2046_ = v___x_2064_;
v_bs_2047_ = v___x_2065_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2067_, lean_object* v_i_2068_, lean_object* v_bs_2069_){
_start:
{
size_t v_sz_boxed_2070_; size_t v_i_boxed_2071_; lean_object* v_res_2072_; 
v_sz_boxed_2070_ = lean_unbox_usize(v_sz_2067_);
lean_dec(v_sz_2067_);
v_i_boxed_2071_ = lean_unbox_usize(v_i_2068_);
lean_dec(v_i_2068_);
v_res_2072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2070_, v_i_boxed_2071_, v_bs_2069_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(lean_object* v_x_2073_){
_start:
{
if (lean_obj_tag(v_x_2073_) == 4)
{
lean_object* v_elems_2074_; size_t v_sz_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
v_elems_2074_ = lean_ctor_get(v_x_2073_, 0);
lean_inc_ref(v_elems_2074_);
lean_dec_ref_known(v_x_2073_, 1);
v_sz_2075_ = lean_array_size(v_elems_2074_);
v___x_2076_ = ((size_t)0ULL);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_2075_, v___x_2076_, v_elems_2074_);
return v___x_2077_;
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2078_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2079_ = lean_unsigned_to_nat(80u);
v___x_2080_ = l_Lean_Json_pretty(v_x_2073_, v___x_2079_);
v___x_2081_ = lean_string_append(v___x_2078_, v___x_2080_);
lean_dec_ref(v___x_2080_);
v___x_2082_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2083_ = lean_string_append(v___x_2081_, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(lean_object* v_x_2087_){
_start:
{
if (lean_obj_tag(v_x_2087_) == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0));
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(v_x_2087_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2106_; 
v_a_2098_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2100_ = v___x_2089_;
v_isShared_2101_ = v_isSharedCheck_2106_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2089_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2106_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v_a_2098_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2102_);
v___x_2104_ = v___x_2100_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(lean_object* v_expectedID_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_Lsp_Ipc_stdout(v_a_2108_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2254_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2254_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2254_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_2111_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2245_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2245_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2245_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___y_2121_; lean_object* v___y_2122_; 
switch(lean_obj_tag(v_a_2116_))
{
case 2:
{
lean_object* v_id_2128_; lean_object* v_result_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2173_; 
v_id_2128_ = lean_ctor_get(v_a_2116_, 0);
v_result_2129_ = lean_ctor_get(v_a_2116_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_a_2116_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2131_ = v_a_2116_;
v_isShared_2132_ = v_isSharedCheck_2173_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_result_2129_);
lean_inc(v_id_2128_);
lean_dec(v_a_2116_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2173_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
uint8_t v___x_2133_; 
v___x_2133_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2128_, v_expectedID_2107_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; lean_object* v___y_2136_; 
lean_del_object(v___x_2131_);
lean_dec(v_result_2129_);
lean_del_object(v___x_2113_);
v___x_2134_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4));
switch(lean_obj_tag(v_expectedID_2107_))
{
case 0:
{
lean_object* v_s_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_s_2147_ = lean_ctor_get(v_expectedID_2107_, 0);
lean_inc_ref(v_s_2147_);
lean_dec_ref_known(v_expectedID_2107_, 1);
v___x_2148_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_2149_ = lean_string_append(v___x_2148_, v_s_2147_);
lean_dec_ref(v_s_2147_);
v___x_2150_ = lean_string_append(v___x_2149_, v___x_2148_);
v___y_2136_ = v___x_2150_;
goto v___jp_2135_;
}
case 1:
{
lean_object* v_n_2151_; lean_object* v___x_2152_; 
v_n_2151_ = lean_ctor_get(v_expectedID_2107_, 0);
lean_inc_ref(v_n_2151_);
lean_dec_ref_known(v_expectedID_2107_, 1);
v___x_2152_ = l_Lean_JsonNumber_toString(v_n_2151_);
v___y_2136_ = v___x_2152_;
goto v___jp_2135_;
}
default: 
{
lean_object* v___x_2153_; 
v___x_2153_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_2136_ = v___x_2153_;
goto v___jp_2135_;
}
}
v___jp_2135_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = lean_string_append(v___x_2134_, v___y_2136_);
lean_dec_ref(v___y_2136_);
v___x_2138_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5));
v___x_2139_ = lean_string_append(v___x_2137_, v___x_2138_);
switch(lean_obj_tag(v_id_2128_))
{
case 0:
{
lean_object* v_s_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_s_2140_ = lean_ctor_get(v_id_2128_, 0);
lean_inc_ref(v_s_2140_);
lean_dec_ref_known(v_id_2128_, 1);
v___x_2141_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_2142_ = lean_string_append(v___x_2141_, v_s_2140_);
lean_dec_ref(v_s_2140_);
v___x_2143_ = lean_string_append(v___x_2142_, v___x_2141_);
v___y_2121_ = v___x_2139_;
v___y_2122_ = v___x_2143_;
goto v___jp_2120_;
}
case 1:
{
lean_object* v_n_2144_; lean_object* v___x_2145_; 
v_n_2144_ = lean_ctor_get(v_id_2128_, 0);
lean_inc_ref(v_n_2144_);
lean_dec_ref_known(v_id_2128_, 1);
v___x_2145_ = l_Lean_JsonNumber_toString(v_n_2144_);
v___y_2121_ = v___x_2139_;
v___y_2122_ = v___x_2145_;
goto v___jp_2120_;
}
default: 
{
lean_object* v___x_2146_; 
v___x_2146_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_2121_ = v___x_2139_;
v___y_2122_ = v___x_2146_;
goto v___jp_2120_;
}
}
}
}
else
{
lean_object* v___x_2154_; 
lean_dec(v_id_2128_);
lean_del_object(v___x_2118_);
lean_inc(v_result_2129_);
v___x_2154_ = l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(v_result_2129_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; 
lean_del_object(v___x_2131_);
lean_dec(v_expectedID_2107_);
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
v___x_2156_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2157_ = l_Lean_Json_compress(v_result_2129_);
v___x_2158_ = lean_string_append(v___x_2156_, v___x_2157_);
lean_dec_ref(v___x_2157_);
v___x_2159_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2160_ = lean_string_append(v___x_2158_, v___x_2159_);
v___x_2161_ = lean_string_append(v___x_2160_, v_a_2155_);
lean_dec(v_a_2155_);
v___x_2162_ = lean_mk_io_user_error(v___x_2161_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set_tag(v___x_2113_, 1);
lean_ctor_set(v___x_2113_, 0, v___x_2162_);
v___x_2164_ = v___x_2113_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; 
lean_dec(v_result_2129_);
v_a_2166_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2154_, 1);
if (v_isShared_2132_ == 0)
{
lean_ctor_set_tag(v___x_2131_, 0);
lean_ctor_set(v___x_2131_, 1, v_a_2166_);
lean_ctor_set(v___x_2131_, 0, v_expectedID_2107_);
v___x_2168_ = v___x_2131_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_expectedID_2107_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_a_2166_);
v___x_2168_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2168_);
v___x_2170_ = v___x_2113_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
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
}
}
case 3:
{
lean_object* v_id_2174_; uint8_t v_code_2175_; lean_object* v_message_2176_; lean_object* v_data_x3f_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___x_2209_; lean_object* v___y_2211_; 
lean_del_object(v___x_2118_);
lean_dec(v_expectedID_2107_);
v_id_2174_ = lean_ctor_get(v_a_2116_, 0);
lean_inc(v_id_2174_);
v_code_2175_ = lean_ctor_get_uint8(v_a_2116_, sizeof(void*)*3);
v_message_2176_ = lean_ctor_get(v_a_2116_, 1);
lean_inc_ref(v_message_2176_);
v_data_x3f_2177_ = lean_ctor_get(v_a_2116_, 2);
lean_inc(v_data_x3f_2177_);
lean_dec_ref_known(v_a_2116_, 3);
v___x_2178_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2179_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2209_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2174_))
{
case 0:
{
lean_object* v_s_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
v_s_2227_ = lean_ctor_get(v_id_2174_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_id_2174_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v_id_2174_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_s_2227_);
lean_dec(v_id_2174_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set_tag(v___x_2229_, 3);
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_s_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
v___y_2211_ = v___x_2232_;
goto v___jp_2210_;
}
}
}
case 1:
{
lean_object* v_n_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v_n_2235_ = lean_ctor_get(v_id_2174_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_id_2174_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v_id_2174_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_n_2235_);
lean_dec(v_id_2174_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set_tag(v___x_2237_, 2);
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_n_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
v___y_2211_ = v___x_2240_;
goto v___jp_2210_;
}
}
}
default: 
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_box(0);
v___y_2211_ = v___x_2243_;
goto v___jp_2210_;
}
}
v___jp_2180_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
lean_inc(v___y_2184_);
lean_inc_ref(v___y_2183_);
v___x_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___y_2183_);
lean_ctor_set(v___x_2185_, 1, v___y_2184_);
v___x_2186_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2187_, 0, v_message_2176_);
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = lean_box(0);
v___x_2190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2185_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2193_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2192_, v_data_x3f_2177_);
lean_dec(v_data_x3f_2177_);
v___x_2194_ = l_List_appendTR___redArg(v___x_2191_, v___x_2193_);
v___x_2195_ = l_Lean_Json_mkObj(v___x_2194_);
lean_dec(v___x_2194_);
lean_inc_ref(v___y_2181_);
v___x_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___y_2181_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
lean_ctor_set(v___x_2197_, 1, v___x_2189_);
v___x_2198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___y_2182_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2179_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = l_Lean_Json_mkObj(v___x_2199_);
lean_dec_ref_known(v___x_2199_, 2);
v___x_2201_ = l_Lean_Json_compress(v___x_2200_);
v___x_2202_ = lean_string_append(v___x_2178_, v___x_2201_);
lean_dec_ref(v___x_2201_);
v___x_2203_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2204_ = lean_string_append(v___x_2202_, v___x_2203_);
v___x_2205_ = lean_mk_io_user_error(v___x_2204_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set_tag(v___x_2113_, 1);
lean_ctor_set(v___x_2113_, 0, v___x_2205_);
v___x_2207_ = v___x_2113_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
v___jp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2209_);
lean_ctor_set(v___x_2212_, 1, v___y_2211_);
v___x_2213_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2214_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2175_)
{
case 0:
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2215_;
goto v___jp_2180_;
}
case 1:
{
lean_object* v___x_2216_; 
v___x_2216_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2216_;
goto v___jp_2180_;
}
case 2:
{
lean_object* v___x_2217_; 
v___x_2217_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2217_;
goto v___jp_2180_;
}
case 3:
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2218_;
goto v___jp_2180_;
}
case 4:
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2219_;
goto v___jp_2180_;
}
case 5:
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2220_;
goto v___jp_2180_;
}
case 6:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2221_;
goto v___jp_2180_;
}
case 7:
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2222_;
goto v___jp_2180_;
}
case 8:
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2223_;
goto v___jp_2180_;
}
case 9:
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2224_;
goto v___jp_2180_;
}
case 10:
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2225_;
goto v___jp_2180_;
}
default: 
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2181_ = v___x_2213_;
v___y_2182_ = v___x_2212_;
v___y_2183_ = v___x_2214_;
v___y_2184_ = v___x_2226_;
goto v___jp_2180_;
}
}
}
}
default: 
{
lean_del_object(v___x_2118_);
lean_dec(v_a_2116_);
lean_del_object(v___x_2113_);
goto _start;
}
}
v___jp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2123_ = lean_string_append(v___y_2121_, v___y_2122_);
lean_dec_ref(v___y_2122_);
v___x_2124_ = lean_mk_io_user_error(v___x_2123_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set_tag(v___x_2118_, 1);
lean_ctor_set(v___x_2118_, 0, v___x_2124_);
v___x_2126_ = v___x_2118_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_del_object(v___x_2113_);
lean_dec(v_expectedID_2107_);
v_a_2246_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2115_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2115_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_expectedID_2107_);
v_a_2255_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2110_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2110_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1___boxed(lean_object* v_expectedID_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v_expectedID_2263_, v_a_2264_);
lean_dec_ref(v_a_2264_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(lean_object* v_as_2267_, size_t v_sz_2268_, size_t v_i_2269_, lean_object* v_b_2270_, lean_object* v___y_2271_){
_start:
{
uint8_t v___x_2273_; 
v___x_2273_ = lean_usize_dec_lt(v_i_2269_, v_sz_2268_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_b_2270_);
return v___x_2274_;
}
else
{
lean_object* v_fst_2275_; lean_object* v_snd_2276_; lean_object* v_a_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_fst_2275_ = lean_ctor_get(v_b_2270_, 0);
lean_inc(v_fst_2275_);
v_snd_2276_ = lean_ctor_get(v_b_2270_, 1);
lean_inc(v_snd_2276_);
lean_dec_ref(v_b_2270_);
v_a_2277_ = lean_array_uget_borrowed(v_as_2267_, v_i_2269_);
v___x_2278_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2279_ = lean_box(1);
lean_inc(v_a_2277_);
v___x_2280_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2275_, v_a_2277_, v___x_2278_, v___x_2279_, v___y_2271_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v_fst_2282_; lean_object* v_snd_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2294_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v_fst_2282_ = lean_ctor_get(v_a_2281_, 0);
v_snd_2283_ = lean_ctor_get(v_a_2281_, 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_a_2281_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2285_ = v_a_2281_;
v_isShared_2286_ = v_isSharedCheck_2294_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_snd_2283_);
lean_inc(v_fst_2282_);
lean_dec(v_a_2281_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2294_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2287_ = lean_array_push(v_snd_2276_, v_fst_2282_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v___x_2287_);
lean_ctor_set(v___x_2285_, 0, v_snd_2283_);
v___x_2289_ = v___x_2285_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_snd_2283_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
size_t v___x_2290_; size_t v___x_2291_; 
v___x_2290_ = ((size_t)1ULL);
v___x_2291_ = lean_usize_add(v_i_2269_, v___x_2290_);
v_i_2269_ = v___x_2291_;
v_b_2270_ = v___x_2289_;
goto _start;
}
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v_snd_2276_);
v_a_2295_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2280_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2280_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2___boxed(lean_object* v_as_2303_, lean_object* v_sz_2304_, lean_object* v_i_2305_, lean_object* v_b_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
size_t v_sz_boxed_2309_; size_t v_i_boxed_2310_; lean_object* v_res_2311_; 
v_sz_boxed_2309_ = lean_unbox_usize(v_sz_2304_);
lean_dec(v_sz_2304_);
v_i_boxed_2310_ = lean_unbox_usize(v_i_2305_);
lean_dec(v_i_2305_);
v_res_2311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v_as_2303_, v_sz_boxed_2309_, v_i_boxed_2310_, v_b_2306_, v___y_2307_);
lean_dec_ref(v___y_2307_);
lean_dec_ref(v_as_2303_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(lean_object* v_v_2312_){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = l_Lean_Lsp_instToJsonCallHierarchyPrepareParams_toJson(v_v_2312_);
v___x_2314_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(lean_object* v_h_2315_, lean_object* v_r_2316_){
_start:
{
lean_object* v_id_2318_; lean_object* v_method_2319_; lean_object* v_param_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2340_; 
v_id_2318_ = lean_ctor_get(v_r_2316_, 0);
v_method_2319_ = lean_ctor_get(v_r_2316_, 1);
v_param_2320_ = lean_ctor_get(v_r_2316_, 2);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_r_2316_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2322_ = v_r_2316_;
v_isShared_2323_ = v_isSharedCheck_2340_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_param_2320_);
lean_inc(v_method_2319_);
lean_inc(v_id_2318_);
lean_dec(v_r_2316_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2340_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___y_2325_; lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(v_param_2320_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v___x_2331_; 
lean_dec_ref_known(v___x_2330_, 1);
v___x_2331_ = lean_box(0);
v___y_2325_ = v___x_2331_;
goto v___jp_2324_;
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
v_a_2332_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2330_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2330_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
v___y_2325_ = v___x_2337_;
goto v___jp_2324_;
}
}
}
v___jp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 2, v___y_2325_);
v___x_2327_ = v___x_2322_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_id_2318_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_method_2319_);
lean_ctor_set(v_reuseFailAlloc_2329_, 2, v___y_2325_);
v___x_2327_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_2315_, v___x_2327_);
return v___x_2328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0___boxed(lean_object* v_h_2341_, lean_object* v_r_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_h_2341_, v_r_2342_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(lean_object* v_r_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2348_; lean_object* v_a_2349_; lean_object* v___x_2350_; 
v___x_2348_ = l_Lean_Lsp_Ipc_stdin(v_a_2346_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref(v___x_2348_);
v___x_2350_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_a_2349_, v_r_2345_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0___boxed(lean_object* v_r_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v_r_2351_, v_a_2352_);
lean_dec_ref(v_a_2352_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(lean_object* v_requestNo_2358_, lean_object* v_uri_2359_, lean_object* v_pos_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_inc(v_requestNo_2358_);
v___x_2363_ = l_Lean_JsonNumber_fromNat(v_requestNo_2358_);
v___x_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
v___x_2365_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_uri_2359_);
lean_ctor_set(v___x_2366_, 1, v_pos_2360_);
lean_inc_ref(v___x_2364_);
v___x_2367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2364_);
lean_ctor_set(v___x_2367_, 1, v___x_2365_);
lean_ctor_set(v___x_2367_, 2, v___x_2366_);
v___x_2368_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2367_, v_a_2361_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v___x_2369_; 
lean_dec_ref_known(v___x_2368_, 1);
v___x_2369_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2364_, v_a_2361_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v_result_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2413_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2369_, 1);
v_result_2371_ = lean_ctor_get(v_a_2370_, 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_a_2370_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; 
v_unused_2414_ = lean_ctor_get(v_a_2370_, 0);
lean_dec(v_unused_2414_);
v___x_2373_ = v_a_2370_;
v_isShared_2374_ = v_isSharedCheck_2413_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_result_2371_);
lean_dec(v_a_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2413_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___y_2378_; 
v___x_2375_ = lean_unsigned_to_nat(1u);
v___x_2376_ = lean_nat_add(v_requestNo_2358_, v___x_2375_);
lean_dec(v_requestNo_2358_);
if (lean_obj_tag(v_result_2371_) == 0)
{
lean_object* v___x_2411_; 
v___x_2411_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2378_ = v___x_2411_;
goto v___jp_2377_;
}
else
{
lean_object* v_val_2412_; 
v_val_2412_ = lean_ctor_get(v_result_2371_, 0);
lean_inc(v_val_2412_);
lean_dec_ref_known(v_result_2371_, 1);
v___y_2378_ = v_val_2412_;
goto v___jp_2377_;
}
v___jp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
v___x_2379_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 1, v___x_2379_);
lean_ctor_set(v___x_2373_, 0, v___x_2376_);
v___x_2381_ = v___x_2373_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
size_t v_sz_2382_; size_t v___x_2383_; lean_object* v___x_2384_; 
v_sz_2382_ = lean_array_size(v___y_2378_);
v___x_2383_ = ((size_t)0ULL);
v___x_2384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v___y_2378_, v_sz_2382_, v___x_2383_, v___x_2381_, v_a_2361_);
lean_dec_ref(v___y_2378_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2401_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2401_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2401_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_fst_2389_; lean_object* v_snd_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2400_; 
v_fst_2389_ = lean_ctor_get(v_a_2385_, 0);
v_snd_2390_ = lean_ctor_get(v_a_2385_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_a_2385_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2392_ = v_a_2385_;
v_isShared_2393_ = v_isSharedCheck_2400_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_snd_2390_);
lean_inc(v_fst_2389_);
lean_dec(v_a_2385_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2400_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 1, v_fst_2389_);
lean_ctor_set(v___x_2392_, 0, v_snd_2390_);
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_snd_2390_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_fst_2389_);
v___x_2395_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2397_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2395_);
v___x_2397_ = v___x_2387_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
v_a_2402_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2384_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2384_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v_requestNo_2358_);
v_a_2415_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2369_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2369_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec_ref_known(v___x_2364_, 1);
lean_dec(v_requestNo_2358_);
v_a_2423_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2368_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2368_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___boxed(lean_object* v_requestNo_2431_, lean_object* v_uri_2432_, lean_object* v_pos_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(v_requestNo_2431_, v_uri_2432_, v_pos_2433_, v_a_2434_);
lean_dec_ref(v_a_2434_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2437_, size_t v_i_2438_, lean_object* v_bs_2439_){
_start:
{
uint8_t v___x_2440_; 
v___x_2440_ = lean_usize_dec_lt(v_i_2438_, v_sz_2437_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2441_, 0, v_bs_2439_);
return v___x_2441_;
}
else
{
lean_object* v_v_2442_; lean_object* v___x_2443_; 
v_v_2442_ = lean_array_uget_borrowed(v_bs_2439_, v_i_2438_);
lean_inc(v_v_2442_);
v___x_2443_ = l_Lean_Lsp_instFromJsonCallHierarchyOutgoingCall_fromJson(v_v_2442_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec_ref(v_bs_2439_);
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2453_; lean_object* v_bs_x27_2454_; size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
v_a_2452_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2453_ = lean_unsigned_to_nat(0u);
v_bs_x27_2454_ = lean_array_uset(v_bs_2439_, v_i_2438_, v___x_2453_);
v___x_2455_ = ((size_t)1ULL);
v___x_2456_ = lean_usize_add(v_i_2438_, v___x_2455_);
v___x_2457_ = lean_array_uset(v_bs_x27_2454_, v_i_2438_, v_a_2452_);
v_i_2438_ = v___x_2456_;
v_bs_2439_ = v___x_2457_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2459_, lean_object* v_i_2460_, lean_object* v_bs_2461_){
_start:
{
size_t v_sz_boxed_2462_; size_t v_i_boxed_2463_; lean_object* v_res_2464_; 
v_sz_boxed_2462_ = lean_unbox_usize(v_sz_2459_);
lean_dec(v_sz_2459_);
v_i_boxed_2463_ = lean_unbox_usize(v_i_2460_);
lean_dec(v_i_2460_);
v_res_2464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2462_, v_i_boxed_2463_, v_bs_2461_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(lean_object* v_x_2465_){
_start:
{
if (lean_obj_tag(v_x_2465_) == 4)
{
lean_object* v_elems_2466_; size_t v_sz_2467_; size_t v___x_2468_; lean_object* v___x_2469_; 
v_elems_2466_ = lean_ctor_get(v_x_2465_, 0);
lean_inc_ref(v_elems_2466_);
lean_dec_ref_known(v_x_2465_, 1);
v_sz_2467_ = lean_array_size(v_elems_2466_);
v___x_2468_ = ((size_t)0ULL);
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_2467_, v___x_2468_, v_elems_2466_);
return v___x_2469_;
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2470_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2471_ = lean_unsigned_to_nat(80u);
v___x_2472_ = l_Lean_Json_pretty(v_x_2465_, v___x_2471_);
v___x_2473_ = lean_string_append(v___x_2470_, v___x_2472_);
lean_dec_ref(v___x_2472_);
v___x_2474_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2475_ = lean_string_append(v___x_2473_, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
return v___x_2476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(lean_object* v_x_2479_){
_start:
{
if (lean_obj_tag(v_x_2479_) == 0)
{
lean_object* v___x_2480_; 
v___x_2480_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0));
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(v_x_2479_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2498_; 
v_a_2490_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2492_ = v___x_2481_;
v_isShared_2493_ = v_isSharedCheck_2498_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2481_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2498_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v_a_2490_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2494_);
v___x_2496_ = v___x_2492_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2494_);
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
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(lean_object* v_expectedID_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_Lsp_Ipc_stdout(v_a_2500_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2646_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2505_ = v___x_2502_;
v_isShared_2506_ = v_isSharedCheck_2646_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2502_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2646_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_2503_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2637_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2637_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2637_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___y_2513_; lean_object* v___y_2514_; 
switch(lean_obj_tag(v_a_2508_))
{
case 2:
{
lean_object* v_id_2520_; lean_object* v_result_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2565_; 
v_id_2520_ = lean_ctor_get(v_a_2508_, 0);
v_result_2521_ = lean_ctor_get(v_a_2508_, 1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_a_2508_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2523_ = v_a_2508_;
v_isShared_2524_ = v_isSharedCheck_2565_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_result_2521_);
lean_inc(v_id_2520_);
lean_dec(v_a_2508_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2565_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
uint8_t v___x_2525_; 
v___x_2525_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2520_, v_expectedID_2499_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___y_2528_; 
lean_del_object(v___x_2523_);
lean_dec(v_result_2521_);
lean_del_object(v___x_2505_);
v___x_2526_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4));
switch(lean_obj_tag(v_expectedID_2499_))
{
case 0:
{
lean_object* v_s_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_s_2539_ = lean_ctor_get(v_expectedID_2499_, 0);
lean_inc_ref(v_s_2539_);
lean_dec_ref_known(v_expectedID_2499_, 1);
v___x_2540_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_2541_ = lean_string_append(v___x_2540_, v_s_2539_);
lean_dec_ref(v_s_2539_);
v___x_2542_ = lean_string_append(v___x_2541_, v___x_2540_);
v___y_2528_ = v___x_2542_;
goto v___jp_2527_;
}
case 1:
{
lean_object* v_n_2543_; lean_object* v___x_2544_; 
v_n_2543_ = lean_ctor_get(v_expectedID_2499_, 0);
lean_inc_ref(v_n_2543_);
lean_dec_ref_known(v_expectedID_2499_, 1);
v___x_2544_ = l_Lean_JsonNumber_toString(v_n_2543_);
v___y_2528_ = v___x_2544_;
goto v___jp_2527_;
}
default: 
{
lean_object* v___x_2545_; 
v___x_2545_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_2528_ = v___x_2545_;
goto v___jp_2527_;
}
}
v___jp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = lean_string_append(v___x_2526_, v___y_2528_);
lean_dec_ref(v___y_2528_);
v___x_2530_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5));
v___x_2531_ = lean_string_append(v___x_2529_, v___x_2530_);
switch(lean_obj_tag(v_id_2520_))
{
case 0:
{
lean_object* v_s_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v_s_2532_ = lean_ctor_get(v_id_2520_, 0);
lean_inc_ref(v_s_2532_);
lean_dec_ref_known(v_id_2520_, 1);
v___x_2533_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_2534_ = lean_string_append(v___x_2533_, v_s_2532_);
lean_dec_ref(v_s_2532_);
v___x_2535_ = lean_string_append(v___x_2534_, v___x_2533_);
v___y_2513_ = v___x_2531_;
v___y_2514_ = v___x_2535_;
goto v___jp_2512_;
}
case 1:
{
lean_object* v_n_2536_; lean_object* v___x_2537_; 
v_n_2536_ = lean_ctor_get(v_id_2520_, 0);
lean_inc_ref(v_n_2536_);
lean_dec_ref_known(v_id_2520_, 1);
v___x_2537_ = l_Lean_JsonNumber_toString(v_n_2536_);
v___y_2513_ = v___x_2531_;
v___y_2514_ = v___x_2537_;
goto v___jp_2512_;
}
default: 
{
lean_object* v___x_2538_; 
v___x_2538_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_2513_ = v___x_2531_;
v___y_2514_ = v___x_2538_;
goto v___jp_2512_;
}
}
}
}
else
{
lean_object* v___x_2546_; 
lean_dec(v_id_2520_);
lean_del_object(v___x_2510_);
lean_inc(v_result_2521_);
v___x_2546_ = l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(v_result_2521_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
lean_del_object(v___x_2523_);
lean_dec(v_expectedID_2499_);
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v___x_2548_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2549_ = l_Lean_Json_compress(v_result_2521_);
v___x_2550_ = lean_string_append(v___x_2548_, v___x_2549_);
lean_dec_ref(v___x_2549_);
v___x_2551_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2552_ = lean_string_append(v___x_2550_, v___x_2551_);
v___x_2553_ = lean_string_append(v___x_2552_, v_a_2547_);
lean_dec(v_a_2547_);
v___x_2554_ = lean_mk_io_user_error(v___x_2553_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set_tag(v___x_2505_, 1);
lean_ctor_set(v___x_2505_, 0, v___x_2554_);
v___x_2556_ = v___x_2505_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; 
lean_dec(v_result_2521_);
v_a_2558_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2546_, 1);
if (v_isShared_2524_ == 0)
{
lean_ctor_set_tag(v___x_2523_, 0);
lean_ctor_set(v___x_2523_, 1, v_a_2558_);
lean_ctor_set(v___x_2523_, 0, v_expectedID_2499_);
v___x_2560_ = v___x_2523_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_expectedID_2499_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_a_2558_);
v___x_2560_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2562_; 
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v___x_2560_);
v___x_2562_ = v___x_2505_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2566_; uint8_t v_code_2567_; lean_object* v_message_2568_; lean_object* v_data_x3f_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___x_2601_; lean_object* v___y_2603_; 
lean_del_object(v___x_2510_);
lean_dec(v_expectedID_2499_);
v_id_2566_ = lean_ctor_get(v_a_2508_, 0);
lean_inc(v_id_2566_);
v_code_2567_ = lean_ctor_get_uint8(v_a_2508_, sizeof(void*)*3);
v_message_2568_ = lean_ctor_get(v_a_2508_, 1);
lean_inc_ref(v_message_2568_);
v_data_x3f_2569_ = lean_ctor_get(v_a_2508_, 2);
lean_inc(v_data_x3f_2569_);
lean_dec_ref_known(v_a_2508_, 3);
v___x_2570_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2571_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2601_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2566_))
{
case 0:
{
lean_object* v_s_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
v_s_2619_ = lean_ctor_get(v_id_2566_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_id_2566_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v_id_2566_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_s_2619_);
lean_dec(v_id_2566_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
lean_ctor_set_tag(v___x_2621_, 3);
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_s_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
v___y_2603_ = v___x_2624_;
goto v___jp_2602_;
}
}
}
case 1:
{
lean_object* v_n_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
v_n_2627_ = lean_ctor_get(v_id_2566_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v_id_2566_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v_id_2566_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_n_2627_);
lean_dec(v_id_2566_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set_tag(v___x_2629_, 2);
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_n_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
v___y_2603_ = v___x_2632_;
goto v___jp_2602_;
}
}
}
default: 
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_box(0);
v___y_2603_ = v___x_2635_;
goto v___jp_2602_;
}
}
v___jp_2572_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
lean_inc(v___y_2576_);
lean_inc_ref(v___y_2575_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___y_2575_);
lean_ctor_set(v___x_2577_, 1, v___y_2576_);
v___x_2578_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2579_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2579_, 0, v_message_2568_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2578_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_box(0);
v___x_2582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2577_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2585_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2584_, v_data_x3f_2569_);
lean_dec(v_data_x3f_2569_);
v___x_2586_ = l_List_appendTR___redArg(v___x_2583_, v___x_2585_);
v___x_2587_ = l_Lean_Json_mkObj(v___x_2586_);
lean_dec(v___x_2586_);
lean_inc_ref(v___y_2574_);
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___y_2574_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
lean_ctor_set(v___x_2589_, 1, v___x_2581_);
v___x_2590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___y_2573_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2571_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = l_Lean_Json_mkObj(v___x_2591_);
lean_dec_ref_known(v___x_2591_, 2);
v___x_2593_ = l_Lean_Json_compress(v___x_2592_);
v___x_2594_ = lean_string_append(v___x_2570_, v___x_2593_);
lean_dec_ref(v___x_2593_);
v___x_2595_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2596_ = lean_string_append(v___x_2594_, v___x_2595_);
v___x_2597_ = lean_mk_io_user_error(v___x_2596_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set_tag(v___x_2505_, 1);
lean_ctor_set(v___x_2505_, 0, v___x_2597_);
v___x_2599_ = v___x_2505_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
v___jp_2602_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2601_);
lean_ctor_set(v___x_2604_, 1, v___y_2603_);
v___x_2605_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2606_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2567_)
{
case 0:
{
lean_object* v___x_2607_; 
v___x_2607_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2607_;
goto v___jp_2572_;
}
case 1:
{
lean_object* v___x_2608_; 
v___x_2608_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2608_;
goto v___jp_2572_;
}
case 2:
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2609_;
goto v___jp_2572_;
}
case 3:
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2610_;
goto v___jp_2572_;
}
case 4:
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2611_;
goto v___jp_2572_;
}
case 5:
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2612_;
goto v___jp_2572_;
}
case 6:
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2613_;
goto v___jp_2572_;
}
case 7:
{
lean_object* v___x_2614_; 
v___x_2614_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2614_;
goto v___jp_2572_;
}
case 8:
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2615_;
goto v___jp_2572_;
}
case 9:
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2616_;
goto v___jp_2572_;
}
case 10:
{
lean_object* v___x_2617_; 
v___x_2617_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2617_;
goto v___jp_2572_;
}
default: 
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2573_ = v___x_2604_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___x_2606_;
v___y_2576_ = v___x_2618_;
goto v___jp_2572_;
}
}
}
}
default: 
{
lean_del_object(v___x_2510_);
lean_dec(v_a_2508_);
lean_del_object(v___x_2505_);
goto _start;
}
}
v___jp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2515_ = lean_string_append(v___y_2513_, v___y_2514_);
lean_dec_ref(v___y_2514_);
v___x_2516_ = lean_mk_io_user_error(v___x_2515_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set_tag(v___x_2510_, 1);
lean_ctor_set(v___x_2510_, 0, v___x_2516_);
v___x_2518_ = v___x_2510_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_del_object(v___x_2505_);
lean_dec(v_expectedID_2499_);
v_a_2638_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2507_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2507_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v_expectedID_2499_);
v_a_2647_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2502_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2502_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1___boxed(lean_object* v_expectedID_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v_expectedID_2655_, v_a_2656_);
lean_dec_ref(v_a_2656_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(lean_object* v_v_2659_){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = l_Lean_Lsp_instToJsonCallHierarchyOutgoingCallsParams_toJson(v_v_2659_);
v___x_2661_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(lean_object* v_h_2662_, lean_object* v_r_2663_){
_start:
{
lean_object* v_id_2665_; lean_object* v_method_2666_; lean_object* v_param_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2687_; 
v_id_2665_ = lean_ctor_get(v_r_2663_, 0);
v_method_2666_ = lean_ctor_get(v_r_2663_, 1);
v_param_2667_ = lean_ctor_get(v_r_2663_, 2);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_r_2663_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2669_ = v_r_2663_;
v_isShared_2670_ = v_isSharedCheck_2687_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_param_2667_);
lean_inc(v_method_2666_);
lean_inc(v_id_2665_);
lean_dec(v_r_2663_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2687_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___y_2672_; lean_object* v___x_2677_; 
v___x_2677_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(v_param_2667_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v___x_2678_; 
lean_dec_ref_known(v___x_2677_, 1);
v___x_2678_ = lean_box(0);
v___y_2672_ = v___x_2678_;
goto v___jp_2671_;
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_a_2679_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2677_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2677_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
v___y_2672_ = v___x_2684_;
goto v___jp_2671_;
}
}
}
v___jp_2671_:
{
lean_object* v___x_2674_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 2, v___y_2672_);
v___x_2674_ = v___x_2669_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_id_2665_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_method_2666_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v___y_2672_);
v___x_2674_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_2662_, v___x_2674_);
return v___x_2675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0___boxed(lean_object* v_h_2688_, lean_object* v_r_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_h_2688_, v_r_2689_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(lean_object* v_r_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v___x_2695_; lean_object* v_a_2696_; lean_object* v___x_2697_; 
v___x_2695_ = l_Lean_Lsp_Ipc_stdin(v_a_2693_);
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2695_);
v___x_2697_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_a_2696_, v_r_2692_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0___boxed(lean_object* v_r_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v_r_2698_, v_a_2699_);
lean_dec_ref(v_a_2699_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(lean_object* v_requestNo_2705_, lean_object* v_item_2706_, lean_object* v_fromRanges_2707_, lean_object* v_visited_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_name_2711_; uint8_t v___x_2712_; 
v_name_2711_ = lean_ctor_get(v_item_2706_, 0);
v___x_2712_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_2711_, v_visited_2708_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_inc(v_requestNo_2705_);
v___x_2713_ = l_Lean_JsonNumber_fromNat(v_requestNo_2705_);
v___x_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
v___x_2715_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_2706_);
lean_inc_ref(v___x_2714_);
v___x_2716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
lean_ctor_set(v___x_2716_, 2, v_item_2706_);
v___x_2717_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v___x_2716_, v_a_2709_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v___x_2718_; 
lean_dec_ref_known(v___x_2717_, 1);
v___x_2718_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v___x_2714_, v_a_2709_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v_result_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2765_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2718_, 1);
v_result_2720_ = lean_ctor_get(v_a_2719_, 1);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_a_2719_);
if (v_isSharedCheck_2765_ == 0)
{
lean_object* v_unused_2766_; 
v_unused_2766_ = lean_ctor_get(v_a_2719_, 0);
lean_dec(v_unused_2766_);
v___x_2722_ = v_a_2719_;
v_isShared_2723_ = v_isSharedCheck_2765_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_result_2720_);
lean_dec(v_a_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2765_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___y_2729_; 
v___x_2724_ = lean_box(0);
lean_inc_ref(v_name_2711_);
v___x_2725_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_2711_, v___x_2724_, v_visited_2708_);
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_nat_add(v_requestNo_2705_, v___x_2726_);
lean_dec(v_requestNo_2705_);
if (lean_obj_tag(v_result_2720_) == 0)
{
lean_object* v___x_2763_; 
v___x_2763_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1));
v___y_2729_ = v___x_2763_;
goto v___jp_2728_;
}
else
{
lean_object* v_val_2764_; 
v_val_2764_ = lean_ctor_get(v_result_2720_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v_result_2720_, 1);
v___y_2729_ = v_val_2764_;
goto v___jp_2728_;
}
v___jp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2730_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 1, v___x_2730_);
lean_ctor_set(v___x_2722_, 0, v___x_2727_);
v___x_2732_ = v___x_2722_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2727_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
size_t v_sz_2733_; size_t v___x_2734_; lean_object* v___x_2735_; 
v_sz_2733_ = lean_array_size(v___y_2729_);
v___x_2734_ = ((size_t)0ULL);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___x_2725_, v___y_2729_, v_sz_2733_, v___x_2734_, v___x_2732_, v_a_2709_);
lean_dec_ref(v___y_2729_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2753_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2753_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2753_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v_fst_2740_; lean_object* v_snd_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2752_; 
v_fst_2740_ = lean_ctor_get(v_a_2736_, 0);
v_snd_2741_ = lean_ctor_get(v_a_2736_, 1);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_a_2736_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2743_ = v_a_2736_;
v_isShared_2744_ = v_isSharedCheck_2752_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_snd_2741_);
lean_inc(v_fst_2740_);
lean_dec(v_a_2736_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2752_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2745_, 0, v_item_2706_);
lean_ctor_set(v___x_2745_, 1, v_fromRanges_2707_);
lean_ctor_set(v___x_2745_, 2, v_snd_2741_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 1, v_fst_2740_);
lean_ctor_set(v___x_2743_, 0, v___x_2745_);
v___x_2747_ = v___x_2743_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_fst_2740_);
v___x_2747_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2749_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2747_);
v___x_2749_ = v___x_2738_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec_ref(v_fromRanges_2707_);
lean_dec_ref(v_item_2706_);
v_a_2754_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2735_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2735_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_visited_2708_);
lean_dec_ref(v_fromRanges_2707_);
lean_dec_ref(v_item_2706_);
lean_dec(v_requestNo_2705_);
v_a_2767_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2718_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2718_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec_ref_known(v___x_2714_, 1);
lean_dec(v_visited_2708_);
lean_dec_ref(v_fromRanges_2707_);
lean_dec_ref(v_item_2706_);
lean_dec(v_requestNo_2705_);
v_a_2775_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2717_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2717_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec(v_visited_2708_);
lean_dec_ref(v_fromRanges_2707_);
v___x_2783_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2784_, 0, v_item_2706_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
lean_ctor_set(v___x_2784_, 2, v___x_2783_);
v___x_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
lean_ctor_set(v___x_2785_, 1, v_requestNo_2705_);
v___x_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
return v___x_2786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(lean_object* v___x_2787_, lean_object* v_as_2788_, size_t v_sz_2789_, size_t v_i_2790_, lean_object* v_b_2791_, lean_object* v___y_2792_){
_start:
{
uint8_t v___x_2794_; 
v___x_2794_ = lean_usize_dec_lt(v_i_2790_, v_sz_2789_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; 
lean_dec(v___x_2787_);
v___x_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2795_, 0, v_b_2791_);
return v___x_2795_;
}
else
{
lean_object* v_fst_2796_; lean_object* v_snd_2797_; lean_object* v_a_2798_; lean_object* v_to_2799_; lean_object* v_fromRanges_2800_; lean_object* v___x_2801_; 
v_fst_2796_ = lean_ctor_get(v_b_2791_, 0);
lean_inc(v_fst_2796_);
v_snd_2797_ = lean_ctor_get(v_b_2791_, 1);
lean_inc(v_snd_2797_);
lean_dec_ref(v_b_2791_);
v_a_2798_ = lean_array_uget_borrowed(v_as_2788_, v_i_2790_);
v_to_2799_ = lean_ctor_get(v_a_2798_, 0);
v_fromRanges_2800_ = lean_ctor_get(v_a_2798_, 1);
lean_inc(v___x_2787_);
lean_inc_ref(v_fromRanges_2800_);
lean_inc_ref(v_to_2799_);
v___x_2801_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2796_, v_to_2799_, v_fromRanges_2800_, v___x_2787_, v___y_2792_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v_fst_2803_; lean_object* v_snd_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2815_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v_fst_2803_ = lean_ctor_get(v_a_2802_, 0);
v_snd_2804_ = lean_ctor_get(v_a_2802_, 1);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_a_2802_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2806_ = v_a_2802_;
v_isShared_2807_ = v_isSharedCheck_2815_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_snd_2804_);
lean_inc(v_fst_2803_);
lean_dec(v_a_2802_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2815_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2808_; lean_object* v___x_2810_; 
v___x_2808_ = lean_array_push(v_snd_2797_, v_fst_2803_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 1, v___x_2808_);
lean_ctor_set(v___x_2806_, 0, v_snd_2804_);
v___x_2810_ = v___x_2806_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_snd_2804_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
size_t v___x_2811_; size_t v___x_2812_; 
v___x_2811_ = ((size_t)1ULL);
v___x_2812_ = lean_usize_add(v_i_2790_, v___x_2811_);
v_i_2790_ = v___x_2812_;
v_b_2791_ = v___x_2810_;
goto _start;
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_snd_2797_);
lean_dec(v___x_2787_);
v_a_2816_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2801_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2801_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2___boxed(lean_object* v___x_2824_, lean_object* v_as_2825_, lean_object* v_sz_2826_, lean_object* v_i_2827_, lean_object* v_b_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
size_t v_sz_boxed_2831_; size_t v_i_boxed_2832_; lean_object* v_res_2833_; 
v_sz_boxed_2831_ = lean_unbox_usize(v_sz_2826_);
lean_dec(v_sz_2826_);
v_i_boxed_2832_ = lean_unbox_usize(v_i_2827_);
lean_dec(v_i_2827_);
v_res_2833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___x_2824_, v_as_2825_, v_sz_boxed_2831_, v_i_boxed_2832_, v_b_2828_, v___y_2829_);
lean_dec_ref(v___y_2829_);
lean_dec_ref(v_as_2825_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___boxed(lean_object* v_requestNo_2834_, lean_object* v_item_2835_, lean_object* v_fromRanges_2836_, lean_object* v_visited_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_requestNo_2834_, v_item_2835_, v_fromRanges_2836_, v_visited_2837_, v_a_2838_);
lean_dec_ref(v_a_2838_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(lean_object* v_as_2841_, size_t v_sz_2842_, size_t v_i_2843_, lean_object* v_b_2844_, lean_object* v___y_2845_){
_start:
{
uint8_t v___x_2847_; 
v___x_2847_ = lean_usize_dec_lt(v_i_2843_, v_sz_2842_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_b_2844_);
return v___x_2848_;
}
else
{
lean_object* v_fst_2849_; lean_object* v_snd_2850_; lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v_fst_2849_ = lean_ctor_get(v_b_2844_, 0);
lean_inc(v_fst_2849_);
v_snd_2850_ = lean_ctor_get(v_b_2844_, 1);
lean_inc(v_snd_2850_);
lean_dec_ref(v_b_2844_);
v_a_2851_ = lean_array_uget_borrowed(v_as_2841_, v_i_2843_);
v___x_2852_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2853_ = lean_box(1);
lean_inc(v_a_2851_);
v___x_2854_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2849_, v_a_2851_, v___x_2852_, v___x_2853_, v___y_2845_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v_fst_2856_; lean_object* v_snd_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2868_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v_fst_2856_ = lean_ctor_get(v_a_2855_, 0);
v_snd_2857_ = lean_ctor_get(v_a_2855_, 1);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_a_2855_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2859_ = v_a_2855_;
v_isShared_2860_ = v_isSharedCheck_2868_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_snd_2857_);
lean_inc(v_fst_2856_);
lean_dec(v_a_2855_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2868_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2861_ = lean_array_push(v_snd_2850_, v_fst_2856_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v___x_2861_);
lean_ctor_set(v___x_2859_, 0, v_snd_2857_);
v___x_2863_ = v___x_2859_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_snd_2857_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
size_t v___x_2864_; size_t v___x_2865_; 
v___x_2864_ = ((size_t)1ULL);
v___x_2865_ = lean_usize_add(v_i_2843_, v___x_2864_);
v_i_2843_ = v___x_2865_;
v_b_2844_ = v___x_2863_;
goto _start;
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec(v_snd_2850_);
v_a_2869_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2854_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2854_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0___boxed(lean_object* v_as_2877_, lean_object* v_sz_2878_, lean_object* v_i_2879_, lean_object* v_b_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
size_t v_sz_boxed_2883_; size_t v_i_boxed_2884_; lean_object* v_res_2885_; 
v_sz_boxed_2883_ = lean_unbox_usize(v_sz_2878_);
lean_dec(v_sz_2878_);
v_i_boxed_2884_ = lean_unbox_usize(v_i_2879_);
lean_dec(v_i_2879_);
v_res_2885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v_as_2877_, v_sz_boxed_2883_, v_i_boxed_2884_, v_b_2880_, v___y_2881_);
lean_dec_ref(v___y_2881_);
lean_dec_ref(v_as_2877_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(lean_object* v_requestNo_2886_, lean_object* v_uri_2887_, lean_object* v_pos_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
lean_inc(v_requestNo_2886_);
v___x_2891_ = l_Lean_JsonNumber_fromNat(v_requestNo_2886_);
v___x_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
v___x_2893_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v_uri_2887_);
lean_ctor_set(v___x_2894_, 1, v_pos_2888_);
lean_inc_ref(v___x_2892_);
v___x_2895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2892_);
lean_ctor_set(v___x_2895_, 1, v___x_2893_);
lean_ctor_set(v___x_2895_, 2, v___x_2894_);
v___x_2896_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2895_, v_a_2889_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v___x_2897_; 
lean_dec_ref_known(v___x_2896_, 1);
v___x_2897_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2892_, v_a_2889_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v_result_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2941_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___x_2897_, 1);
v_result_2899_ = lean_ctor_get(v_a_2898_, 1);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_a_2898_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; 
v_unused_2942_ = lean_ctor_get(v_a_2898_, 0);
lean_dec(v_unused_2942_);
v___x_2901_ = v_a_2898_;
v_isShared_2902_ = v_isSharedCheck_2941_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_result_2899_);
lean_dec(v_a_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2941_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___y_2906_; 
v___x_2903_ = lean_unsigned_to_nat(1u);
v___x_2904_ = lean_nat_add(v_requestNo_2886_, v___x_2903_);
lean_dec(v_requestNo_2886_);
if (lean_obj_tag(v_result_2899_) == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2906_ = v___x_2939_;
goto v___jp_2905_;
}
else
{
lean_object* v_val_2940_; 
v_val_2940_ = lean_ctor_get(v_result_2899_, 0);
lean_inc(v_val_2940_);
lean_dec_ref_known(v_result_2899_, 1);
v___y_2906_ = v_val_2940_;
goto v___jp_2905_;
}
v___jp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2907_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 1, v___x_2907_);
lean_ctor_set(v___x_2901_, 0, v___x_2904_);
v___x_2909_ = v___x_2901_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
size_t v_sz_2910_; size_t v___x_2911_; lean_object* v___x_2912_; 
v_sz_2910_ = lean_array_size(v___y_2906_);
v___x_2911_ = ((size_t)0ULL);
v___x_2912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v___y_2906_, v_sz_2910_, v___x_2911_, v___x_2909_, v_a_2889_);
lean_dec_ref(v___y_2906_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2929_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2915_ = v___x_2912_;
v_isShared_2916_ = v_isSharedCheck_2929_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2912_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2929_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v_fst_2917_; lean_object* v_snd_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2928_; 
v_fst_2917_ = lean_ctor_get(v_a_2913_, 0);
v_snd_2918_ = lean_ctor_get(v_a_2913_, 1);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_a_2913_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2920_ = v_a_2913_;
v_isShared_2921_ = v_isSharedCheck_2928_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_snd_2918_);
lean_inc(v_fst_2917_);
lean_dec(v_a_2913_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2928_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 1, v_fst_2917_);
lean_ctor_set(v___x_2920_, 0, v_snd_2918_);
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_snd_2918_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_fst_2917_);
v___x_2923_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2925_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v___x_2923_);
v___x_2925_ = v___x_2915_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v___x_2923_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
v_a_2930_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2912_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2912_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_requestNo_2886_);
v_a_2943_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2897_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2897_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec_ref_known(v___x_2892_, 1);
lean_dec(v_requestNo_2886_);
v_a_2951_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2896_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2896_);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy___boxed(lean_object* v_requestNo_2959_, lean_object* v_uri_2960_, lean_object* v_pos_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(v_requestNo_2959_, v_uri_2960_, v_pos_2961_, v_a_2962_);
lean_dec_ref(v_a_2962_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(lean_object* v_j_2965_, lean_object* v_k_2966_){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = l_Lean_Json_getObjValD(v_j_2965_, v_k_2966_);
v___x_2968_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v___x_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0___boxed(lean_object* v_j_2969_, lean_object* v_k_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_j_2969_, v_k_2970_);
lean_dec_ref(v_k_2970_);
return v_res_2971_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2978_ = 1;
v___x_2979_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1));
v___x_2980_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2979_, v___x_2978_);
return v___x_2980_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_2982_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2);
v___x_2983_ = lean_string_append(v___x_2982_, v___x_2981_);
return v___x_2983_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_2985_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_2986_ = lean_string_append(v___x_2985_, v___x_2984_);
return v___x_2986_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_2988_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4);
v___x_2989_ = lean_string_append(v___x_2988_, v___x_2987_);
return v___x_2989_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_2991_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_2992_ = lean_string_append(v___x_2991_, v___x_2990_);
return v___x_2992_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2993_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_2994_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6);
v___x_2995_ = lean_string_append(v___x_2994_, v___x_2993_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(lean_object* v_json_2996_){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_2996_);
v___x_2998_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_json_2996_, v___x_2997_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3008_; 
lean_dec(v_json_2996_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3008_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3008_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
v___x_3003_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5);
v___x_3004_ = lean_string_append(v___x_3003_, v_a_2999_);
lean_dec(v_a_2999_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3004_);
v___x_3006_ = v___x_3001_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v_a_3009_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_2998_, 1);
v___x_3010_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3011_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_json_2996_, v___x_3010_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_a_3009_);
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3014_ = v___x_3011_;
v_isShared_3015_ = v_isSharedCheck_3021_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3021_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3016_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7);
v___x_3017_ = lean_string_append(v___x_3016_, v_a_3012_);
lean_dec(v_a_3012_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v___x_3017_);
v___x_3019_ = v___x_3014_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3030_; 
v_a_3022_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3024_ = v___x_3011_;
v_isShared_3025_ = v_isSharedCheck_3030_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3011_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3030_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; lean_object* v___x_3028_; 
v___x_3026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3026_, 0, v_a_3009_);
lean_ctor_set(v___x_3026_, 1, v_a_3022_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3026_);
v___x_3028_ = v___x_3024_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_3031_, size_t v_i_3032_, lean_object* v_bs_3033_){
_start:
{
uint8_t v___x_3034_; 
v___x_3034_ = lean_usize_dec_lt(v_i_3032_, v_sz_3031_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3035_, 0, v_bs_3033_);
return v___x_3035_;
}
else
{
lean_object* v_v_3036_; lean_object* v___x_3037_; 
v_v_3036_ = lean_array_uget_borrowed(v_bs_3033_, v_i_3032_);
lean_inc(v_v_3036_);
v___x_3037_ = l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(v_v_3036_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v_bs_3033_);
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3047_; lean_object* v_bs_x27_3048_; size_t v___x_3049_; size_t v___x_3050_; lean_object* v___x_3051_; 
v_a_3046_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3037_, 1);
v___x_3047_ = lean_unsigned_to_nat(0u);
v_bs_x27_3048_ = lean_array_uset(v_bs_3033_, v_i_3032_, v___x_3047_);
v___x_3049_ = ((size_t)1ULL);
v___x_3050_ = lean_usize_add(v_i_3032_, v___x_3049_);
v___x_3051_ = lean_array_uset(v_bs_x27_3048_, v_i_3032_, v_a_3046_);
v_i_3032_ = v___x_3050_;
v_bs_3033_ = v___x_3051_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_3053_){
_start:
{
if (lean_obj_tag(v_x_3053_) == 4)
{
lean_object* v_elems_3054_; size_t v_sz_3055_; size_t v___x_3056_; lean_object* v___x_3057_; 
v_elems_3054_ = lean_ctor_get(v_x_3053_, 0);
lean_inc_ref(v_elems_3054_);
lean_dec_ref_known(v_x_3053_, 1);
v_sz_3055_ = lean_array_size(v_elems_3054_);
v___x_3056_ = ((size_t)0ULL);
v___x_3057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_3055_, v___x_3056_, v_elems_3054_);
return v___x_3057_;
}
else
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3058_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3059_ = lean_unsigned_to_nat(80u);
v___x_3060_ = l_Lean_Json_pretty(v_x_3053_, v___x_3059_);
v___x_3061_ = lean_string_append(v___x_3058_, v___x_3060_);
lean_dec_ref(v___x_3060_);
v___x_3062_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3063_ = lean_string_append(v___x_3061_, v___x_3062_);
v___x_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
return v___x_3064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(lean_object* v_j_3065_, lean_object* v_k_3066_){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = l_Lean_Json_getObjValD(v_j_3065_, v_k_3066_);
v___x_3068_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(v___x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1___boxed(lean_object* v_j_3069_, lean_object* v_k_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_j_3069_, v_k_3070_);
lean_dec_ref(v_k_3070_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_3072_, lean_object* v_i_3073_, lean_object* v_bs_3074_){
_start:
{
size_t v_sz_boxed_3075_; size_t v_i_boxed_3076_; lean_object* v_res_3077_; 
v_sz_boxed_3075_ = lean_unbox_usize(v_sz_3072_);
lean_dec(v_sz_3072_);
v_i_boxed_3076_ = lean_unbox_usize(v_i_3073_);
lean_dec(v_i_3073_);
v_res_3077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_3075_, v_i_boxed_3076_, v_bs_3074_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(lean_object* v_x_3080_){
_start:
{
lean_object* v_item_3081_; lean_object* v_children_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3102_; 
v_item_3081_ = lean_ctor_get(v_x_3080_, 0);
v_children_3082_ = lean_ctor_get(v_x_3080_, 1);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_x_3080_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3084_ = v_x_3080_;
v_isShared_3085_ = v_isSharedCheck_3102_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_children_3082_);
lean_inc(v_item_3081_);
lean_dec(v_x_3080_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3102_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3086_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_3087_ = l_Lean_Lsp_instToJsonLeanImport_toJson(v_item_3081_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 1, v___x_3087_);
lean_ctor_set(v___x_3084_, 0, v___x_3086_);
v___x_3089_ = v___x_3084_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3090_ = lean_box(0);
v___x_3091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3093_ = l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(v_children_3082_);
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3092_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
v___x_3095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v___x_3090_);
v___x_3096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
lean_ctor_set(v___x_3096_, 1, v___x_3090_);
v___x_3097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3091_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_3099_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_3097_, v___x_3098_);
v___x_3100_ = l_Lean_Json_mkObj(v___x_3099_);
lean_dec(v___x_3099_);
return v___x_3100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(size_t v_sz_3103_, size_t v_i_3104_, lean_object* v_bs_3105_){
_start:
{
uint8_t v___x_3106_; 
v___x_3106_ = lean_usize_dec_lt(v_i_3104_, v_sz_3103_);
if (v___x_3106_ == 0)
{
return v_bs_3105_;
}
else
{
lean_object* v_v_3107_; lean_object* v___x_3108_; lean_object* v_bs_x27_3109_; lean_object* v___x_3110_; size_t v___x_3111_; size_t v___x_3112_; lean_object* v___x_3113_; 
v_v_3107_ = lean_array_uget(v_bs_3105_, v_i_3104_);
v___x_3108_ = lean_unsigned_to_nat(0u);
v_bs_x27_3109_ = lean_array_uset(v_bs_3105_, v_i_3104_, v___x_3108_);
v___x_3110_ = l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(v_v_3107_);
v___x_3111_ = ((size_t)1ULL);
v___x_3112_ = lean_usize_add(v_i_3104_, v___x_3111_);
v___x_3113_ = lean_array_uset(v_bs_x27_3109_, v_i_3104_, v___x_3110_);
v_i_3104_ = v___x_3112_;
v_bs_3105_ = v___x_3113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(lean_object* v_a_3115_){
_start:
{
size_t v_sz_3116_; size_t v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_sz_3116_ = lean_array_size(v_a_3115_);
v___x_3117_ = ((size_t)0ULL);
v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_3116_, v___x_3117_, v_a_3115_);
v___x_3119_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3120_, lean_object* v_i_3121_, lean_object* v_bs_3122_){
_start:
{
size_t v_sz_boxed_3123_; size_t v_i_boxed_3124_; lean_object* v_res_3125_; 
v_sz_boxed_3123_ = lean_unbox_usize(v_sz_3120_);
lean_dec(v_sz_3120_);
v_i_boxed_3124_ = lean_unbox_usize(v_i_3121_);
lean_dec(v_i_3121_);
v_res_3125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_boxed_3123_, v_i_boxed_3124_, v_bs_3122_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(size_t v_sz_3128_, size_t v_i_3129_, lean_object* v_bs_3130_){
_start:
{
uint8_t v___x_3131_; 
v___x_3131_ = lean_usize_dec_lt(v_i_3129_, v_sz_3128_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; 
v___x_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3132_, 0, v_bs_3130_);
return v___x_3132_;
}
else
{
lean_object* v_v_3133_; lean_object* v___x_3134_; 
v_v_3133_ = lean_array_uget_borrowed(v_bs_3130_, v_i_3129_);
lean_inc(v_v_3133_);
v___x_3134_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v_v_3133_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec_ref(v_bs_3130_);
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3134_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3134_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3144_; lean_object* v_bs_x27_3145_; size_t v___x_3146_; size_t v___x_3147_; lean_object* v___x_3148_; 
v_a_3143_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3134_, 1);
v___x_3144_ = lean_unsigned_to_nat(0u);
v_bs_x27_3145_ = lean_array_uset(v_bs_3130_, v_i_3129_, v___x_3144_);
v___x_3146_ = ((size_t)1ULL);
v___x_3147_ = lean_usize_add(v_i_3129_, v___x_3146_);
v___x_3148_ = lean_array_uset(v_bs_x27_3145_, v_i_3129_, v_a_3143_);
v_i_3129_ = v___x_3147_;
v_bs_3130_ = v___x_3148_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_3150_, lean_object* v_i_3151_, lean_object* v_bs_3152_){
_start:
{
size_t v_sz_boxed_3153_; size_t v_i_boxed_3154_; lean_object* v_res_3155_; 
v_sz_boxed_3153_ = lean_unbox_usize(v_sz_3150_);
lean_dec(v_sz_3150_);
v_i_boxed_3154_ = lean_unbox_usize(v_i_3151_);
lean_dec(v_i_3151_);
v_res_3155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_boxed_3153_, v_i_boxed_3154_, v_bs_3152_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(lean_object* v_x_3156_){
_start:
{
if (lean_obj_tag(v_x_3156_) == 4)
{
lean_object* v_elems_3157_; size_t v_sz_3158_; size_t v___x_3159_; lean_object* v___x_3160_; 
v_elems_3157_ = lean_ctor_get(v_x_3156_, 0);
lean_inc_ref(v_elems_3157_);
lean_dec_ref_known(v_x_3156_, 1);
v_sz_3158_ = lean_array_size(v_elems_3157_);
v___x_3159_ = ((size_t)0ULL);
v___x_3160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_3158_, v___x_3159_, v_elems_3157_);
return v___x_3160_;
}
else
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3161_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3162_ = lean_unsigned_to_nat(80u);
v___x_3163_ = l_Lean_Json_pretty(v_x_3156_, v___x_3162_);
v___x_3164_ = lean_string_append(v___x_3161_, v___x_3163_);
lean_dec_ref(v___x_3163_);
v___x_3165_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3166_ = lean_string_append(v___x_3164_, v___x_3165_);
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(lean_object* v_expectedID_3168_, lean_object* v_a_3169_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_Lsp_Ipc_stdout(v_a_3169_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3315_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3174_ = v___x_3171_;
v_isShared_3175_ = v_isSharedCheck_3315_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3315_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_3172_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3306_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3306_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3306_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___y_3182_; lean_object* v___y_3183_; 
switch(lean_obj_tag(v_a_3177_))
{
case 2:
{
lean_object* v_id_3189_; lean_object* v_result_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3234_; 
v_id_3189_ = lean_ctor_get(v_a_3177_, 0);
v_result_3190_ = lean_ctor_get(v_a_3177_, 1);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_a_3177_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3192_ = v_a_3177_;
v_isShared_3193_ = v_isSharedCheck_3234_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_result_3190_);
lean_inc(v_id_3189_);
lean_dec(v_a_3177_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3234_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
uint8_t v___x_3194_; 
v___x_3194_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3189_, v_expectedID_3168_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; lean_object* v___y_3197_; 
lean_del_object(v___x_3192_);
lean_dec(v_result_3190_);
lean_del_object(v___x_3174_);
v___x_3195_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4));
switch(lean_obj_tag(v_expectedID_3168_))
{
case 0:
{
lean_object* v_s_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_s_3208_ = lean_ctor_get(v_expectedID_3168_, 0);
lean_inc_ref(v_s_3208_);
lean_dec_ref_known(v_expectedID_3168_, 1);
v___x_3209_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_3210_ = lean_string_append(v___x_3209_, v_s_3208_);
lean_dec_ref(v_s_3208_);
v___x_3211_ = lean_string_append(v___x_3210_, v___x_3209_);
v___y_3197_ = v___x_3211_;
goto v___jp_3196_;
}
case 1:
{
lean_object* v_n_3212_; lean_object* v___x_3213_; 
v_n_3212_ = lean_ctor_get(v_expectedID_3168_, 0);
lean_inc_ref(v_n_3212_);
lean_dec_ref_known(v_expectedID_3168_, 1);
v___x_3213_ = l_Lean_JsonNumber_toString(v_n_3212_);
v___y_3197_ = v___x_3213_;
goto v___jp_3196_;
}
default: 
{
lean_object* v___x_3214_; 
v___x_3214_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_3197_ = v___x_3214_;
goto v___jp_3196_;
}
}
v___jp_3196_:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3198_ = lean_string_append(v___x_3195_, v___y_3197_);
lean_dec_ref(v___y_3197_);
v___x_3199_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5));
v___x_3200_ = lean_string_append(v___x_3198_, v___x_3199_);
switch(lean_obj_tag(v_id_3189_))
{
case 0:
{
lean_object* v_s_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_s_3201_ = lean_ctor_get(v_id_3189_, 0);
lean_inc_ref(v_s_3201_);
lean_dec_ref_known(v_id_3189_, 1);
v___x_3202_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_3203_ = lean_string_append(v___x_3202_, v_s_3201_);
lean_dec_ref(v_s_3201_);
v___x_3204_ = lean_string_append(v___x_3203_, v___x_3202_);
v___y_3182_ = v___x_3200_;
v___y_3183_ = v___x_3204_;
goto v___jp_3181_;
}
case 1:
{
lean_object* v_n_3205_; lean_object* v___x_3206_; 
v_n_3205_ = lean_ctor_get(v_id_3189_, 0);
lean_inc_ref(v_n_3205_);
lean_dec_ref_known(v_id_3189_, 1);
v___x_3206_ = l_Lean_JsonNumber_toString(v_n_3205_);
v___y_3182_ = v___x_3200_;
v___y_3183_ = v___x_3206_;
goto v___jp_3181_;
}
default: 
{
lean_object* v___x_3207_; 
v___x_3207_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_3182_ = v___x_3200_;
v___y_3183_ = v___x_3207_;
goto v___jp_3181_;
}
}
}
}
else
{
lean_object* v___x_3215_; 
lean_dec(v_id_3189_);
lean_del_object(v___x_3179_);
lean_inc(v_result_3190_);
v___x_3215_ = l_Lean_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(v_result_3190_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
lean_del_object(v___x_3192_);
lean_dec(v_expectedID_3168_);
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3215_, 1);
v___x_3217_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3218_ = l_Lean_Json_compress(v_result_3190_);
v___x_3219_ = lean_string_append(v___x_3217_, v___x_3218_);
lean_dec_ref(v___x_3218_);
v___x_3220_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3221_ = lean_string_append(v___x_3219_, v___x_3220_);
v___x_3222_ = lean_string_append(v___x_3221_, v_a_3216_);
lean_dec(v_a_3216_);
v___x_3223_ = lean_mk_io_user_error(v___x_3222_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 1);
lean_ctor_set(v___x_3174_, 0, v___x_3223_);
v___x_3225_ = v___x_3174_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; 
lean_dec(v_result_3190_);
v_a_3227_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3215_, 1);
if (v_isShared_3193_ == 0)
{
lean_ctor_set_tag(v___x_3192_, 0);
lean_ctor_set(v___x_3192_, 1, v_a_3227_);
lean_ctor_set(v___x_3192_, 0, v_expectedID_3168_);
v___x_3229_ = v___x_3192_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_expectedID_3168_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_a_3227_);
v___x_3229_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
lean_object* v___x_3231_; 
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3229_);
v___x_3231_ = v___x_3174_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3235_; uint8_t v_code_3236_; lean_object* v_message_3237_; lean_object* v_data_x3f_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___x_3270_; lean_object* v___y_3272_; 
lean_del_object(v___x_3179_);
lean_dec(v_expectedID_3168_);
v_id_3235_ = lean_ctor_get(v_a_3177_, 0);
lean_inc(v_id_3235_);
v_code_3236_ = lean_ctor_get_uint8(v_a_3177_, sizeof(void*)*3);
v_message_3237_ = lean_ctor_get(v_a_3177_, 1);
lean_inc_ref(v_message_3237_);
v_data_x3f_3238_ = lean_ctor_get(v_a_3177_, 2);
lean_inc(v_data_x3f_3238_);
lean_dec_ref_known(v_a_3177_, 3);
v___x_3239_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3240_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3270_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3235_))
{
case 0:
{
lean_object* v_s_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
v_s_3288_ = lean_ctor_get(v_id_3235_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_id_3235_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v_id_3235_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_s_3288_);
lean_dec(v_id_3235_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
lean_ctor_set_tag(v___x_3290_, 3);
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_s_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
v___y_3272_ = v___x_3293_;
goto v___jp_3271_;
}
}
}
case 1:
{
lean_object* v_n_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
v_n_3296_ = lean_ctor_get(v_id_3235_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_id_3235_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v_id_3235_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_n_3296_);
lean_dec(v_id_3235_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
lean_ctor_set_tag(v___x_3298_, 2);
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_n_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
v___y_3272_ = v___x_3301_;
goto v___jp_3271_;
}
}
}
default: 
{
lean_object* v___x_3304_; 
v___x_3304_ = lean_box(0);
v___y_3272_ = v___x_3304_;
goto v___jp_3271_;
}
}
v___jp_3241_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3268_; 
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3243_);
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___y_3243_);
lean_ctor_set(v___x_3246_, 1, v___y_3245_);
v___x_3247_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3248_, 0, v_message_3237_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = lean_box(0);
v___x_3251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3246_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3254_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3253_, v_data_x3f_3238_);
lean_dec(v_data_x3f_3238_);
v___x_3255_ = l_List_appendTR___redArg(v___x_3252_, v___x_3254_);
v___x_3256_ = l_Lean_Json_mkObj(v___x_3255_);
lean_dec(v___x_3255_);
lean_inc_ref(v___y_3244_);
v___x_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___y_3244_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set(v___x_3258_, 1, v___x_3250_);
v___x_3259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___y_3242_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3240_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = l_Lean_Json_mkObj(v___x_3260_);
lean_dec_ref_known(v___x_3260_, 2);
v___x_3262_ = l_Lean_Json_compress(v___x_3261_);
v___x_3263_ = lean_string_append(v___x_3239_, v___x_3262_);
lean_dec_ref(v___x_3262_);
v___x_3264_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3265_ = lean_string_append(v___x_3263_, v___x_3264_);
v___x_3266_ = lean_mk_io_user_error(v___x_3265_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 1);
lean_ctor_set(v___x_3174_, 0, v___x_3266_);
v___x_3268_ = v___x_3174_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
v___jp_3271_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3270_);
lean_ctor_set(v___x_3273_, 1, v___y_3272_);
v___x_3274_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3275_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3236_)
{
case 0:
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3276_;
goto v___jp_3241_;
}
case 1:
{
lean_object* v___x_3277_; 
v___x_3277_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3277_;
goto v___jp_3241_;
}
case 2:
{
lean_object* v___x_3278_; 
v___x_3278_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3278_;
goto v___jp_3241_;
}
case 3:
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3279_;
goto v___jp_3241_;
}
case 4:
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3280_;
goto v___jp_3241_;
}
case 5:
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3281_;
goto v___jp_3241_;
}
case 6:
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3282_;
goto v___jp_3241_;
}
case 7:
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3283_;
goto v___jp_3241_;
}
case 8:
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3284_;
goto v___jp_3241_;
}
case 9:
{
lean_object* v___x_3285_; 
v___x_3285_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3285_;
goto v___jp_3241_;
}
case 10:
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3286_;
goto v___jp_3241_;
}
default: 
{
lean_object* v___x_3287_; 
v___x_3287_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3242_ = v___x_3273_;
v___y_3243_ = v___x_3275_;
v___y_3244_ = v___x_3274_;
v___y_3245_ = v___x_3287_;
goto v___jp_3241_;
}
}
}
}
default: 
{
lean_del_object(v___x_3179_);
lean_dec(v_a_3177_);
lean_del_object(v___x_3174_);
goto _start;
}
}
v___jp_3181_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3184_ = lean_string_append(v___y_3182_, v___y_3183_);
lean_dec_ref(v___y_3183_);
v___x_3185_ = lean_mk_io_user_error(v___x_3184_);
if (v_isShared_3180_ == 0)
{
lean_ctor_set_tag(v___x_3179_, 1);
lean_ctor_set(v___x_3179_, 0, v___x_3185_);
v___x_3187_ = v___x_3179_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_del_object(v___x_3174_);
lean_dec(v_expectedID_3168_);
v_a_3307_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3176_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3176_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_dec(v_expectedID_3168_);
v_a_3316_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3171_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3171_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1___boxed(lean_object* v_expectedID_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v_expectedID_3324_, v_a_3325_);
lean_dec_ref(v_a_3325_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(lean_object* v_v_3328_){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_v_3328_);
v___x_3330_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_v_3331_);
lean_dec_ref(v_v_3331_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(lean_object* v_h_3333_, lean_object* v_r_3334_){
_start:
{
lean_object* v_id_3336_; lean_object* v_method_3337_; lean_object* v_param_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3358_; 
v_id_3336_ = lean_ctor_get(v_r_3334_, 0);
v_method_3337_ = lean_ctor_get(v_r_3334_, 1);
v_param_3338_ = lean_ctor_get(v_r_3334_, 2);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_r_3334_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3340_ = v_r_3334_;
v_isShared_3341_ = v_isSharedCheck_3358_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_param_3338_);
lean_inc(v_method_3337_);
lean_inc(v_id_3336_);
lean_dec(v_r_3334_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3358_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___y_3343_; lean_object* v___x_3348_; 
v___x_3348_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_param_3338_);
lean_dec(v_param_3338_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v___x_3349_; 
lean_dec_ref_known(v___x_3348_, 1);
v___x_3349_ = lean_box(0);
v___y_3343_ = v___x_3349_;
goto v___jp_3342_;
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
v_a_3350_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3348_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3348_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
v___y_3343_ = v___x_3355_;
goto v___jp_3342_;
}
}
}
v___jp_3342_:
{
lean_object* v___x_3345_; 
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 2, v___y_3343_);
v___x_3345_ = v___x_3340_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_id_3336_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v_method_3337_);
lean_ctor_set(v_reuseFailAlloc_3347_, 2, v___y_3343_);
v___x_3345_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3346_; 
v___x_3346_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_3333_, v___x_3345_);
return v___x_3346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0___boxed(lean_object* v_h_3359_, lean_object* v_r_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_h_3359_, v_r_3360_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(lean_object* v_r_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v___x_3366_; lean_object* v_a_3367_; lean_object* v___x_3368_; 
v___x_3366_ = l_Lean_Lsp_Ipc_stdin(v_a_3364_);
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref(v___x_3366_);
v___x_3368_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_a_3367_, v_r_3363_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0___boxed(lean_object* v_r_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v_r_3369_, v_a_3370_);
lean_dec_ref(v_a_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(lean_object* v_requestNo_3376_, lean_object* v_item_3377_, lean_object* v_visited_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_module_3381_; lean_object* v_name_3382_; uint8_t v___x_3383_; 
v_module_3381_ = lean_ctor_get(v_item_3377_, 0);
v_name_3382_ = lean_ctor_get(v_module_3381_, 0);
v___x_3383_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3382_, v_visited_3378_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
lean_inc(v_requestNo_3376_);
v___x_3384_ = l_Lean_JsonNumber_fromNat(v_requestNo_3376_);
v___x_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
v___x_3386_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0));
lean_inc_ref(v_module_3381_);
lean_inc_ref(v___x_3385_);
v___x_3387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
lean_ctor_set(v___x_3387_, 2, v_module_3381_);
v___x_3388_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v___x_3387_, v_a_3379_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v___x_3389_; 
lean_dec_ref_known(v___x_3388_, 1);
v___x_3389_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3385_, v_a_3379_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v_result_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3432_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___x_3389_, 1);
v_result_3391_ = lean_ctor_get(v_a_3390_, 1);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_a_3390_);
if (v_isSharedCheck_3432_ == 0)
{
lean_object* v_unused_3433_; 
v_unused_3433_ = lean_ctor_get(v_a_3390_, 0);
lean_dec(v_unused_3433_);
v___x_3393_ = v_a_3390_;
v_isShared_3394_ = v_isSharedCheck_3432_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_result_3391_);
lean_dec(v_a_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3432_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3395_ = lean_box(0);
lean_inc_ref(v_name_3382_);
v___x_3396_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3382_, v___x_3395_, v_visited_3378_);
v___x_3397_ = lean_unsigned_to_nat(1u);
v___x_3398_ = lean_nat_add(v_requestNo_3376_, v___x_3397_);
lean_dec(v_requestNo_3376_);
v___x_3399_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 1, v___x_3399_);
lean_ctor_set(v___x_3393_, 0, v___x_3398_);
v___x_3401_ = v___x_3393_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
size_t v_sz_3402_; size_t v___x_3403_; lean_object* v___x_3404_; 
v_sz_3402_ = lean_array_size(v_result_3391_);
v___x_3403_ = ((size_t)0ULL);
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___x_3396_, v_result_3391_, v_sz_3402_, v___x_3403_, v___x_3401_, v_a_3379_);
lean_dec(v_result_3391_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3422_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3422_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3422_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v_fst_3409_; lean_object* v_snd_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3421_; 
v_fst_3409_ = lean_ctor_get(v_a_3405_, 0);
v_snd_3410_ = lean_ctor_get(v_a_3405_, 1);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_a_3405_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3412_ = v_a_3405_;
v_isShared_3413_ = v_isSharedCheck_3421_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_snd_3410_);
lean_inc(v_fst_3409_);
lean_dec(v_a_3405_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3421_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
v___x_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3414_, 0, v_item_3377_);
lean_ctor_set(v___x_3414_, 1, v_snd_3410_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 1, v_fst_3409_);
lean_ctor_set(v___x_3412_, 0, v___x_3414_);
v___x_3416_ = v___x_3412_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_fst_3409_);
v___x_3416_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
lean_object* v___x_3418_; 
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3416_);
v___x_3418_ = v___x_3407_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v_item_3377_);
v_a_3423_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3404_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3404_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec(v_visited_3378_);
lean_dec_ref(v_item_3377_);
lean_dec(v_requestNo_3376_);
v_a_3434_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3389_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3389_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec_ref_known(v___x_3385_, 1);
lean_dec(v_visited_3378_);
lean_dec_ref(v_item_3377_);
lean_dec(v_requestNo_3376_);
v_a_3442_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3388_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3388_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_dec(v_visited_3378_);
v___x_3450_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3451_, 0, v_item_3377_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_ctor_set(v___x_3452_, 1, v_requestNo_3376_);
v___x_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
return v___x_3453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(lean_object* v___x_3454_, lean_object* v_as_3455_, size_t v_sz_3456_, size_t v_i_3457_, lean_object* v_b_3458_, lean_object* v___y_3459_){
_start:
{
uint8_t v___x_3461_; 
v___x_3461_ = lean_usize_dec_lt(v_i_3457_, v_sz_3456_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; 
lean_dec(v___x_3454_);
v___x_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3462_, 0, v_b_3458_);
return v___x_3462_;
}
else
{
lean_object* v_fst_3463_; lean_object* v_snd_3464_; lean_object* v_a_3465_; lean_object* v___x_3466_; 
v_fst_3463_ = lean_ctor_get(v_b_3458_, 0);
lean_inc(v_fst_3463_);
v_snd_3464_ = lean_ctor_get(v_b_3458_, 1);
lean_inc(v_snd_3464_);
lean_dec_ref(v_b_3458_);
v_a_3465_ = lean_array_uget_borrowed(v_as_3455_, v_i_3457_);
lean_inc(v___x_3454_);
lean_inc(v_a_3465_);
v___x_3466_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_fst_3463_, v_a_3465_, v___x_3454_, v___y_3459_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v_fst_3468_; lean_object* v_snd_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3480_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3467_);
lean_dec_ref_known(v___x_3466_, 1);
v_fst_3468_ = lean_ctor_get(v_a_3467_, 0);
v_snd_3469_ = lean_ctor_get(v_a_3467_, 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_a_3467_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3471_ = v_a_3467_;
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_snd_3469_);
lean_inc(v_fst_3468_);
lean_dec(v_a_3467_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3473_ = lean_array_push(v_snd_3464_, v_fst_3468_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 1, v___x_3473_);
lean_ctor_set(v___x_3471_, 0, v_snd_3469_);
v___x_3475_ = v___x_3471_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_snd_3469_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v___x_3473_);
v___x_3475_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
size_t v___x_3476_; size_t v___x_3477_; 
v___x_3476_ = ((size_t)1ULL);
v___x_3477_ = lean_usize_add(v_i_3457_, v___x_3476_);
v_i_3457_ = v___x_3477_;
v_b_3458_ = v___x_3475_;
goto _start;
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec(v_snd_3464_);
lean_dec(v___x_3454_);
v_a_3481_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3466_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3466_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2___boxed(lean_object* v___x_3489_, lean_object* v_as_3490_, lean_object* v_sz_3491_, lean_object* v_i_3492_, lean_object* v_b_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
size_t v_sz_boxed_3496_; size_t v_i_boxed_3497_; lean_object* v_res_3498_; 
v_sz_boxed_3496_ = lean_unbox_usize(v_sz_3491_);
lean_dec(v_sz_3491_);
v_i_boxed_3497_ = lean_unbox_usize(v_i_3492_);
lean_dec(v_i_3492_);
v_res_3498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___x_3489_, v_as_3490_, v_sz_boxed_3496_, v_i_boxed_3497_, v_b_3493_, v___y_3494_);
lean_dec_ref(v___y_3494_);
lean_dec_ref(v_as_3490_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___boxed(lean_object* v_requestNo_3499_, lean_object* v_item_3500_, lean_object* v_visited_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_requestNo_3499_, v_item_3500_, v_visited_3501_, v_a_3502_);
lean_dec_ref(v_a_3502_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(lean_object* v_v_3505_){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(v_v_3505_);
v___x_3507_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(lean_object* v_h_3508_, lean_object* v_r_3509_){
_start:
{
lean_object* v_id_3511_; lean_object* v_method_3512_; lean_object* v_param_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3533_; 
v_id_3511_ = lean_ctor_get(v_r_3509_, 0);
v_method_3512_ = lean_ctor_get(v_r_3509_, 1);
v_param_3513_ = lean_ctor_get(v_r_3509_, 2);
v_isSharedCheck_3533_ = !lean_is_exclusive(v_r_3509_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3515_ = v_r_3509_;
v_isShared_3516_ = v_isSharedCheck_3533_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_param_3513_);
lean_inc(v_method_3512_);
lean_inc(v_id_3511_);
lean_dec(v_r_3509_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3533_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___y_3518_; lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(v_param_3513_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v___x_3524_; 
lean_dec_ref_known(v___x_3523_, 1);
v___x_3524_ = lean_box(0);
v___y_3518_ = v___x_3524_;
goto v___jp_3517_;
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
v_a_3525_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3523_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3523_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
v___y_3518_ = v___x_3530_;
goto v___jp_3517_;
}
}
}
v___jp_3517_:
{
lean_object* v___x_3520_; 
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 2, v___y_3518_);
v___x_3520_ = v___x_3515_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_id_3511_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_method_3512_);
lean_ctor_set(v_reuseFailAlloc_3522_, 2, v___y_3518_);
v___x_3520_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_3508_, v___x_3520_);
return v___x_3521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0___boxed(lean_object* v_h_3534_, lean_object* v_r_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_h_3534_, v_r_3535_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(lean_object* v_r_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v___x_3541_; lean_object* v_a_3542_; lean_object* v___x_3543_; 
v___x_3541_ = l_Lean_Lsp_Ipc_stdin(v_a_3539_);
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref(v___x_3541_);
v___x_3543_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_a_3542_, v_r_3538_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0___boxed(lean_object* v_r_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v_r_3544_, v_a_3545_);
lean_dec_ref(v_a_3545_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(lean_object* v_x_3550_){
_start:
{
if (lean_obj_tag(v_x_3550_) == 0)
{
lean_object* v___x_3551_; 
v___x_3551_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0));
return v___x_3551_;
}
else
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v_x_3550_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3569_; 
v_a_3561_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3563_ = v___x_3552_;
v_isShared_3564_ = v_isSharedCheck_3569_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3552_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3569_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3565_; lean_object* v___x_3567_; 
v___x_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3565_, 0, v_a_3561_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 0, v___x_3565_);
v___x_3567_ = v___x_3563_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(lean_object* v_expectedID_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_Lsp_Ipc_stdout(v_a_3571_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3717_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3576_ = v___x_3573_;
v_isShared_3577_ = v_isSharedCheck_3717_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3573_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3717_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_IO_FS_Stream_readLspMessage(v_a_3574_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3708_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3581_ = v___x_3578_;
v_isShared_3582_ = v_isSharedCheck_3708_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3578_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3708_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___y_3584_; lean_object* v___y_3585_; 
switch(lean_obj_tag(v_a_3579_))
{
case 2:
{
lean_object* v_id_3591_; lean_object* v_result_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3636_; 
v_id_3591_ = lean_ctor_get(v_a_3579_, 0);
v_result_3592_ = lean_ctor_get(v_a_3579_, 1);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_a_3579_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3594_ = v_a_3579_;
v_isShared_3595_ = v_isSharedCheck_3636_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_result_3592_);
lean_inc(v_id_3591_);
lean_dec(v_a_3579_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3636_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
uint8_t v___x_3596_; 
v___x_3596_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3591_, v_expectedID_3570_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; lean_object* v___y_3599_; 
lean_del_object(v___x_3594_);
lean_dec(v_result_3592_);
lean_del_object(v___x_3576_);
v___x_3597_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4));
switch(lean_obj_tag(v_expectedID_3570_))
{
case 0:
{
lean_object* v_s_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v_s_3610_ = lean_ctor_get(v_expectedID_3570_, 0);
lean_inc_ref(v_s_3610_);
lean_dec_ref_known(v_expectedID_3570_, 1);
v___x_3611_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_3612_ = lean_string_append(v___x_3611_, v_s_3610_);
lean_dec_ref(v_s_3610_);
v___x_3613_ = lean_string_append(v___x_3612_, v___x_3611_);
v___y_3599_ = v___x_3613_;
goto v___jp_3598_;
}
case 1:
{
lean_object* v_n_3614_; lean_object* v___x_3615_; 
v_n_3614_ = lean_ctor_get(v_expectedID_3570_, 0);
lean_inc_ref(v_n_3614_);
lean_dec_ref_known(v_expectedID_3570_, 1);
v___x_3615_ = l_Lean_JsonNumber_toString(v_n_3614_);
v___y_3599_ = v___x_3615_;
goto v___jp_3598_;
}
default: 
{
lean_object* v___x_3616_; 
v___x_3616_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_3599_ = v___x_3616_;
goto v___jp_3598_;
}
}
v___jp_3598_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = lean_string_append(v___x_3597_, v___y_3599_);
lean_dec_ref(v___y_3599_);
v___x_3601_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5));
v___x_3602_ = lean_string_append(v___x_3600_, v___x_3601_);
switch(lean_obj_tag(v_id_3591_))
{
case 0:
{
lean_object* v_s_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v_s_3603_ = lean_ctor_get(v_id_3591_, 0);
lean_inc_ref(v_s_3603_);
lean_dec_ref_known(v_id_3591_, 1);
v___x_3604_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_3605_ = lean_string_append(v___x_3604_, v_s_3603_);
lean_dec_ref(v_s_3603_);
v___x_3606_ = lean_string_append(v___x_3605_, v___x_3604_);
v___y_3584_ = v___x_3602_;
v___y_3585_ = v___x_3606_;
goto v___jp_3583_;
}
case 1:
{
lean_object* v_n_3607_; lean_object* v___x_3608_; 
v_n_3607_ = lean_ctor_get(v_id_3591_, 0);
lean_inc_ref(v_n_3607_);
lean_dec_ref_known(v_id_3591_, 1);
v___x_3608_ = l_Lean_JsonNumber_toString(v_n_3607_);
v___y_3584_ = v___x_3602_;
v___y_3585_ = v___x_3608_;
goto v___jp_3583_;
}
default: 
{
lean_object* v___x_3609_; 
v___x_3609_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___y_3584_ = v___x_3602_;
v___y_3585_ = v___x_3609_;
goto v___jp_3583_;
}
}
}
}
else
{
lean_object* v___x_3617_; 
lean_dec(v_id_3591_);
lean_del_object(v___x_3581_);
lean_inc(v_result_3592_);
v___x_3617_ = l_Lean_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(v_result_3592_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3627_; 
lean_del_object(v___x_3594_);
lean_dec(v_expectedID_3570_);
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
v___x_3619_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3620_ = l_Lean_Json_compress(v_result_3592_);
v___x_3621_ = lean_string_append(v___x_3619_, v___x_3620_);
lean_dec_ref(v___x_3620_);
v___x_3622_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3623_ = lean_string_append(v___x_3621_, v___x_3622_);
v___x_3624_ = lean_string_append(v___x_3623_, v_a_3618_);
lean_dec(v_a_3618_);
v___x_3625_ = lean_mk_io_user_error(v___x_3624_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set_tag(v___x_3576_, 1);
lean_ctor_set(v___x_3576_, 0, v___x_3625_);
v___x_3627_ = v___x_3576_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3625_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; 
lean_dec(v_result_3592_);
v_a_3629_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3617_, 1);
if (v_isShared_3595_ == 0)
{
lean_ctor_set_tag(v___x_3594_, 0);
lean_ctor_set(v___x_3594_, 1, v_a_3629_);
lean_ctor_set(v___x_3594_, 0, v_expectedID_3570_);
v___x_3631_ = v___x_3594_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_expectedID_3570_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_a_3629_);
v___x_3631_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3633_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 0, v___x_3631_);
v___x_3633_ = v___x_3576_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3637_; uint8_t v_code_3638_; lean_object* v_message_3639_; lean_object* v_data_x3f_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___x_3672_; lean_object* v___y_3674_; 
lean_del_object(v___x_3581_);
lean_dec(v_expectedID_3570_);
v_id_3637_ = lean_ctor_get(v_a_3579_, 0);
lean_inc(v_id_3637_);
v_code_3638_ = lean_ctor_get_uint8(v_a_3579_, sizeof(void*)*3);
v_message_3639_ = lean_ctor_get(v_a_3579_, 1);
lean_inc_ref(v_message_3639_);
v_data_x3f_3640_ = lean_ctor_get(v_a_3579_, 2);
lean_inc(v_data_x3f_3640_);
lean_dec_ref_known(v_a_3579_, 3);
v___x_3641_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3642_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3672_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3637_))
{
case 0:
{
lean_object* v_s_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
v_s_3690_ = lean_ctor_get(v_id_3637_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_id_3637_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v_id_3637_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_s_3690_);
lean_dec(v_id_3637_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
lean_ctor_set_tag(v___x_3692_, 3);
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_s_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
v___y_3674_ = v___x_3695_;
goto v___jp_3673_;
}
}
}
case 1:
{
lean_object* v_n_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
v_n_3698_ = lean_ctor_get(v_id_3637_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_id_3637_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v_id_3637_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_n_3698_);
lean_dec(v_id_3637_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
lean_ctor_set_tag(v___x_3700_, 2);
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_n_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
v___y_3674_ = v___x_3703_;
goto v___jp_3673_;
}
}
}
default: 
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_box(0);
v___y_3674_ = v___x_3706_;
goto v___jp_3673_;
}
}
v___jp_3643_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
lean_inc(v___y_3647_);
lean_inc_ref(v___y_3646_);
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___y_3646_);
lean_ctor_set(v___x_3648_, 1, v___y_3647_);
v___x_3649_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3650_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3650_, 0, v_message_3639_);
v___x_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = lean_box(0);
v___x_3653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3651_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3648_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3656_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3655_, v_data_x3f_3640_);
lean_dec(v_data_x3f_3640_);
v___x_3657_ = l_List_appendTR___redArg(v___x_3654_, v___x_3656_);
v___x_3658_ = l_Lean_Json_mkObj(v___x_3657_);
lean_dec(v___x_3657_);
lean_inc_ref(v___y_3645_);
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___y_3645_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
lean_ctor_set(v___x_3660_, 1, v___x_3652_);
v___x_3661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___y_3644_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3642_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = l_Lean_Json_mkObj(v___x_3662_);
lean_dec_ref_known(v___x_3662_, 2);
v___x_3664_ = l_Lean_Json_compress(v___x_3663_);
v___x_3665_ = lean_string_append(v___x_3641_, v___x_3664_);
lean_dec_ref(v___x_3664_);
v___x_3666_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3667_ = lean_string_append(v___x_3665_, v___x_3666_);
v___x_3668_ = lean_mk_io_user_error(v___x_3667_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set_tag(v___x_3576_, 1);
lean_ctor_set(v___x_3576_, 0, v___x_3668_);
v___x_3670_ = v___x_3576_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
v___jp_3673_:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3672_);
lean_ctor_set(v___x_3675_, 1, v___y_3674_);
v___x_3676_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3677_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3638_)
{
case 0:
{
lean_object* v___x_3678_; 
v___x_3678_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3678_;
goto v___jp_3643_;
}
case 1:
{
lean_object* v___x_3679_; 
v___x_3679_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3679_;
goto v___jp_3643_;
}
case 2:
{
lean_object* v___x_3680_; 
v___x_3680_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3680_;
goto v___jp_3643_;
}
case 3:
{
lean_object* v___x_3681_; 
v___x_3681_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3681_;
goto v___jp_3643_;
}
case 4:
{
lean_object* v___x_3682_; 
v___x_3682_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3682_;
goto v___jp_3643_;
}
case 5:
{
lean_object* v___x_3683_; 
v___x_3683_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3683_;
goto v___jp_3643_;
}
case 6:
{
lean_object* v___x_3684_; 
v___x_3684_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3684_;
goto v___jp_3643_;
}
case 7:
{
lean_object* v___x_3685_; 
v___x_3685_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3685_;
goto v___jp_3643_;
}
case 8:
{
lean_object* v___x_3686_; 
v___x_3686_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3686_;
goto v___jp_3643_;
}
case 9:
{
lean_object* v___x_3687_; 
v___x_3687_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3687_;
goto v___jp_3643_;
}
case 10:
{
lean_object* v___x_3688_; 
v___x_3688_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3688_;
goto v___jp_3643_;
}
default: 
{
lean_object* v___x_3689_; 
v___x_3689_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3644_ = v___x_3675_;
v___y_3645_ = v___x_3676_;
v___y_3646_ = v___x_3677_;
v___y_3647_ = v___x_3689_;
goto v___jp_3643_;
}
}
}
}
default: 
{
lean_del_object(v___x_3581_);
lean_dec(v_a_3579_);
lean_del_object(v___x_3576_);
goto _start;
}
}
v___jp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3586_ = lean_string_append(v___y_3584_, v___y_3585_);
lean_dec_ref(v___y_3585_);
v___x_3587_ = lean_mk_io_user_error(v___x_3586_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set_tag(v___x_3581_, 1);
lean_ctor_set(v___x_3581_, 0, v___x_3587_);
v___x_3589_ = v___x_3581_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_del_object(v___x_3576_);
lean_dec(v_expectedID_3570_);
v_a_3709_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3578_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3578_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec(v_expectedID_3570_);
v_a_3718_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3573_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3573_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1___boxed(lean_object* v_expectedID_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v_expectedID_3726_, v_a_3727_);
lean_dec_ref(v_a_3727_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports(lean_object* v_requestNo_3734_, lean_object* v_uri_3735_, lean_object* v_a_3736_){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_inc(v_requestNo_3734_);
v___x_3738_ = l_Lean_JsonNumber_fromNat(v_requestNo_3734_);
v___x_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
v___x_3740_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_3739_);
v___x_3741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
lean_ctor_set(v___x_3741_, 2, v_uri_3735_);
v___x_3742_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_3741_, v_a_3736_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v___x_3743_; 
lean_dec_ref_known(v___x_3742_, 1);
v___x_3743_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_3739_, v_a_3736_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3802_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3746_ = v___x_3743_;
v_isShared_3747_ = v_isSharedCheck_3802_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3743_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3802_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v_result_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3800_; 
v_result_3748_ = lean_ctor_get(v_a_3744_, 1);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_a_3744_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; 
v_unused_3801_ = lean_ctor_get(v_a_3744_, 0);
lean_dec(v_unused_3801_);
v___x_3750_ = v_a_3744_;
v_isShared_3751_ = v_isSharedCheck_3800_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_result_3748_);
lean_dec(v_a_3744_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3800_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_unsigned_to_nat(1u);
v___x_3753_ = lean_nat_add(v_requestNo_3734_, v___x_3752_);
lean_dec(v_requestNo_3734_);
if (lean_obj_tag(v_result_3748_) == 1)
{
lean_object* v_val_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3792_; 
lean_del_object(v___x_3746_);
v_val_3754_ = lean_ctor_get(v_result_3748_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v_result_3748_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3756_ = v_result_3748_;
v_isShared_3757_ = v_isSharedCheck_3792_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_val_3754_);
lean_dec(v_result_3748_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3792_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3758_; lean_object* v___x_3760_; 
v___x_3758_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v___x_3758_);
lean_ctor_set(v___x_3750_, 0, v_val_3754_);
v___x_3760_ = v___x_3750_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_val_3754_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3761_ = lean_box(1);
v___x_3762_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v___x_3753_, v___x_3760_, v___x_3761_, v_a_3736_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3782_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3765_ = v___x_3762_;
v_isShared_3766_ = v_isSharedCheck_3782_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3762_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3782_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v_fst_3767_; lean_object* v_snd_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3781_; 
v_fst_3767_ = lean_ctor_get(v_a_3763_, 0);
v_snd_3768_ = lean_ctor_get(v_a_3763_, 1);
v_isSharedCheck_3781_ = !lean_is_exclusive(v_a_3763_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3770_ = v_a_3763_;
v_isShared_3771_ = v_isSharedCheck_3781_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_snd_3768_);
lean_inc(v_fst_3767_);
lean_dec(v_a_3763_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3781_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 0, v_fst_3767_);
v___x_3773_ = v___x_3756_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_fst_3767_);
v___x_3773_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3775_; 
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 0, v___x_3773_);
v___x_3775_ = v___x_3770_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3773_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_snd_3768_);
v___x_3775_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3777_; 
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3775_);
v___x_3777_ = v___x_3765_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3775_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_del_object(v___x_3756_);
v_a_3783_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3762_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3762_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
}
else
{
lean_object* v___x_3793_; lean_object* v___x_3795_; 
lean_dec(v_result_3748_);
v___x_3793_ = lean_box(0);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v___x_3753_);
lean_ctor_set(v___x_3750_, 0, v___x_3793_);
v___x_3795_ = v___x_3750_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3793_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v___x_3753_);
v___x_3795_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3797_; 
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 0, v___x_3795_);
v___x_3797_ = v___x_3746_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec(v_requestNo_3734_);
v_a_3803_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3743_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3743_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref_known(v___x_3739_, 1);
lean_dec(v_requestNo_3734_);
v_a_3811_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3742_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3742_);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___boxed(lean_object* v_requestNo_3819_, lean_object* v_uri_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImports(v_requestNo_3819_, v_uri_3820_, v_a_3821_);
lean_dec_ref(v_a_3821_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(lean_object* v_v_3824_){
_start:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3825_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_v_3824_);
v___x_3826_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3825_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_v_3827_);
lean_dec_ref(v_v_3827_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(lean_object* v_h_3829_, lean_object* v_r_3830_){
_start:
{
lean_object* v_id_3832_; lean_object* v_method_3833_; lean_object* v_param_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3854_; 
v_id_3832_ = lean_ctor_get(v_r_3830_, 0);
v_method_3833_ = lean_ctor_get(v_r_3830_, 1);
v_param_3834_ = lean_ctor_get(v_r_3830_, 2);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_r_3830_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3836_ = v_r_3830_;
v_isShared_3837_ = v_isSharedCheck_3854_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_param_3834_);
lean_inc(v_method_3833_);
lean_inc(v_id_3832_);
lean_dec(v_r_3830_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3854_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___y_3839_; lean_object* v___x_3844_; 
v___x_3844_ = l_Lean_Json_toStructured_x3f___at___00Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_param_3834_);
lean_dec(v_param_3834_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v___x_3845_; 
lean_dec_ref_known(v___x_3844_, 1);
v___x_3845_ = lean_box(0);
v___y_3839_ = v___x_3845_;
goto v___jp_3838_;
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
v_a_3846_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3844_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3844_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
v___y_3839_ = v___x_3851_;
goto v___jp_3838_;
}
}
}
v___jp_3838_:
{
lean_object* v___x_3841_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 2, v___y_3839_);
v___x_3841_ = v___x_3836_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_id_3832_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_method_3833_);
lean_ctor_set(v_reuseFailAlloc_3843_, 2, v___y_3839_);
v___x_3841_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
lean_object* v___x_3842_; 
v___x_3842_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_3829_, v___x_3841_);
return v___x_3842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0___boxed(lean_object* v_h_3855_, lean_object* v_r_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_h_3855_, v_r_3856_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(lean_object* v_r_3859_, lean_object* v_a_3860_){
_start:
{
lean_object* v___x_3862_; lean_object* v_a_3863_; lean_object* v___x_3864_; 
v___x_3862_ = l_Lean_Lsp_Ipc_stdin(v_a_3860_);
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref(v___x_3862_);
v___x_3864_ = l_Lean_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_a_3863_, v_r_3859_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0___boxed(lean_object* v_r_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v_r_3865_, v_a_3866_);
lean_dec_ref(v_a_3866_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(lean_object* v_requestNo_3870_, lean_object* v_item_3871_, lean_object* v_visited_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v_module_3875_; lean_object* v_name_3876_; uint8_t v___x_3877_; 
v_module_3875_ = lean_ctor_get(v_item_3871_, 0);
v_name_3876_ = lean_ctor_get(v_module_3875_, 0);
v___x_3877_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3876_, v_visited_3872_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
lean_inc(v_requestNo_3870_);
v___x_3878_ = l_Lean_JsonNumber_fromNat(v_requestNo_3870_);
v___x_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
v___x_3880_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0));
lean_inc_ref(v_module_3875_);
lean_inc_ref(v___x_3879_);
v___x_3881_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
lean_ctor_set(v___x_3881_, 2, v_module_3875_);
v___x_3882_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v___x_3881_, v_a_3873_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v___x_3883_; 
lean_dec_ref_known(v___x_3882_, 1);
v___x_3883_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3879_, v_a_3873_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v_result_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3926_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
v_result_3885_ = lean_ctor_get(v_a_3884_, 1);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_a_3884_);
if (v_isSharedCheck_3926_ == 0)
{
lean_object* v_unused_3927_; 
v_unused_3927_ = lean_ctor_get(v_a_3884_, 0);
lean_dec(v_unused_3927_);
v___x_3887_ = v_a_3884_;
v_isShared_3888_ = v_isSharedCheck_3926_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_result_3885_);
lean_dec(v_a_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3926_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3889_ = lean_box(0);
lean_inc_ref(v_name_3876_);
v___x_3890_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3876_, v___x_3889_, v_visited_3872_);
v___x_3891_ = lean_unsigned_to_nat(1u);
v___x_3892_ = lean_nat_add(v_requestNo_3870_, v___x_3891_);
lean_dec(v_requestNo_3870_);
v___x_3893_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 1, v___x_3893_);
lean_ctor_set(v___x_3887_, 0, v___x_3892_);
v___x_3895_ = v___x_3887_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3892_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
size_t v_sz_3896_; size_t v___x_3897_; lean_object* v___x_3898_; 
v_sz_3896_ = lean_array_size(v_result_3885_);
v___x_3897_ = ((size_t)0ULL);
v___x_3898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___x_3890_, v_result_3885_, v_sz_3896_, v___x_3897_, v___x_3895_, v_a_3873_);
lean_dec(v_result_3885_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3916_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3901_ = v___x_3898_;
v_isShared_3902_ = v_isSharedCheck_3916_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3916_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v_fst_3903_; lean_object* v_snd_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3915_; 
v_fst_3903_ = lean_ctor_get(v_a_3899_, 0);
v_snd_3904_ = lean_ctor_get(v_a_3899_, 1);
v_isSharedCheck_3915_ = !lean_is_exclusive(v_a_3899_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3906_ = v_a_3899_;
v_isShared_3907_ = v_isSharedCheck_3915_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_snd_3904_);
lean_inc(v_fst_3903_);
lean_dec(v_a_3899_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3915_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3908_; lean_object* v___x_3910_; 
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v_item_3871_);
lean_ctor_set(v___x_3908_, 1, v_snd_3904_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 1, v_fst_3903_);
lean_ctor_set(v___x_3906_, 0, v___x_3908_);
v___x_3910_ = v___x_3906_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v_fst_3903_);
v___x_3910_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
lean_object* v___x_3912_; 
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3910_);
v___x_3912_ = v___x_3901_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_dec_ref(v_item_3871_);
v_a_3917_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3898_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3898_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec(v_visited_3872_);
lean_dec_ref(v_item_3871_);
lean_dec(v_requestNo_3870_);
v_a_3928_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3883_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3883_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec_ref_known(v___x_3879_, 1);
lean_dec(v_visited_3872_);
lean_dec_ref(v_item_3871_);
lean_dec(v_requestNo_3870_);
v_a_3936_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3882_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3882_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
lean_dec(v_visited_3872_);
v___x_3944_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3945_, 0, v_item_3871_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
lean_ctor_set(v___x_3946_, 1, v_requestNo_3870_);
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
return v___x_3947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(lean_object* v___x_3948_, lean_object* v_as_3949_, size_t v_sz_3950_, size_t v_i_3951_, lean_object* v_b_3952_, lean_object* v___y_3953_){
_start:
{
uint8_t v___x_3955_; 
v___x_3955_ = lean_usize_dec_lt(v_i_3951_, v_sz_3950_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
lean_dec(v___x_3948_);
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v_b_3952_);
return v___x_3956_;
}
else
{
lean_object* v_fst_3957_; lean_object* v_snd_3958_; lean_object* v_a_3959_; lean_object* v___x_3960_; 
v_fst_3957_ = lean_ctor_get(v_b_3952_, 0);
lean_inc(v_fst_3957_);
v_snd_3958_ = lean_ctor_get(v_b_3952_, 1);
lean_inc(v_snd_3958_);
lean_dec_ref(v_b_3952_);
v_a_3959_ = lean_array_uget_borrowed(v_as_3949_, v_i_3951_);
lean_inc(v___x_3948_);
lean_inc(v_a_3959_);
v___x_3960_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_fst_3957_, v_a_3959_, v___x_3948_, v___y_3953_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v_fst_3962_; lean_object* v_snd_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3974_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref_known(v___x_3960_, 1);
v_fst_3962_ = lean_ctor_get(v_a_3961_, 0);
v_snd_3963_ = lean_ctor_get(v_a_3961_, 1);
v_isSharedCheck_3974_ = !lean_is_exclusive(v_a_3961_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3965_ = v_a_3961_;
v_isShared_3966_ = v_isSharedCheck_3974_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_snd_3963_);
lean_inc(v_fst_3962_);
lean_dec(v_a_3961_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3974_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3967_ = lean_array_push(v_snd_3958_, v_fst_3962_);
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 1, v___x_3967_);
lean_ctor_set(v___x_3965_, 0, v_snd_3963_);
v___x_3969_ = v___x_3965_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_snd_3963_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
size_t v___x_3970_; size_t v___x_3971_; 
v___x_3970_ = ((size_t)1ULL);
v___x_3971_ = lean_usize_add(v_i_3951_, v___x_3970_);
v_i_3951_ = v___x_3971_;
v_b_3952_ = v___x_3969_;
goto _start;
}
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v_snd_3958_);
lean_dec(v___x_3948_);
v_a_3975_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3960_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3960_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1___boxed(lean_object* v___x_3983_, lean_object* v_as_3984_, lean_object* v_sz_3985_, lean_object* v_i_3986_, lean_object* v_b_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
size_t v_sz_boxed_3990_; size_t v_i_boxed_3991_; lean_object* v_res_3992_; 
v_sz_boxed_3990_ = lean_unbox_usize(v_sz_3985_);
lean_dec(v_sz_3985_);
v_i_boxed_3991_ = lean_unbox_usize(v_i_3986_);
lean_dec(v_i_3986_);
v_res_3992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___x_3983_, v_as_3984_, v_sz_boxed_3990_, v_i_boxed_3991_, v_b_3987_, v___y_3988_);
lean_dec_ref(v___y_3988_);
lean_dec_ref(v_as_3984_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___boxed(lean_object* v_requestNo_3993_, lean_object* v_item_3994_, lean_object* v_visited_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_requestNo_3993_, v_item_3994_, v_visited_3995_, v_a_3996_);
lean_dec_ref(v_a_3996_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(lean_object* v_requestNo_3999_, lean_object* v_uri_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
lean_inc(v_requestNo_3999_);
v___x_4003_ = l_Lean_JsonNumber_fromNat(v_requestNo_3999_);
v___x_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
v___x_4005_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_4004_);
v___x_4006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4004_);
lean_ctor_set(v___x_4006_, 1, v___x_4005_);
lean_ctor_set(v___x_4006_, 2, v_uri_4000_);
v___x_4007_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_4006_, v_a_4001_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v___x_4008_; 
lean_dec_ref_known(v___x_4007_, 1);
v___x_4008_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_4004_, v_a_4001_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4067_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4011_ = v___x_4008_;
v_isShared_4012_ = v_isSharedCheck_4067_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_4008_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4067_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v_result_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4065_; 
v_result_4013_ = lean_ctor_get(v_a_4009_, 1);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_a_4009_);
if (v_isSharedCheck_4065_ == 0)
{
lean_object* v_unused_4066_; 
v_unused_4066_ = lean_ctor_get(v_a_4009_, 0);
lean_dec(v_unused_4066_);
v___x_4015_ = v_a_4009_;
v_isShared_4016_ = v_isSharedCheck_4065_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_result_4013_);
lean_dec(v_a_4009_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4065_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4017_ = lean_unsigned_to_nat(1u);
v___x_4018_ = lean_nat_add(v_requestNo_3999_, v___x_4017_);
lean_dec(v_requestNo_3999_);
if (lean_obj_tag(v_result_4013_) == 1)
{
lean_object* v_val_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4057_; 
lean_del_object(v___x_4011_);
v_val_4019_ = lean_ctor_get(v_result_4013_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v_result_4013_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4021_ = v_result_4013_;
v_isShared_4022_ = v_isSharedCheck_4057_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_val_4019_);
lean_dec(v_result_4013_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4057_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4023_; lean_object* v___x_4025_; 
v___x_4023_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 1, v___x_4023_);
lean_ctor_set(v___x_4015_, 0, v_val_4019_);
v___x_4025_ = v___x_4015_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_val_4019_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v___x_4023_);
v___x_4025_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4026_ = lean_box(1);
v___x_4027_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v___x_4018_, v___x_4025_, v___x_4026_, v_a_4001_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4047_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4047_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4047_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v_fst_4032_; lean_object* v_snd_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4046_; 
v_fst_4032_ = lean_ctor_get(v_a_4028_, 0);
v_snd_4033_ = lean_ctor_get(v_a_4028_, 1);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_a_4028_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4035_ = v_a_4028_;
v_isShared_4036_ = v_isSharedCheck_4046_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_snd_4033_);
lean_inc(v_fst_4032_);
lean_dec(v_a_4028_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4046_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v_fst_4032_);
v___x_4038_ = v___x_4021_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_fst_4032_);
v___x_4038_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
lean_object* v___x_4040_; 
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4038_);
v___x_4040_ = v___x_4035_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_snd_4033_);
v___x_4040_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
lean_object* v___x_4042_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 0, v___x_4040_);
v___x_4042_ = v___x_4030_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4040_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
}
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_del_object(v___x_4021_);
v_a_4048_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4027_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4027_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
}
else
{
lean_object* v___x_4058_; lean_object* v___x_4060_; 
lean_dec(v_result_4013_);
v___x_4058_ = lean_box(0);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 1, v___x_4018_);
lean_ctor_set(v___x_4015_, 0, v___x_4058_);
v___x_4060_ = v___x_4015_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v___x_4018_);
v___x_4060_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4062_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v___x_4060_);
v___x_4062_ = v___x_4011_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4060_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
}
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
lean_dec(v_requestNo_3999_);
v_a_4068_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4008_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4008_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec_ref_known(v___x_4004_, 1);
lean_dec(v_requestNo_3999_);
v_a_4076_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4007_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4007_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy___boxed(lean_object* v_requestNo_4084_, lean_object* v_uri_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(v_requestNo_4084_, v_uri_4085_, v_a_4086_);
lean_dec_ref(v_a_4086_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object* v_lean_4091_, lean_object* v_args_4092_, lean_object* v_test_4093_){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; uint8_t v___x_4098_; uint8_t v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4095_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_4096_ = lean_box(0);
v___x_4097_ = ((lean_object*)(l_Lean_Lsp_Ipc_runWith___redArg___closed__0));
v___x_4098_ = 1;
v___x_4099_ = 0;
v___x_4100_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4100_, 0, v___x_4095_);
lean_ctor_set(v___x_4100_, 1, v_lean_4091_);
lean_ctor_set(v___x_4100_, 2, v_args_4092_);
lean_ctor_set(v___x_4100_, 3, v___x_4096_);
lean_ctor_set(v___x_4100_, 4, v___x_4097_);
lean_ctor_set_uint8(v___x_4100_, sizeof(void*)*5, v___x_4098_);
lean_ctor_set_uint8(v___x_4100_, sizeof(void*)*5 + 1, v___x_4099_);
v___x_4101_ = lean_io_process_spawn(v___x_4100_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4103_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4101_, 1);
v___x_4103_ = lean_apply_2(v_test_4093_, v_a_4102_, lean_box(0));
return v___x_4103_;
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec_ref(v_test_4093_);
v_a_4104_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4101_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4101_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg___boxed(lean_object* v_lean_4112_, lean_object* v_args_4113_, lean_object* v_test_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4112_, v_args_4113_, v_test_4114_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object* v_00_u03b1_4117_, lean_object* v_lean_4118_, lean_object* v_args_4119_, lean_object* v_test_4120_){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4118_, v_args_4119_, v_test_4120_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___boxed(lean_object* v_00_u03b1_4123_, lean_object* v_lean_4124_, lean_object* v_args_4125_, lean_object* v_test_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_Lsp_Ipc_runWith(v_00_u03b1_4123_, v_lean_4124_, v_args_4125_, v_test_4126_);
return v_res_4128_;
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
