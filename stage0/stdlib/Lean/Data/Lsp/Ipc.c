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
uint8_t l_Lean_Json_isNull(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCallHierarchyIncomingCall_fromJson(lean_object*);
lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___00Lean_Lsp_Ipc_shutdown_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Data.Lsp.Ipc"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Lsp.Ipc.shutdown"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "assertion violation: result.isNull\n      "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "exit"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5_value;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_Ipc_shutdown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "shutdown"};
static const lean_object* l_Lean_Lsp_Ipc_shutdown___closed__0 = (const lean_object*)&l_Lean_Lsp_Ipc_shutdown___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object*);
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
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_114_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__2));
v___x_115_ = lean_unsigned_to_nat(6u);
v___x_116_ = lean_unsigned_to_nat(56u);
v___x_117_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__1));
v___x_118_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__0));
v___x_119_ = l_mkPanicMessageWithDecl(v___x_118_, v___x_117_, v___x_116_, v___x_115_, v___x_114_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v___x_130_, lean_object* v_requestNo_131_, lean_object* v___y_132_){
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
lean_dec_ref_known(v_a_135_, 2);
v___x_141_ = l_Lean_Json_isNull(v_result_140_);
lean_dec(v_result_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_id_139_);
lean_del_object(v___x_137_);
v___x_142_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__3);
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
lean_dec_ref_known(v_a_144_, 1);
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
lean_dec_ref_known(v_a_144_, 1);
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
v___x_175_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
v___x_176_ = l_Nat_reprFast(v_requestNo_131_);
v___x_177_ = lean_string_append(v___x_175_, v___x_176_);
lean_dec_ref(v___x_176_);
v___x_178_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_179_ = lean_string_append(v___x_177_, v___x_178_);
switch(lean_obj_tag(v_id_139_))
{
case 0:
{
lean_object* v_s_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_s_187_ = lean_ctor_get(v_id_139_, 0);
lean_inc_ref(v_s_187_);
lean_dec_ref_known(v_id_139_, 1);
v___x_188_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
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
lean_dec_ref_known(v_id_139_, 1);
v___x_192_ = l_Lean_JsonNumber_toString(v_n_191_);
v___y_181_ = v___x_192_;
goto v___jp_180_;
}
default: 
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
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
v___x_164_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__5));
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___boxed(lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v___x_206_, lean_object* v_requestNo_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_204_, v_a_205_, v___x_206_, v_requestNo_207_, v___y_208_);
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
lean_dec_ref_known(v___x_226_, 1);
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
lean_dec_ref_known(v___x_258_, 1);
v___x_259_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_246_, v_a_248_, v___x_254_, v_requestNo_242_, v_a_243_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v___x_279_, lean_object* v_requestNo_280_, lean_object* v_inst_281_, lean_object* v_a_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg(v_a_277_, v_a_278_, v___x_279_, v_requestNo_280_, v___y_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___boxed(lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v___x_288_, lean_object* v_requestNo_289_, lean_object* v_inst_290_, lean_object* v_a_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3(v_a_286_, v_a_287_, v___x_288_, v_requestNo_289_, v_inst_290_, v_a_291_, v___y_292_);
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
v___x_468_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_440_))
{
case 0:
{
lean_object* v_s_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_s_481_ = lean_ctor_get(v_expectedID_440_, 0);
lean_inc_ref(v_s_481_);
lean_dec_ref_known(v_expectedID_440_, 1);
v___x_482_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
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
lean_dec_ref_known(v_expectedID_440_, 1);
v___x_486_ = l_Lean_JsonNumber_toString(v_n_485_);
v___y_470_ = v___x_486_;
goto v___jp_469_;
}
default: 
{
lean_object* v___x_487_; 
v___x_487_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_470_ = v___x_487_;
goto v___jp_469_;
}
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_string_append(v___x_468_, v___y_470_);
lean_dec_ref(v___y_470_);
v___x_472_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_473_ = lean_string_append(v___x_471_, v___x_472_);
switch(lean_obj_tag(v_id_462_))
{
case 0:
{
lean_object* v_s_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_s_474_ = lean_ctor_get(v_id_462_, 0);
lean_inc_ref(v_s_474_);
lean_dec_ref_known(v_id_462_, 1);
v___x_475_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
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
lean_dec_ref_known(v_id_462_, 1);
v___x_479_ = l_Lean_JsonNumber_toString(v_n_478_);
v___y_455_ = v___x_473_;
v___y_456_ = v___x_479_;
goto v___jp_454_;
}
default: 
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
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
lean_dec_ref_known(v___x_488_, 1);
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
lean_dec_ref_known(v___x_488_, 1);
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
lean_dec_ref_known(v_a_450_, 3);
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
lean_dec_ref_known(v___x_534_, 2);
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
v___x_633_ = lean_string_compare(v_message_631_, v_message_632_);
v___y_625_ = v___x_633_;
goto v___jp_624_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed(lean_object* v_d1_634_, lean_object* v_d2_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(v_d1_634_, v_d2_635_);
lean_dec_ref(v_d2_635_);
lean_dec_ref(v_d1_634_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(lean_object* v_p_639_){
_start:
{
lean_object* v_uri_640_; lean_object* v_version_x3f_641_; lean_object* v_isIncremental_x3f_642_; lean_object* v_diagnostics_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_654_; 
v_uri_640_ = lean_ctor_get(v_p_639_, 0);
v_version_x3f_641_ = lean_ctor_get(v_p_639_, 1);
v_isIncremental_x3f_642_ = lean_ctor_get(v_p_639_, 2);
v_diagnostics_643_ = lean_ctor_get(v_p_639_, 3);
v_isSharedCheck_654_ = !lean_is_exclusive(v_p_639_);
if (v_isSharedCheck_654_ == 0)
{
v___x_645_ = v_p_639_;
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_diagnostics_643_);
lean_inc(v_isIncremental_x3f_642_);
lean_inc(v_version_x3f_641_);
lean_inc(v_uri_640_);
lean_dec(v_p_639_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___f_647_; lean_object* v___x_648_; lean_object* v_sorted_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___f_647_ = ((lean_object*)(l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___closed__0));
v___x_648_ = lean_array_to_list(v_diagnostics_643_);
v_sorted_649_ = l_List_mergeSort___redArg(v___x_648_, v___f_647_);
v___x_650_ = lean_array_mk(v_sorted_649_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 3, v___x_650_);
v___x_652_ = v___x_645_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_uri_640_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_version_x3f_641_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_isIncremental_x3f_642_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(lean_object* v_prev_x3f_658_, lean_object* v_next_659_){
_start:
{
lean_object* v_uri_660_; lean_object* v_version_x3f_661_; lean_object* v_isIncremental_x3f_662_; lean_object* v_diagnostics_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_686_; 
v_uri_660_ = lean_ctor_get(v_next_659_, 0);
v_version_x3f_661_ = lean_ctor_get(v_next_659_, 1);
v_isIncremental_x3f_662_ = lean_ctor_get(v_next_659_, 2);
v_diagnostics_663_ = lean_ctor_get(v_next_659_, 3);
v_isSharedCheck_686_ = !lean_is_exclusive(v_next_659_);
if (v_isSharedCheck_686_ == 0)
{
v___x_665_ = v_next_659_;
v_isShared_666_ = v_isSharedCheck_686_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_diagnostics_663_);
lean_inc(v_isIncremental_x3f_662_);
lean_inc(v_version_x3f_661_);
lean_inc(v_uri_660_);
lean_dec(v_next_659_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_686_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v_replace_669_; 
v___x_667_ = ((lean_object*)(l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams___closed__0));
lean_inc_ref(v_diagnostics_663_);
lean_inc(v_version_x3f_661_);
lean_inc_ref(v_uri_660_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 2, v___x_667_);
v_replace_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_uri_660_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_version_x3f_661_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_diagnostics_663_);
v_replace_669_ = v_reuseFailAlloc_685_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
if (lean_obj_tag(v_prev_x3f_658_) == 1)
{
if (lean_obj_tag(v_isIncremental_x3f_662_) == 0)
{
lean_dec_ref_known(v_prev_x3f_658_, 1);
lean_dec_ref(v_diagnostics_663_);
lean_dec(v_version_x3f_661_);
lean_dec_ref(v_uri_660_);
return v_replace_669_;
}
else
{
lean_object* v_val_670_; uint8_t v___x_671_; 
v_val_670_ = lean_ctor_get(v_isIncremental_x3f_662_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v_isIncremental_x3f_662_, 1);
v___x_671_ = lean_unbox(v_val_670_);
lean_dec(v_val_670_);
if (v___x_671_ == 0)
{
lean_dec_ref_known(v_prev_x3f_658_, 1);
lean_dec_ref(v_diagnostics_663_);
lean_dec(v_version_x3f_661_);
lean_dec_ref(v_uri_660_);
return v_replace_669_;
}
else
{
lean_object* v_val_672_; lean_object* v_diagnostics_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v_replace_669_);
v_val_672_ = lean_ctor_get(v_prev_x3f_658_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v_prev_x3f_658_, 1);
v_diagnostics_673_ = lean_ctor_get(v_val_672_, 3);
v_isSharedCheck_681_ = !lean_is_exclusive(v_val_672_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; lean_object* v_unused_683_; lean_object* v_unused_684_; 
v_unused_682_ = lean_ctor_get(v_val_672_, 2);
lean_dec(v_unused_682_);
v_unused_683_ = lean_ctor_get(v_val_672_, 1);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_val_672_, 0);
lean_dec(v_unused_684_);
v___x_675_ = v_val_672_;
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_diagnostics_673_);
lean_dec(v_val_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = l_Array_append___redArg(v_diagnostics_673_, v_diagnostics_663_);
lean_dec_ref(v_diagnostics_663_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 3, v___x_677_);
lean_ctor_set(v___x_675_, 2, v___x_667_);
lean_ctor_set(v___x_675_, 1, v_version_x3f_661_);
lean_ctor_set(v___x_675_, 0, v_uri_660_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_uri_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_version_x3f_661_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
else
{
lean_dec_ref(v_diagnostics_663_);
lean_dec(v_isIncremental_x3f_662_);
lean_dec(v_version_x3f_661_);
lean_dec_ref(v_uri_660_);
lean_dec(v_prev_x3f_658_);
return v_replace_669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object* v_waitForDiagnosticsId_690_, lean_object* v_accumulated_x3f_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Lsp_Ipc_readMessage(v_a_692_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_764_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_764_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_764_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_764_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
switch(lean_obj_tag(v_a_695_))
{
case 2:
{
lean_object* v_id_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_725_; 
v_id_699_ = lean_ctor_get(v_a_695_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_a_695_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v_a_695_, 1);
lean_dec(v_unused_726_);
v___x_701_ = v_a_695_;
v_isShared_702_ = v_isSharedCheck_725_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_id_699_);
lean_dec(v_a_695_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_725_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
uint8_t v___x_703_; 
v___x_703_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_699_, v_waitForDiagnosticsId_690_);
lean_dec(v_id_699_);
if (v___x_703_ == 0)
{
lean_del_object(v___x_701_);
lean_del_object(v___x_697_);
goto _start;
}
else
{
if (lean_obj_tag(v_accumulated_x3f_691_) == 0)
{
lean_object* v___x_705_; lean_object* v___x_707_; 
lean_del_object(v___x_701_);
v___x_705_ = lean_box(0);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_705_);
v___x_707_ = v___x_697_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
else
{
lean_object* v_val_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_724_; 
v_val_709_ = lean_ctor_get(v_accumulated_x3f_691_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_accumulated_x3f_691_);
if (v_isSharedCheck_724_ == 0)
{
v___x_711_ = v_accumulated_x3f_691_;
v_isShared_712_ = v_isSharedCheck_724_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_val_709_);
lean_dec(v_accumulated_x3f_691_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_724_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_714_ = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(v_val_709_);
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 0);
lean_ctor_set(v___x_701_, 1, v___x_714_);
lean_ctor_set(v___x_701_, 0, v___x_713_);
v___x_716_ = v___x_701_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_714_);
v___x_716_ = v_reuseFailAlloc_723_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_716_);
v___x_718_ = v___x_711_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_718_);
v___x_720_ = v___x_697_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
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
lean_object* v_id_727_; lean_object* v_message_728_; uint8_t v___x_729_; 
v_id_727_ = lean_ctor_get(v_a_695_, 0);
lean_inc(v_id_727_);
v_message_728_ = lean_ctor_get(v_a_695_, 1);
lean_inc_ref(v_message_728_);
lean_dec_ref_known(v_a_695_, 3);
v___x_729_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_727_, v_waitForDiagnosticsId_690_);
lean_dec(v_id_727_);
if (v___x_729_ == 0)
{
lean_dec_ref(v_message_728_);
lean_del_object(v___x_697_);
goto _start;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
lean_dec(v_accumulated_x3f_691_);
v___x_731_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1));
v___x_732_ = lean_string_append(v___x_731_, v_message_728_);
lean_dec_ref(v_message_728_);
v___x_733_ = lean_mk_io_user_error(v___x_732_);
if (v_isShared_698_ == 0)
{
lean_ctor_set_tag(v___x_697_, 1);
lean_ctor_set(v___x_697_, 0, v___x_733_);
v___x_735_ = v___x_697_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
case 1:
{
lean_object* v_method_737_; lean_object* v_params_x3f_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_method_737_ = lean_ctor_get(v_a_695_, 0);
lean_inc_ref(v_method_737_);
v_params_x3f_738_ = lean_ctor_get(v_a_695_, 1);
lean_inc(v_params_x3f_738_);
lean_dec_ref_known(v_a_695_, 2);
v___x_739_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_740_ = lean_string_dec_eq(v_method_737_, v___x_739_);
lean_dec_ref(v_method_737_);
if (v___x_740_ == 0)
{
lean_dec(v_params_x3f_738_);
lean_del_object(v___x_697_);
goto _start;
}
else
{
if (lean_obj_tag(v_params_x3f_738_) == 1)
{
lean_object* v_val_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_761_; 
v_val_742_ = lean_ctor_get(v_params_x3f_738_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_params_x3f_738_);
if (v_isSharedCheck_761_ == 0)
{
v___x_744_ = v_params_x3f_738_;
v_isShared_745_ = v_isSharedCheck_761_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_val_742_);
lean_dec(v_params_x3f_738_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_761_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = l_Lean_Json_Structured_toJson(v_val_742_);
v___x_747_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(v___x_746_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
lean_del_object(v___x_744_);
lean_dec(v_accumulated_x3f_691_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v___x_749_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2));
v___x_750_ = lean_string_append(v___x_749_, v_a_748_);
lean_dec(v_a_748_);
v___x_751_ = lean_mk_io_user_error(v___x_750_);
if (v_isShared_698_ == 0)
{
lean_ctor_set_tag(v___x_697_, 1);
lean_ctor_set(v___x_697_, 0, v___x_751_);
v___x_753_ = v___x_697_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
lean_del_object(v___x_697_);
v_a_755_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_747_, 1);
v___x_756_ = l_Lean_Lsp_Ipc_mergePublishDiagnosticsParams(v_accumulated_x3f_691_, v_a_755_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_756_);
v___x_758_ = v___x_744_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_760_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
v_accumulated_x3f_691_ = v___x_758_;
goto _start;
}
}
}
}
else
{
lean_dec(v_params_x3f_738_);
lean_del_object(v___x_697_);
goto _start;
}
}
}
default: 
{
lean_del_object(v___x_697_);
lean_dec(v_a_695_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_accumulated_x3f_691_);
v_a_765_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_694_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_694_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object* v_waitForDiagnosticsId_773_, lean_object* v_accumulated_x3f_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_773_, v_accumulated_x3f_774_, v_a_775_);
lean_dec_ref(v_a_775_);
lean_dec(v_waitForDiagnosticsId_773_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(lean_object* v_v_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(v_v_778_);
v___x_780_ = l_Lean_Json_Structured_fromJson_x3f(v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object* v_h_781_, lean_object* v_r_782_){
_start:
{
lean_object* v_id_784_; lean_object* v_method_785_; lean_object* v_param_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_806_; 
v_id_784_ = lean_ctor_get(v_r_782_, 0);
v_method_785_ = lean_ctor_get(v_r_782_, 1);
v_param_786_ = lean_ctor_get(v_r_782_, 2);
v_isSharedCheck_806_ = !lean_is_exclusive(v_r_782_);
if (v_isSharedCheck_806_ == 0)
{
v___x_788_ = v_r_782_;
v_isShared_789_ = v_isSharedCheck_806_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_param_786_);
lean_inc(v_method_785_);
lean_inc(v_id_784_);
lean_dec(v_r_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_806_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___y_791_; lean_object* v___x_796_; 
v___x_796_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(v_param_786_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_797_; 
lean_dec_ref_known(v___x_796_, 1);
v___x_797_ = lean_box(0);
v___y_791_ = v___x_797_;
goto v___jp_790_;
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_a_798_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_796_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v___y_791_ = v___x_803_;
goto v___jp_790_;
}
}
}
v___jp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 2, v___y_791_);
v___x_793_ = v___x_788_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_id_784_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_method_785_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v___y_791_);
v___x_793_ = v_reuseFailAlloc_795_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; 
v___x_794_ = l_IO_FS_Stream_writeLspMessage(v_h_781_, v___x_793_);
return v___x_794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0___boxed(lean_object* v_h_807_, lean_object* v_r_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_h_807_, v_r_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object* v_r_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___x_814_; lean_object* v_a_815_; lean_object* v___x_816_; 
v___x_814_ = l_Lean_Lsp_Ipc_stdin(v_a_812_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v___x_814_);
v___x_816_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_a_815_, v_r_811_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0___boxed(lean_object* v_r_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v_r_817_, v_a_818_);
lean_dec_ref(v_a_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object* v_waitForDiagnosticsId_822_, lean_object* v_target_823_, lean_object* v_version_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_827_ = ((lean_object*)(l_Lean_Lsp_Ipc_collectDiagnostics___closed__0));
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v_target_823_);
lean_ctor_set(v___x_828_, 1, v_version_824_);
lean_inc(v_waitForDiagnosticsId_822_);
v___x_829_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_829_, 0, v_waitForDiagnosticsId_822_);
lean_ctor_set(v___x_829_, 1, v___x_827_);
lean_ctor_set(v___x_829_, 2, v___x_828_);
v___x_830_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0(v___x_829_, v_a_825_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_dec_ref_known(v___x_830_, 1);
v___x_831_ = lean_box(0);
v___x_832_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(v_waitForDiagnosticsId_822_, v___x_831_, v_a_825_);
lean_dec(v_waitForDiagnosticsId_822_);
return v___x_832_;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_waitForDiagnosticsId_822_);
v_a_833_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_830_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_830_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___boxed(lean_object* v_waitForDiagnosticsId_841_, lean_object* v_target_842_, lean_object* v_version_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Lsp_Ipc_collectDiagnostics(v_waitForDiagnosticsId_841_, v_target_842_, v_version_843_, v_a_844_);
lean_dec_ref(v_a_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(lean_object* v_v_847_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(v_v_847_);
v___x_849_ = l_Lean_Json_Structured_fromJson_x3f(v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object* v_h_850_, lean_object* v_r_851_){
_start:
{
lean_object* v_id_853_; lean_object* v_method_854_; lean_object* v_param_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_875_; 
v_id_853_ = lean_ctor_get(v_r_851_, 0);
v_method_854_ = lean_ctor_get(v_r_851_, 1);
v_param_855_ = lean_ctor_get(v_r_851_, 2);
v_isSharedCheck_875_ = !lean_is_exclusive(v_r_851_);
if (v_isSharedCheck_875_ == 0)
{
v___x_857_ = v_r_851_;
v_isShared_858_ = v_isSharedCheck_875_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_param_855_);
lean_inc(v_method_854_);
lean_inc(v_id_853_);
lean_dec(v_r_851_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_875_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___y_860_; lean_object* v___x_865_; 
v___x_865_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(v_param_855_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_866_; 
lean_dec_ref_known(v___x_865_, 1);
v___x_866_ = lean_box(0);
v___y_860_ = v___x_866_;
goto v___jp_859_;
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_a_867_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_865_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_865_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
v___y_860_ = v___x_872_;
goto v___jp_859_;
}
}
}
v___jp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 2, v___y_860_);
v___x_862_ = v___x_857_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_id_853_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_method_854_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v___y_860_);
v___x_862_ = v_reuseFailAlloc_864_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; 
v___x_863_ = l_IO_FS_Stream_writeLspMessage(v_h_850_, v___x_862_);
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0___boxed(lean_object* v_h_876_, lean_object* v_r_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_h_876_, v_r_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object* v_r_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; lean_object* v_a_884_; lean_object* v___x_885_; 
v___x_883_ = l_Lean_Lsp_Ipc_stdin(v_a_881_);
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v___x_883_);
v___x_885_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_a_884_, v_r_880_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0___boxed(lean_object* v_r_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v_r_886_, v_a_887_);
lean_dec_ref(v_a_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(lean_object* v_waitForILeansId_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Lsp_Ipc_readMessage(v___y_897_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_922_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_922_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_922_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_922_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
switch(lean_obj_tag(v_a_900_))
{
case 2:
{
lean_object* v_id_904_; uint8_t v___x_905_; 
v_id_904_ = lean_ctor_get(v_a_900_, 0);
lean_inc(v_id_904_);
lean_dec_ref_known(v_a_900_, 2);
v___x_905_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_904_, v_waitForILeansId_896_);
lean_dec(v_id_904_);
if (v___x_905_ == 0)
{
lean_del_object(v___x_902_);
goto _start;
}
else
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1));
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_907_);
v___x_909_ = v___x_902_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
case 3:
{
lean_object* v_id_911_; lean_object* v_message_912_; uint8_t v___x_913_; 
v_id_911_ = lean_ctor_get(v_a_900_, 0);
lean_inc(v_id_911_);
v_message_912_ = lean_ctor_get(v_a_900_, 1);
lean_inc_ref(v_message_912_);
lean_dec_ref_known(v_a_900_, 3);
v___x_913_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_911_, v_waitForILeansId_896_);
lean_dec(v_id_911_);
if (v___x_913_ == 0)
{
lean_dec_ref(v_message_912_);
lean_del_object(v___x_902_);
goto _start;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_915_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2));
v___x_916_ = lean_string_append(v___x_915_, v_message_912_);
lean_dec_ref(v_message_912_);
v___x_917_ = lean_mk_io_user_error(v___x_916_);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 1);
lean_ctor_set(v___x_902_, 0, v___x_917_);
v___x_919_ = v___x_902_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
default: 
{
lean_del_object(v___x_902_);
lean_dec(v_a_900_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_a_923_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_899_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_899_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___boxed(lean_object* v_waitForILeansId_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_931_, v___y_932_);
lean_dec_ref(v___y_932_);
lean_dec(v_waitForILeansId_931_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object* v_waitForILeansId_936_, lean_object* v_target_937_, lean_object* v_version_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_941_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v_target_937_);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v_version_938_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
lean_inc(v_waitForILeansId_936_);
v___x_945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_945_, 0, v_waitForILeansId_936_);
lean_ctor_set(v___x_945_, 1, v___x_941_);
lean_ctor_set(v___x_945_, 2, v___x_944_);
v___x_946_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_945_, v_a_939_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v___x_947_; 
lean_dec_ref_known(v___x_946_, 1);
v___x_947_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_936_, v_a_939_);
lean_dec(v_waitForILeansId_936_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_961_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_961_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_961_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_961_;
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
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = lean_box(0);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_953_);
v___x_955_ = v___x_950_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
else
{
lean_object* v_val_957_; lean_object* v___x_959_; 
v_val_957_ = lean_ctor_get(v_fst_952_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v_fst_952_, 1);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v_val_957_);
v___x_959_ = v___x_950_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_val_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
v_a_962_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_947_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_947_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
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
lean_dec(v_waitForILeansId_936_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans___boxed(lean_object* v_waitForILeansId_970_, lean_object* v_target_971_, lean_object* v_version_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Lsp_Ipc_waitForILeans(v_waitForILeansId_970_, v_target_971_, v_version_972_, v_a_973_);
lean_dec_ref(v_a_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(lean_object* v_waitForILeansId_976_, lean_object* v_inst_977_, lean_object* v_a_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_976_, v___y_979_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___boxed(lean_object* v_waitForILeansId_982_, lean_object* v_inst_983_, lean_object* v_a_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(v_waitForILeansId_982_, v_inst_983_, v_a_984_, v___y_985_);
lean_dec_ref(v___y_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_waitForILeansId_982_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans(lean_object* v_waitForILeansId_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_993_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_994_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0));
lean_inc(v_waitForILeansId_990_);
v___x_995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_995_, 0, v_waitForILeansId_990_);
lean_ctor_set(v___x_995_, 1, v___x_993_);
lean_ctor_set(v___x_995_, 2, v___x_994_);
v___x_996_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_995_, v_a_991_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_997_; 
lean_dec_ref_known(v___x_996_, 1);
v___x_997_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_990_, v_a_991_);
lean_dec(v_waitForILeansId_990_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1011_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1011_;
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
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_box(0);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1003_);
v___x_1005_ = v___x_1000_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
lean_object* v_val_1007_; lean_object* v___x_1009_; 
v_val_1007_ = lean_ctor_get(v_fst_1002_, 0);
lean_inc(v_val_1007_);
lean_dec_ref_known(v_fst_1002_, 1);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v_val_1007_);
v___x_1009_ = v___x_1000_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_val_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_997_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_997_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
else
{
lean_dec(v_waitForILeansId_990_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___boxed(lean_object* v_waitForILeansId_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Lsp_Ipc_waitForWatchdogILeans(v_waitForILeansId_1020_, v_a_1021_);
lean_dec_ref(v_a_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(lean_object* v_j_1024_, lean_object* v_k_1025_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = l_Lean_Json_getObjValD(v_j_1024_, v_k_1025_);
v___x_1027_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0___boxed(lean_object* v_j_1028_, lean_object* v_k_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_j_1028_, v_k_1029_);
lean_dec_ref(v_k_1029_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_1031_, size_t v_i_1032_, lean_object* v_bs_1033_){
_start:
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_usize_dec_lt(v_i_1032_, v_sz_1031_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v_bs_1033_);
return v___x_1035_;
}
else
{
lean_object* v_v_1036_; lean_object* v___x_1037_; 
v_v_1036_ = lean_array_uget_borrowed(v_bs_1033_, v_i_1032_);
lean_inc(v_v_1036_);
v___x_1037_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_v_1036_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_bs_1033_);
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1047_; lean_object* v_bs_x27_1048_; size_t v___x_1049_; size_t v___x_1050_; lean_object* v___x_1051_; 
v_a_1046_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1047_ = lean_unsigned_to_nat(0u);
v_bs_x27_1048_ = lean_array_uset(v_bs_1033_, v_i_1032_, v___x_1047_);
v___x_1049_ = ((size_t)1ULL);
v___x_1050_ = lean_usize_add(v_i_1032_, v___x_1049_);
v___x_1051_ = lean_array_uset(v_bs_x27_1048_, v_i_1032_, v_a_1046_);
v_i_1032_ = v___x_1050_;
v_bs_1033_ = v___x_1051_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1053_, lean_object* v_i_1054_, lean_object* v_bs_1055_){
_start:
{
size_t v_sz_boxed_1056_; size_t v_i_boxed_1057_; lean_object* v_res_1058_; 
v_sz_boxed_1056_ = lean_unbox_usize(v_sz_1053_);
lean_dec(v_sz_1053_);
v_i_boxed_1057_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_res_1058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_1056_, v_i_boxed_1057_, v_bs_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_1060_){
_start:
{
if (lean_obj_tag(v_x_1060_) == 4)
{
lean_object* v_elems_1061_; size_t v_sz_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v_elems_1061_ = lean_ctor_get(v_x_1060_, 0);
lean_inc_ref(v_elems_1061_);
lean_dec_ref_known(v_x_1060_, 1);
v_sz_1062_ = lean_array_size(v_elems_1061_);
v___x_1063_ = ((size_t)0ULL);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_1062_, v___x_1063_, v_elems_1061_);
return v___x_1064_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1065_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1066_ = lean_unsigned_to_nat(80u);
v___x_1067_ = l_Lean_Json_pretty(v_x_1060_, v___x_1066_);
v___x_1068_ = lean_string_append(v___x_1065_, v___x_1067_);
lean_dec_ref(v___x_1067_);
v___x_1069_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1070_ = lean_string_append(v___x_1068_, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(lean_object* v_j_1072_, lean_object* v_k_1073_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = l_Lean_Json_getObjValD(v_j_1072_, v_k_1073_);
v___x_1075_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1___boxed(lean_object* v_j_1076_, lean_object* v_k_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_j_1076_, v_k_1077_);
lean_dec_ref(v_k_1077_);
return v_res_1078_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = 1;
v___x_1084_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9));
v___x_1085_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1084_, v___x_1083_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = 1;
v___x_1097_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5));
v___x_1098_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1097_, v___x_1096_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_1100_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6);
v___x_1101_ = lean_string_append(v___x_1100_, v___x_1099_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_1103_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1104_ = lean_string_append(v___x_1103_, v___x_1102_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1106_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11);
v___x_1107_ = lean_string_append(v___x_1106_, v___x_1105_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = 1;
v___x_1112_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15));
v___x_1113_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1112_, v___x_1111_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16);
v___x_1115_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1116_ = lean_string_append(v___x_1115_, v___x_1114_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1118_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17);
v___x_1119_ = lean_string_append(v___x_1118_, v___x_1117_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = 1;
v___x_1124_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20));
v___x_1125_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1124_, v___x_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_1127_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1128_ = lean_string_append(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1130_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22);
v___x_1131_ = lean_string_append(v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(lean_object* v_json_1132_){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_1132_);
v___x_1134_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_json_1132_, v___x_1133_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_json_1132_);
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1144_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1144_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1139_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13);
v___x_1140_ = lean_string_append(v___x_1139_, v_a_1135_);
lean_dec(v_a_1135_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1140_);
v___x_1142_ = v___x_1137_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
else
{
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_json_1132_);
v_a_1145_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1134_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1134_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 0);
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v_a_1153_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1154_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
lean_inc(v_json_1132_);
v___x_1155_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_json_1132_, v___x_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_a_1153_);
lean_dec(v_json_1132_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1165_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1165_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1160_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18);
v___x_1161_ = lean_string_append(v___x_1160_, v_a_1156_);
lean_dec(v_a_1156_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1161_);
v___x_1163_ = v___x_1158_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v_a_1153_);
lean_dec(v_json_1132_);
v_a_1166_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1155_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1155_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 0);
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_a_1174_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1175_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1176_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_json_1132_, v___x_1175_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_a_1174_);
lean_dec(v_a_1153_);
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1181_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23);
v___x_1182_ = lean_string_append(v___x_1181_, v_a_1177_);
lean_dec(v_a_1177_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1182_);
v___x_1184_ = v___x_1179_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
else
{
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec(v_a_1174_);
lean_dec(v_a_1153_);
v_a_1187_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1176_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1176_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 0);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1203_; 
v_a_1195_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1197_ = v___x_1176_;
v_isShared_1198_ = v_isSharedCheck_1203_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1176_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1203_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1199_, 0, v_a_1153_);
lean_ctor_set(v___x_1199_, 1, v_a_1174_);
lean_ctor_set(v___x_1199_, 2, v_a_1195_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1199_);
v___x_1201_ = v___x_1197_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(size_t v_sz_1204_, size_t v_i_1205_, lean_object* v_bs_1206_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = lean_usize_dec_lt(v_i_1205_, v_sz_1204_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_bs_1206_);
return v___x_1208_;
}
else
{
lean_object* v_v_1209_; lean_object* v___x_1210_; 
v_v_1209_ = lean_array_uget_borrowed(v_bs_1206_, v_i_1205_);
lean_inc(v_v_1209_);
v___x_1210_ = l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(v_v_1209_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v_bs_1206_);
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1220_; lean_object* v_bs_x27_1221_; size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
v_a_1219_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1220_ = lean_unsigned_to_nat(0u);
v_bs_x27_1221_ = lean_array_uset(v_bs_1206_, v_i_1205_, v___x_1220_);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1205_, v___x_1222_);
v___x_1224_ = lean_array_uset(v_bs_x27_1221_, v_i_1205_, v_a_1219_);
v_i_1205_ = v___x_1223_;
v_bs_1206_ = v___x_1224_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(lean_object* v_x_1226_){
_start:
{
if (lean_obj_tag(v_x_1226_) == 4)
{
lean_object* v_elems_1227_; size_t v_sz_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v_elems_1227_ = lean_ctor_get(v_x_1226_, 0);
lean_inc_ref(v_elems_1227_);
lean_dec_ref_known(v_x_1226_, 1);
v_sz_1228_ = lean_array_size(v_elems_1227_);
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_1228_, v___x_1229_, v_elems_1227_);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1231_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1232_ = lean_unsigned_to_nat(80u);
v___x_1233_ = l_Lean_Json_pretty(v_x_1226_, v___x_1232_);
v___x_1234_ = lean_string_append(v___x_1231_, v___x_1233_);
lean_dec_ref(v___x_1233_);
v___x_1235_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1236_ = lean_string_append(v___x_1234_, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(lean_object* v_j_1238_, lean_object* v_k_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = l_Lean_Json_getObjValD(v_j_1238_, v_k_1239_);
v___x_1241_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2___boxed(lean_object* v_j_1242_, lean_object* v_k_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_j_1242_, v_k_1243_);
lean_dec_ref(v_k_1243_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1245_, lean_object* v_i_1246_, lean_object* v_bs_1247_){
_start:
{
size_t v_sz_boxed_1248_; size_t v_i_boxed_1249_; lean_object* v_res_1250_; 
v_sz_boxed_1248_ = lean_unbox_usize(v_sz_1245_);
lean_dec(v_sz_1245_);
v_i_boxed_1249_ = lean_unbox_usize(v_i_1246_);
lean_dec(v_i_1246_);
v_res_1250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_boxed_1248_, v_i_boxed_1249_, v_bs_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
if (lean_obj_tag(v_a_1253_) == 0)
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_array_to_list(v_a_1254_);
return v___x_1255_;
}
else
{
lean_object* v_head_1256_; lean_object* v_tail_1257_; lean_object* v___x_1258_; 
v_head_1256_ = lean_ctor_get(v_a_1253_, 0);
lean_inc(v_head_1256_);
v_tail_1257_ = lean_ctor_get(v_a_1253_, 1);
lean_inc(v_tail_1257_);
lean_dec_ref_known(v_a_1253_, 2);
v___x_1258_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1254_, v_head_1256_);
v_a_1253_ = v_tail_1257_;
v_a_1254_ = v___x_1258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(size_t v_sz_1260_, size_t v_i_1261_, lean_object* v_bs_1262_){
_start:
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_usize_dec_lt(v_i_1261_, v_sz_1260_);
if (v___x_1263_ == 0)
{
return v_bs_1262_;
}
else
{
lean_object* v_v_1264_; lean_object* v___x_1265_; lean_object* v_bs_x27_1266_; lean_object* v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; lean_object* v___x_1270_; 
v_v_1264_ = lean_array_uget(v_bs_1262_, v_i_1261_);
v___x_1265_ = lean_unsigned_to_nat(0u);
v_bs_x27_1266_ = lean_array_uset(v_bs_1262_, v_i_1261_, v___x_1265_);
v___x_1267_ = l_Lean_Lsp_instToJsonRange_toJson(v_v_1264_);
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_add(v_i_1261_, v___x_1268_);
v___x_1270_ = lean_array_uset(v_bs_x27_1266_, v_i_1261_, v___x_1267_);
v_i_1261_ = v___x_1269_;
v_bs_1262_ = v___x_1270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1272_, lean_object* v_i_1273_, lean_object* v_bs_1274_){
_start:
{
size_t v_sz_boxed_1275_; size_t v_i_boxed_1276_; lean_object* v_res_1277_; 
v_sz_boxed_1275_ = lean_unbox_usize(v_sz_1272_);
lean_dec(v_sz_1272_);
v_i_boxed_1276_ = lean_unbox_usize(v_i_1273_);
lean_dec(v_i_1273_);
v_res_1277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_boxed_1275_, v_i_boxed_1276_, v_bs_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(lean_object* v_a_1278_){
_start:
{
size_t v_sz_1279_; size_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_sz_1279_ = lean_array_size(v_a_1278_);
v___x_1280_ = ((size_t)0ULL);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_1279_, v___x_1280_, v_a_1278_);
v___x_1282_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(lean_object* v_x_1285_){
_start:
{
lean_object* v_item_1286_; lean_object* v_fromRanges_1287_; lean_object* v_children_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_item_1286_ = lean_ctor_get(v_x_1285_, 0);
lean_inc_ref(v_item_1286_);
v_fromRanges_1287_ = lean_ctor_get(v_x_1285_, 1);
lean_inc_ref(v_fromRanges_1287_);
v_children_1288_ = lean_ctor_get(v_x_1285_, 2);
lean_inc_ref(v_children_1288_);
lean_dec_ref(v_x_1285_);
v___x_1289_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_1290_ = l_Lean_Lsp_instToJsonCallHierarchyItem_toJson(v_item_1286_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1289_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = lean_box(0);
v___x_1293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
v___x_1295_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(v_fromRanges_1287_);
v___x_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
lean_ctor_set(v___x_1297_, 1, v___x_1292_);
v___x_1298_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1299_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(v_children_1288_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___x_1292_);
v___x_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v___x_1292_);
v___x_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1297_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1293_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_1306_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_1304_, v___x_1305_);
v___x_1307_ = l_Lean_Json_mkObj(v___x_1306_);
lean_dec(v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(size_t v_sz_1308_, size_t v_i_1309_, lean_object* v_bs_1310_){
_start:
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_usize_dec_lt(v_i_1309_, v_sz_1308_);
if (v___x_1311_ == 0)
{
return v_bs_1310_;
}
else
{
lean_object* v_v_1312_; lean_object* v___x_1313_; lean_object* v_bs_x27_1314_; lean_object* v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v_v_1312_ = lean_array_uget(v_bs_1310_, v_i_1309_);
v___x_1313_ = lean_unsigned_to_nat(0u);
v_bs_x27_1314_ = lean_array_uset(v_bs_1310_, v_i_1309_, v___x_1313_);
v___x_1315_ = l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(v_v_1312_);
v___x_1316_ = ((size_t)1ULL);
v___x_1317_ = lean_usize_add(v_i_1309_, v___x_1316_);
v___x_1318_ = lean_array_uset(v_bs_x27_1314_, v_i_1309_, v___x_1315_);
v_i_1309_ = v___x_1317_;
v_bs_1310_ = v___x_1318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(lean_object* v_a_1320_){
_start:
{
size_t v_sz_1321_; size_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_sz_1321_ = lean_array_size(v_a_1320_);
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_1321_, v___x_1322_, v_a_1320_);
v___x_1324_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2___boxed(lean_object* v_sz_1325_, lean_object* v_i_1326_, lean_object* v_bs_1327_){
_start:
{
size_t v_sz_boxed_1328_; size_t v_i_boxed_1329_; lean_object* v_res_1330_; 
v_sz_boxed_1328_ = lean_unbox_usize(v_sz_1325_);
lean_dec(v_sz_1325_);
v_i_boxed_1329_ = lean_unbox_usize(v_i_1326_);
lean_dec(v_i_1326_);
v_res_1330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_boxed_1328_, v_i_boxed_1329_, v_bs_1327_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(lean_object* v_k_1333_, lean_object* v_v_1334_, lean_object* v_t_1335_){
_start:
{
if (lean_obj_tag(v_t_1335_) == 0)
{
lean_object* v_size_1336_; lean_object* v_k_1337_; lean_object* v_v_1338_; lean_object* v_l_1339_; lean_object* v_r_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1620_; 
v_size_1336_ = lean_ctor_get(v_t_1335_, 0);
v_k_1337_ = lean_ctor_get(v_t_1335_, 1);
v_v_1338_ = lean_ctor_get(v_t_1335_, 2);
v_l_1339_ = lean_ctor_get(v_t_1335_, 3);
v_r_1340_ = lean_ctor_get(v_t_1335_, 4);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_t_1335_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1342_ = v_t_1335_;
v_isShared_1343_ = v_isSharedCheck_1620_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_r_1340_);
lean_inc(v_l_1339_);
lean_inc(v_v_1338_);
lean_inc(v_k_1337_);
lean_inc(v_size_1336_);
lean_dec(v_t_1335_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1620_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_string_compare(v_k_1333_, v_k_1337_);
switch(v___x_1344_)
{
case 0:
{
lean_object* v_impl_1345_; lean_object* v___x_1346_; 
lean_dec(v_size_1336_);
v_impl_1345_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1333_, v_v_1334_, v_l_1339_);
v___x_1346_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1340_) == 0)
{
lean_object* v_size_1347_; lean_object* v_size_1348_; lean_object* v_k_1349_; lean_object* v_v_1350_; lean_object* v_l_1351_; lean_object* v_r_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v_size_1347_ = lean_ctor_get(v_r_1340_, 0);
v_size_1348_ = lean_ctor_get(v_impl_1345_, 0);
lean_inc(v_size_1348_);
v_k_1349_ = lean_ctor_get(v_impl_1345_, 1);
lean_inc(v_k_1349_);
v_v_1350_ = lean_ctor_get(v_impl_1345_, 2);
lean_inc(v_v_1350_);
v_l_1351_ = lean_ctor_get(v_impl_1345_, 3);
lean_inc(v_l_1351_);
v_r_1352_ = lean_ctor_get(v_impl_1345_, 4);
lean_inc(v_r_1352_);
v___x_1353_ = lean_unsigned_to_nat(3u);
v___x_1354_ = lean_nat_mul(v___x_1353_, v_size_1347_);
v___x_1355_ = lean_nat_dec_lt(v___x_1354_, v_size_1348_);
lean_dec(v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
lean_dec(v_r_1352_);
lean_dec(v_l_1351_);
lean_dec(v_v_1350_);
lean_dec(v_k_1349_);
v___x_1356_ = lean_nat_add(v___x_1346_, v_size_1348_);
lean_dec(v_size_1348_);
v___x_1357_ = lean_nat_add(v___x_1356_, v_size_1347_);
lean_dec(v___x_1356_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 3, v_impl_1345_);
lean_ctor_set(v___x_1342_, 0, v___x_1357_);
v___x_1359_ = v___x_1342_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v_impl_1345_);
lean_ctor_set(v_reuseFailAlloc_1360_, 4, v_r_1340_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
else
{
lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1426_; 
v_isSharedCheck_1426_ = !lean_is_exclusive(v_impl_1345_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; lean_object* v_unused_1428_; lean_object* v_unused_1429_; lean_object* v_unused_1430_; lean_object* v_unused_1431_; 
v_unused_1427_ = lean_ctor_get(v_impl_1345_, 4);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_impl_1345_, 3);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_impl_1345_, 2);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_impl_1345_, 1);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_impl_1345_, 0);
lean_dec(v_unused_1431_);
v___x_1362_ = v_impl_1345_;
v_isShared_1363_ = v_isSharedCheck_1426_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v_impl_1345_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1426_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_size_1364_; lean_object* v_size_1365_; lean_object* v_k_1366_; lean_object* v_v_1367_; lean_object* v_l_1368_; lean_object* v_r_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_size_1364_ = lean_ctor_get(v_l_1351_, 0);
v_size_1365_ = lean_ctor_get(v_r_1352_, 0);
v_k_1366_ = lean_ctor_get(v_r_1352_, 1);
v_v_1367_ = lean_ctor_get(v_r_1352_, 2);
v_l_1368_ = lean_ctor_get(v_r_1352_, 3);
v_r_1369_ = lean_ctor_get(v_r_1352_, 4);
v___x_1370_ = lean_unsigned_to_nat(2u);
v___x_1371_ = lean_nat_mul(v___x_1370_, v_size_1364_);
v___x_1372_ = lean_nat_dec_lt(v_size_1365_, v___x_1371_);
lean_dec(v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1401_; 
lean_inc(v_r_1369_);
lean_inc(v_l_1368_);
lean_inc(v_v_1367_);
lean_inc(v_k_1366_);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_r_1352_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; lean_object* v_unused_1403_; lean_object* v_unused_1404_; lean_object* v_unused_1405_; lean_object* v_unused_1406_; 
v_unused_1402_ = lean_ctor_get(v_r_1352_, 4);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_r_1352_, 3);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_r_1352_, 2);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_r_1352_, 1);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_r_1352_, 0);
lean_dec(v_unused_1406_);
v___x_1374_ = v_r_1352_;
v_isShared_1375_ = v_isSharedCheck_1401_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v_r_1352_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1401_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___x_1389_; lean_object* v___y_1391_; 
v___x_1376_ = lean_nat_add(v___x_1346_, v_size_1348_);
lean_dec(v_size_1348_);
v___x_1377_ = lean_nat_add(v___x_1376_, v_size_1347_);
lean_dec(v___x_1376_);
v___x_1389_ = lean_nat_add(v___x_1346_, v_size_1364_);
if (lean_obj_tag(v_l_1368_) == 0)
{
lean_object* v_size_1399_; 
v_size_1399_ = lean_ctor_get(v_l_1368_, 0);
lean_inc(v_size_1399_);
v___y_1391_ = v_size_1399_;
goto v___jp_1390_;
}
else
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_unsigned_to_nat(0u);
v___y_1391_ = v___x_1400_;
goto v___jp_1390_;
}
v___jp_1378_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = lean_nat_add(v___y_1379_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec(v___y_1379_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 4, v_r_1340_);
lean_ctor_set(v___x_1374_, 3, v_r_1369_);
lean_ctor_set(v___x_1374_, 2, v_v_1338_);
lean_ctor_set(v___x_1374_, 1, v_k_1337_);
lean_ctor_set(v___x_1374_, 0, v___x_1382_);
v___x_1384_ = v___x_1374_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1388_, 3, v_r_1369_);
lean_ctor_set(v_reuseFailAlloc_1388_, 4, v_r_1340_);
v___x_1384_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1386_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v___x_1384_);
lean_ctor_set(v___x_1362_, 3, v___y_1380_);
lean_ctor_set(v___x_1362_, 2, v_v_1367_);
lean_ctor_set(v___x_1362_, 1, v_k_1366_);
lean_ctor_set(v___x_1362_, 0, v___x_1377_);
v___x_1386_ = v___x_1362_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_k_1366_);
lean_ctor_set(v_reuseFailAlloc_1387_, 2, v_v_1367_);
lean_ctor_set(v_reuseFailAlloc_1387_, 3, v___y_1380_);
lean_ctor_set(v_reuseFailAlloc_1387_, 4, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
v___jp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = lean_nat_add(v___x_1389_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec(v___x_1389_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 4, v_l_1368_);
lean_ctor_set(v___x_1342_, 3, v_l_1351_);
lean_ctor_set(v___x_1342_, 2, v_v_1350_);
lean_ctor_set(v___x_1342_, 1, v_k_1349_);
lean_ctor_set(v___x_1342_, 0, v___x_1392_);
v___x_1394_ = v___x_1342_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_k_1349_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_v_1350_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v_l_1351_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v_l_1368_);
v___x_1394_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_nat_add(v___x_1346_, v_size_1347_);
if (lean_obj_tag(v_r_1369_) == 0)
{
lean_object* v_size_1396_; 
v_size_1396_ = lean_ctor_get(v_r_1369_, 0);
lean_inc(v_size_1396_);
v___y_1379_ = v___x_1395_;
v___y_1380_ = v___x_1394_;
v___y_1381_ = v_size_1396_;
goto v___jp_1378_;
}
else
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
v___y_1379_ = v___x_1395_;
v___y_1380_ = v___x_1394_;
v___y_1381_ = v___x_1397_;
goto v___jp_1378_;
}
}
}
}
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_del_object(v___x_1342_);
v___x_1407_ = lean_nat_add(v___x_1346_, v_size_1348_);
lean_dec(v_size_1348_);
v___x_1408_ = lean_nat_add(v___x_1407_, v_size_1347_);
lean_dec(v___x_1407_);
v___x_1409_ = lean_nat_add(v___x_1346_, v_size_1347_);
v___x_1410_ = lean_nat_add(v___x_1409_, v_size_1365_);
lean_dec(v___x_1409_);
lean_inc_ref(v_r_1340_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_r_1340_);
lean_ctor_set(v___x_1362_, 3, v_r_1352_);
lean_ctor_set(v___x_1362_, 2, v_v_1338_);
lean_ctor_set(v___x_1362_, 1, v_k_1337_);
lean_ctor_set(v___x_1362_, 0, v___x_1410_);
v___x_1412_ = v___x_1362_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_r_1352_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_r_1340_);
v___x_1412_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_isSharedCheck_1419_ = !lean_is_exclusive(v_r_1340_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; lean_object* v_unused_1421_; lean_object* v_unused_1422_; lean_object* v_unused_1423_; lean_object* v_unused_1424_; 
v_unused_1420_ = lean_ctor_get(v_r_1340_, 4);
lean_dec(v_unused_1420_);
v_unused_1421_ = lean_ctor_get(v_r_1340_, 3);
lean_dec(v_unused_1421_);
v_unused_1422_ = lean_ctor_get(v_r_1340_, 2);
lean_dec(v_unused_1422_);
v_unused_1423_ = lean_ctor_get(v_r_1340_, 1);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v_r_1340_, 0);
lean_dec(v_unused_1424_);
v___x_1414_ = v_r_1340_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v_r_1340_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 4, v___x_1412_);
lean_ctor_set(v___x_1414_, 3, v_l_1351_);
lean_ctor_set(v___x_1414_, 2, v_v_1350_);
lean_ctor_set(v___x_1414_, 1, v_k_1349_);
lean_ctor_set(v___x_1414_, 0, v___x_1408_);
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_k_1349_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_v_1350_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v_l_1351_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v___x_1412_);
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
v_l_1432_ = lean_ctor_get(v_impl_1345_, 3);
lean_inc(v_l_1432_);
if (lean_obj_tag(v_l_1432_) == 0)
{
lean_object* v_r_1433_; lean_object* v_k_1434_; lean_object* v_v_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1446_; 
v_r_1433_ = lean_ctor_get(v_impl_1345_, 4);
v_k_1434_ = lean_ctor_get(v_impl_1345_, 1);
v_v_1435_ = lean_ctor_get(v_impl_1345_, 2);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_impl_1345_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; lean_object* v_unused_1448_; 
v_unused_1447_ = lean_ctor_get(v_impl_1345_, 3);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_impl_1345_, 0);
lean_dec(v_unused_1448_);
v___x_1437_ = v_impl_1345_;
v_isShared_1438_ = v_isSharedCheck_1446_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_r_1433_);
lean_inc(v_v_1435_);
lean_inc(v_k_1434_);
lean_dec(v_impl_1345_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1446_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1433_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 3, v_r_1433_);
lean_ctor_set(v___x_1437_, 2, v_v_1338_);
lean_ctor_set(v___x_1437_, 1, v_k_1337_);
lean_ctor_set(v___x_1437_, 0, v___x_1346_);
v___x_1441_ = v___x_1437_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_r_1433_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v_r_1433_);
v___x_1441_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 4, v___x_1441_);
lean_ctor_set(v___x_1342_, 3, v_l_1432_);
lean_ctor_set(v___x_1342_, 2, v_v_1435_);
lean_ctor_set(v___x_1342_, 1, v_k_1434_);
lean_ctor_set(v___x_1342_, 0, v___x_1439_);
v___x_1443_ = v___x_1342_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1434_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1435_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_l_1432_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_r_1449_; 
v_r_1449_ = lean_ctor_get(v_impl_1345_, 4);
lean_inc(v_r_1449_);
if (lean_obj_tag(v_r_1449_) == 0)
{
lean_object* v_k_1450_; lean_object* v_v_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1474_; 
v_k_1450_ = lean_ctor_get(v_impl_1345_, 1);
v_v_1451_ = lean_ctor_get(v_impl_1345_, 2);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_impl_1345_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; 
v_unused_1475_ = lean_ctor_get(v_impl_1345_, 4);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_impl_1345_, 3);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_impl_1345_, 0);
lean_dec(v_unused_1477_);
v___x_1453_ = v_impl_1345_;
v_isShared_1454_ = v_isSharedCheck_1474_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_v_1451_);
lean_inc(v_k_1450_);
lean_dec(v_impl_1345_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1474_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v_k_1455_; lean_object* v_v_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1470_; 
v_k_1455_ = lean_ctor_get(v_r_1449_, 1);
v_v_1456_ = lean_ctor_get(v_r_1449_, 2);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_r_1449_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; lean_object* v_unused_1472_; lean_object* v_unused_1473_; 
v_unused_1471_ = lean_ctor_get(v_r_1449_, 4);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_r_1449_, 3);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_r_1449_, 0);
lean_dec(v_unused_1473_);
v___x_1458_ = v_r_1449_;
v_isShared_1459_ = v_isSharedCheck_1470_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_v_1456_);
lean_inc(v_k_1455_);
lean_dec(v_r_1449_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1470_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1460_ = lean_unsigned_to_nat(3u);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 4, v_l_1432_);
lean_ctor_set(v___x_1458_, 3, v_l_1432_);
lean_ctor_set(v___x_1458_, 2, v_v_1451_);
lean_ctor_set(v___x_1458_, 1, v_k_1450_);
lean_ctor_set(v___x_1458_, 0, v___x_1346_);
v___x_1462_ = v___x_1458_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_k_1450_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_v_1451_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_l_1432_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_l_1432_);
v___x_1462_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 4, v_l_1432_);
lean_ctor_set(v___x_1453_, 2, v_v_1338_);
lean_ctor_set(v___x_1453_, 1, v_k_1337_);
lean_ctor_set(v___x_1453_, 0, v___x_1346_);
v___x_1464_ = v___x_1453_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_l_1432_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v_l_1432_);
v___x_1464_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1466_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 4, v___x_1464_);
lean_ctor_set(v___x_1342_, 3, v___x_1462_);
lean_ctor_set(v___x_1342_, 2, v_v_1456_);
lean_ctor_set(v___x_1342_, 1, v_k_1455_);
lean_ctor_set(v___x_1342_, 0, v___x_1460_);
v___x_1466_ = v___x_1342_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_k_1455_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_v_1456_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
}
else
{
lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1478_ = lean_unsigned_to_nat(2u);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 4, v_r_1449_);
lean_ctor_set(v___x_1342_, 3, v_impl_1345_);
lean_ctor_set(v___x_1342_, 0, v___x_1478_);
v___x_1480_ = v___x_1342_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_impl_1345_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_r_1449_);
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
case 1:
{
lean_object* v___x_1483_; 
lean_dec(v_v_1338_);
lean_dec(v_k_1337_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 2, v_v_1334_);
lean_ctor_set(v___x_1342_, 1, v_k_1333_);
v___x_1483_ = v___x_1342_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_size_1336_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1333_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1334_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_l_1339_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_r_1340_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
default: 
{
lean_object* v_impl_1485_; lean_object* v___x_1486_; 
lean_dec(v_size_1336_);
v_impl_1485_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1333_, v_v_1334_, v_r_1340_);
v___x_1486_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1339_) == 0)
{
lean_object* v_size_1487_; lean_object* v_size_1488_; lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v_l_1491_; lean_object* v_r_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v_size_1487_ = lean_ctor_get(v_l_1339_, 0);
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
v___x_1496_ = lean_nat_add(v___x_1486_, v_size_1487_);
v___x_1497_ = lean_nat_add(v___x_1496_, v_size_1488_);
lean_dec(v_size_1488_);
lean_dec(v___x_1496_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 4, v_impl_1485_);
lean_ctor_set(v___x_1342_, 0, v___x_1497_);
v___x_1499_ = v___x_1342_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1339_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_impl_1485_);
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
lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1564_; 
v_isSharedCheck_1564_ = !lean_is_exclusive(v_impl_1485_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; lean_object* v_unused_1566_; lean_object* v_unused_1567_; lean_object* v_unused_1568_; lean_object* v_unused_1569_; 
v_unused_1565_ = lean_ctor_get(v_impl_1485_, 4);
lean_dec(v_unused_1565_);
v_unused_1566_ = lean_ctor_get(v_impl_1485_, 3);
lean_dec(v_unused_1566_);
v_unused_1567_ = lean_ctor_get(v_impl_1485_, 2);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v_impl_1485_, 1);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_impl_1485_, 0);
lean_dec(v_unused_1569_);
v___x_1502_ = v_impl_1485_;
v_isShared_1503_ = v_isSharedCheck_1564_;
goto v_resetjp_1501_;
}
else
{
lean_dec(v_impl_1485_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1564_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_size_1504_; lean_object* v_k_1505_; lean_object* v_v_1506_; lean_object* v_l_1507_; lean_object* v_r_1508_; lean_object* v_size_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v_size_1504_ = lean_ctor_get(v_l_1491_, 0);
v_k_1505_ = lean_ctor_get(v_l_1491_, 1);
v_v_1506_ = lean_ctor_get(v_l_1491_, 2);
v_l_1507_ = lean_ctor_get(v_l_1491_, 3);
v_r_1508_ = lean_ctor_get(v_l_1491_, 4);
v_size_1509_ = lean_ctor_get(v_r_1492_, 0);
v___x_1510_ = lean_unsigned_to_nat(2u);
v___x_1511_ = lean_nat_mul(v___x_1510_, v_size_1509_);
v___x_1512_ = lean_nat_dec_lt(v_size_1504_, v___x_1511_);
lean_dec(v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1540_; 
lean_inc(v_r_1508_);
lean_inc(v_l_1507_);
lean_inc(v_v_1506_);
lean_inc(v_k_1505_);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_l_1491_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; lean_object* v_unused_1542_; lean_object* v_unused_1543_; lean_object* v_unused_1544_; lean_object* v_unused_1545_; 
v_unused_1541_ = lean_ctor_get(v_l_1491_, 4);
lean_dec(v_unused_1541_);
v_unused_1542_ = lean_ctor_get(v_l_1491_, 3);
lean_dec(v_unused_1542_);
v_unused_1543_ = lean_ctor_get(v_l_1491_, 2);
lean_dec(v_unused_1543_);
v_unused_1544_ = lean_ctor_get(v_l_1491_, 1);
lean_dec(v_unused_1544_);
v_unused_1545_ = lean_ctor_get(v_l_1491_, 0);
lean_dec(v_unused_1545_);
v___x_1514_ = v_l_1491_;
v_isShared_1515_ = v_isSharedCheck_1540_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v_l_1491_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1540_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1530_; 
v___x_1516_ = lean_nat_add(v___x_1486_, v_size_1487_);
v___x_1517_ = lean_nat_add(v___x_1516_, v_size_1488_);
lean_dec(v_size_1488_);
if (lean_obj_tag(v_l_1507_) == 0)
{
lean_object* v_size_1538_; 
v_size_1538_ = lean_ctor_get(v_l_1507_, 0);
lean_inc(v_size_1538_);
v___y_1530_ = v_size_1538_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_unsigned_to_nat(0u);
v___y_1530_ = v___x_1539_;
goto v___jp_1529_;
}
v___jp_1518_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1522_ = lean_nat_add(v___y_1519_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec(v___y_1519_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 4, v_r_1492_);
lean_ctor_set(v___x_1514_, 3, v_r_1508_);
lean_ctor_set(v___x_1514_, 2, v_v_1490_);
lean_ctor_set(v___x_1514_, 1, v_k_1489_);
lean_ctor_set(v___x_1514_, 0, v___x_1522_);
v___x_1524_ = v___x_1514_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_r_1508_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_r_1492_);
v___x_1524_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1526_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 4, v___x_1524_);
lean_ctor_set(v___x_1502_, 3, v___y_1520_);
lean_ctor_set(v___x_1502_, 2, v_v_1506_);
lean_ctor_set(v___x_1502_, 1, v_k_1505_);
lean_ctor_set(v___x_1502_, 0, v___x_1517_);
v___x_1526_ = v___x_1502_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_k_1505_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_v_1506_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v___y_1520_);
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
v___jp_1529_:
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1531_ = lean_nat_add(v___x_1516_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec(v___x_1516_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 4, v_l_1507_);
lean_ctor_set(v___x_1342_, 0, v___x_1531_);
v___x_1533_ = v___x_1342_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1537_, 3, v_l_1339_);
lean_ctor_set(v_reuseFailAlloc_1537_, 4, v_l_1507_);
v___x_1533_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_nat_add(v___x_1486_, v_size_1509_);
if (lean_obj_tag(v_r_1508_) == 0)
{
lean_object* v_size_1535_; 
v_size_1535_ = lean_ctor_get(v_r_1508_, 0);
lean_inc(v_size_1535_);
v___y_1519_ = v___x_1534_;
v___y_1520_ = v___x_1533_;
v___y_1521_ = v_size_1535_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_unsigned_to_nat(0u);
v___y_1519_ = v___x_1534_;
v___y_1520_ = v___x_1533_;
v___y_1521_ = v___x_1536_;
goto v___jp_1518_;
}
}
}
}
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
lean_del_object(v___x_1342_);
v___x_1546_ = lean_nat_add(v___x_1486_, v_size_1487_);
v___x_1547_ = lean_nat_add(v___x_1546_, v_size_1488_);
lean_dec(v_size_1488_);
v___x_1548_ = lean_nat_add(v___x_1546_, v_size_1504_);
lean_dec(v___x_1546_);
lean_inc_ref(v_l_1339_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 4, v_l_1491_);
lean_ctor_set(v___x_1502_, 3, v_l_1339_);
lean_ctor_set(v___x_1502_, 2, v_v_1338_);
lean_ctor_set(v___x_1502_, 1, v_k_1337_);
lean_ctor_set(v___x_1502_, 0, v___x_1548_);
v___x_1550_ = v___x_1502_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v_l_1339_);
lean_ctor_set(v_reuseFailAlloc_1563_, 4, v_l_1491_);
v___x_1550_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_isSharedCheck_1557_ = !lean_is_exclusive(v_l_1339_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; lean_object* v_unused_1559_; lean_object* v_unused_1560_; lean_object* v_unused_1561_; lean_object* v_unused_1562_; 
v_unused_1558_ = lean_ctor_get(v_l_1339_, 4);
lean_dec(v_unused_1558_);
v_unused_1559_ = lean_ctor_get(v_l_1339_, 3);
lean_dec(v_unused_1559_);
v_unused_1560_ = lean_ctor_get(v_l_1339_, 2);
lean_dec(v_unused_1560_);
v_unused_1561_ = lean_ctor_get(v_l_1339_, 1);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_l_1339_, 0);
lean_dec(v_unused_1562_);
v___x_1552_ = v_l_1339_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_dec(v_l_1339_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 4, v_r_1492_);
lean_ctor_set(v___x_1552_, 3, v___x_1550_);
lean_ctor_set(v___x_1552_, 2, v_v_1490_);
lean_ctor_set(v___x_1552_, 1, v_k_1489_);
lean_ctor_set(v___x_1552_, 0, v___x_1547_);
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_k_1489_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_v_1490_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1556_, 4, v_r_1492_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1570_; 
v_l_1570_ = lean_ctor_get(v_impl_1485_, 3);
lean_inc(v_l_1570_);
if (lean_obj_tag(v_l_1570_) == 0)
{
lean_object* v_r_1571_; lean_object* v_k_1572_; lean_object* v_v_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1596_; 
v_r_1571_ = lean_ctor_get(v_impl_1485_, 4);
v_k_1572_ = lean_ctor_get(v_impl_1485_, 1);
v_v_1573_ = lean_ctor_get(v_impl_1485_, 2);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_impl_1485_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; lean_object* v_unused_1598_; 
v_unused_1597_ = lean_ctor_get(v_impl_1485_, 3);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_impl_1485_, 0);
lean_dec(v_unused_1598_);
v___x_1575_ = v_impl_1485_;
v_isShared_1576_ = v_isSharedCheck_1596_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_r_1571_);
lean_inc(v_v_1573_);
lean_inc(v_k_1572_);
lean_dec(v_impl_1485_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1596_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v_k_1577_; lean_object* v_v_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1592_; 
v_k_1577_ = lean_ctor_get(v_l_1570_, 1);
v_v_1578_ = lean_ctor_get(v_l_1570_, 2);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_l_1570_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1593_ = lean_ctor_get(v_l_1570_, 4);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_l_1570_, 3);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_l_1570_, 0);
lean_dec(v_unused_1595_);
v___x_1580_ = v_l_1570_;
v_isShared_1581_ = v_isSharedCheck_1592_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_v_1578_);
lean_inc(v_k_1577_);
lean_dec(v_l_1570_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1592_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1582_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1571_, 2);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 4, v_r_1571_);
lean_ctor_set(v___x_1580_, 3, v_r_1571_);
lean_ctor_set(v___x_1580_, 2, v_v_1338_);
lean_ctor_set(v___x_1580_, 1, v_k_1337_);
lean_ctor_set(v___x_1580_, 0, v___x_1486_);
v___x_1584_ = v___x_1580_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_r_1571_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_r_1571_);
v___x_1584_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1586_; 
lean_inc(v_r_1571_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 3, v_r_1571_);
lean_ctor_set(v___x_1575_, 0, v___x_1486_);
v___x_1586_ = v___x_1575_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_k_1572_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_v_1573_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_r_1571_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v_r_1571_);
v___x_1586_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1588_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 4, v___x_1586_);
lean_ctor_set(v___x_1342_, 3, v___x_1584_);
lean_ctor_set(v___x_1342_, 2, v_v_1578_);
lean_ctor_set(v___x_1342_, 1, v_k_1577_);
lean_ctor_set(v___x_1342_, 0, v___x_1582_);
v___x_1588_ = v___x_1342_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_k_1577_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_v_1578_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v___x_1586_);
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
else
{
lean_object* v_r_1599_; 
v_r_1599_ = lean_ctor_get(v_impl_1485_, 4);
lean_inc(v_r_1599_);
if (lean_obj_tag(v_r_1599_) == 0)
{
lean_object* v_k_1600_; lean_object* v_v_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1612_; 
v_k_1600_ = lean_ctor_get(v_impl_1485_, 1);
v_v_1601_ = lean_ctor_get(v_impl_1485_, 2);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_impl_1485_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; 
v_unused_1613_ = lean_ctor_get(v_impl_1485_, 4);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_impl_1485_, 3);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_impl_1485_, 0);
lean_dec(v_unused_1615_);
v___x_1603_ = v_impl_1485_;
v_isShared_1604_ = v_isSharedCheck_1612_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_v_1601_);
lean_inc(v_k_1600_);
lean_dec(v_impl_1485_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1612_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_unsigned_to_nat(3u);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 4, v_l_1570_);
lean_ctor_set(v___x_1603_, 2, v_v_1338_);
lean_ctor_set(v___x_1603_, 1, v_k_1337_);
lean_ctor_set(v___x_1603_, 0, v___x_1486_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_l_1570_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_l_1570_);
v___x_1607_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 4, v_r_1599_);
lean_ctor_set(v___x_1342_, 3, v___x_1607_);
lean_ctor_set(v___x_1342_, 2, v_v_1601_);
lean_ctor_set(v___x_1342_, 1, v_k_1600_);
lean_ctor_set(v___x_1342_, 0, v___x_1605_);
v___x_1609_ = v___x_1342_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_k_1600_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_v_1601_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_r_1599_);
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
else
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1616_ = lean_unsigned_to_nat(2u);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 4, v_impl_1485_);
lean_ctor_set(v___x_1342_, 3, v_r_1599_);
lean_ctor_set(v___x_1342_, 0, v___x_1616_);
v___x_1618_ = v___x_1342_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_k_1337_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_v_1338_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_r_1599_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_impl_1485_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
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
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_unsigned_to_nat(1u);
v___x_1622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
lean_ctor_set(v___x_1622_, 1, v_k_1333_);
lean_ctor_set(v___x_1622_, 2, v_v_1334_);
lean_ctor_set(v___x_1622_, 3, v_t_1335_);
lean_ctor_set(v___x_1622_, 4, v_t_1335_);
return v___x_1622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(lean_object* v_k_1623_, lean_object* v_x_1624_){
_start:
{
if (lean_obj_tag(v_x_1624_) == 0)
{
lean_object* v___x_1625_; 
lean_dec_ref(v_k_1623_);
v___x_1625_ = lean_box(0);
return v___x_1625_;
}
else
{
lean_object* v_val_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_val_1626_ = lean_ctor_get(v_x_1624_, 0);
lean_inc(v_val_1626_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v_k_1623_);
lean_ctor_set(v___x_1627_, 1, v_val_1626_);
v___x_1628_ = lean_box(0);
v___x_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4___boxed(lean_object* v_k_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v_k_1630_, v_x_1631_);
lean_dec(v_x_1631_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(size_t v_sz_1633_, size_t v_i_1634_, lean_object* v_bs_1635_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_usize_dec_lt(v_i_1634_, v_sz_1633_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_bs_1635_);
return v___x_1637_;
}
else
{
lean_object* v_v_1638_; lean_object* v___x_1639_; 
v_v_1638_ = lean_array_uget_borrowed(v_bs_1635_, v_i_1634_);
lean_inc(v_v_1638_);
v___x_1639_ = l_Lean_Lsp_instFromJsonCallHierarchyIncomingCall_fromJson(v_v_1638_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v_bs_1635_);
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1649_; lean_object* v_bs_x27_1650_; size_t v___x_1651_; size_t v___x_1652_; lean_object* v___x_1653_; 
v_a_1648_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1649_ = lean_unsigned_to_nat(0u);
v_bs_x27_1650_ = lean_array_uset(v_bs_1635_, v_i_1634_, v___x_1649_);
v___x_1651_ = ((size_t)1ULL);
v___x_1652_ = lean_usize_add(v_i_1634_, v___x_1651_);
v___x_1653_ = lean_array_uset(v_bs_x27_1650_, v_i_1634_, v_a_1648_);
v_i_1634_ = v___x_1652_;
v_bs_1635_ = v___x_1653_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_sz_1655_, lean_object* v_i_1656_, lean_object* v_bs_1657_){
_start:
{
size_t v_sz_boxed_1658_; size_t v_i_boxed_1659_; lean_object* v_res_1660_; 
v_sz_boxed_1658_ = lean_unbox_usize(v_sz_1655_);
lean_dec(v_sz_1655_);
v_i_boxed_1659_ = lean_unbox_usize(v_i_1656_);
lean_dec(v_i_1656_);
v_res_1660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_boxed_1658_, v_i_boxed_1659_, v_bs_1657_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(lean_object* v_x_1661_){
_start:
{
if (lean_obj_tag(v_x_1661_) == 4)
{
lean_object* v_elems_1662_; size_t v_sz_1663_; size_t v___x_1664_; lean_object* v___x_1665_; 
v_elems_1662_ = lean_ctor_get(v_x_1661_, 0);
lean_inc_ref(v_elems_1662_);
lean_dec_ref_known(v_x_1661_, 1);
v_sz_1663_ = lean_array_size(v_elems_1662_);
v___x_1664_ = ((size_t)0ULL);
v___x_1665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_1663_, v___x_1664_, v_elems_1662_);
return v___x_1665_;
}
else
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1666_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1667_ = lean_unsigned_to_nat(80u);
v___x_1668_ = l_Lean_Json_pretty(v_x_1661_, v___x_1667_);
v___x_1669_ = lean_string_append(v___x_1666_, v___x_1668_);
lean_dec_ref(v___x_1668_);
v___x_1670_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1671_ = lean_string_append(v___x_1669_, v___x_1670_);
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(lean_object* v_x_1675_){
_start:
{
if (lean_obj_tag(v_x_1675_) == 0)
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0));
return v___x_1676_;
}
else
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(v_x_1675_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
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
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1694_; 
v_a_1686_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1688_ = v___x_1677_;
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1677_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_a_1686_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(lean_object* v_expectedID_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Lsp_Ipc_stdout(v_a_1696_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1842_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1842_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1842_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_IO_FS_Stream_readLspMessage(v_a_1699_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1833_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1833_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1833_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___y_1709_; lean_object* v___y_1710_; 
switch(lean_obj_tag(v_a_1704_))
{
case 2:
{
lean_object* v_id_1716_; lean_object* v_result_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1761_; 
v_id_1716_ = lean_ctor_get(v_a_1704_, 0);
v_result_1717_ = lean_ctor_get(v_a_1704_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_a_1704_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1719_ = v_a_1704_;
v_isShared_1720_ = v_isSharedCheck_1761_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_result_1717_);
lean_inc(v_id_1716_);
lean_dec(v_a_1704_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1761_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
uint8_t v___x_1721_; 
v___x_1721_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_1716_, v_expectedID_1695_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; lean_object* v___y_1724_; 
lean_del_object(v___x_1719_);
lean_dec(v_result_1717_);
lean_del_object(v___x_1701_);
v___x_1722_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_1695_))
{
case 0:
{
lean_object* v_s_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v_s_1735_ = lean_ctor_get(v_expectedID_1695_, 0);
lean_inc_ref(v_s_1735_);
lean_dec_ref_known(v_expectedID_1695_, 1);
v___x_1736_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1737_ = lean_string_append(v___x_1736_, v_s_1735_);
lean_dec_ref(v_s_1735_);
v___x_1738_ = lean_string_append(v___x_1737_, v___x_1736_);
v___y_1724_ = v___x_1738_;
goto v___jp_1723_;
}
case 1:
{
lean_object* v_n_1739_; lean_object* v___x_1740_; 
v_n_1739_ = lean_ctor_get(v_expectedID_1695_, 0);
lean_inc_ref(v_n_1739_);
lean_dec_ref_known(v_expectedID_1695_, 1);
v___x_1740_ = l_Lean_JsonNumber_toString(v_n_1739_);
v___y_1724_ = v___x_1740_;
goto v___jp_1723_;
}
default: 
{
lean_object* v___x_1741_; 
v___x_1741_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1724_ = v___x_1741_;
goto v___jp_1723_;
}
}
v___jp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_string_append(v___x_1722_, v___y_1724_);
lean_dec_ref(v___y_1724_);
v___x_1726_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_1727_ = lean_string_append(v___x_1725_, v___x_1726_);
switch(lean_obj_tag(v_id_1716_))
{
case 0:
{
lean_object* v_s_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_s_1728_ = lean_ctor_get(v_id_1716_, 0);
lean_inc_ref(v_s_1728_);
lean_dec_ref_known(v_id_1716_, 1);
v___x_1729_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1730_ = lean_string_append(v___x_1729_, v_s_1728_);
lean_dec_ref(v_s_1728_);
v___x_1731_ = lean_string_append(v___x_1730_, v___x_1729_);
v___y_1709_ = v___x_1727_;
v___y_1710_ = v___x_1731_;
goto v___jp_1708_;
}
case 1:
{
lean_object* v_n_1732_; lean_object* v___x_1733_; 
v_n_1732_ = lean_ctor_get(v_id_1716_, 0);
lean_inc_ref(v_n_1732_);
lean_dec_ref_known(v_id_1716_, 1);
v___x_1733_ = l_Lean_JsonNumber_toString(v_n_1732_);
v___y_1709_ = v___x_1727_;
v___y_1710_ = v___x_1733_;
goto v___jp_1708_;
}
default: 
{
lean_object* v___x_1734_; 
v___x_1734_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1709_ = v___x_1727_;
v___y_1710_ = v___x_1734_;
goto v___jp_1708_;
}
}
}
}
else
{
lean_object* v___x_1742_; 
lean_dec(v_id_1716_);
lean_del_object(v___x_1706_);
lean_inc(v_result_1717_);
v___x_1742_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(v_result_1717_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
lean_del_object(v___x_1719_);
lean_dec(v_expectedID_1695_);
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
v___x_1744_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_1745_ = l_Lean_Json_compress(v_result_1717_);
v___x_1746_ = lean_string_append(v___x_1744_, v___x_1745_);
lean_dec_ref(v___x_1745_);
v___x_1747_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_1748_ = lean_string_append(v___x_1746_, v___x_1747_);
v___x_1749_ = lean_string_append(v___x_1748_, v_a_1743_);
lean_dec(v_a_1743_);
v___x_1750_ = lean_mk_io_user_error(v___x_1749_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set_tag(v___x_1701_, 1);
lean_ctor_set(v___x_1701_, 0, v___x_1750_);
v___x_1752_ = v___x_1701_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; 
lean_dec(v_result_1717_);
v_a_1754_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1742_, 1);
if (v_isShared_1720_ == 0)
{
lean_ctor_set_tag(v___x_1719_, 0);
lean_ctor_set(v___x_1719_, 1, v_a_1754_);
lean_ctor_set(v___x_1719_, 0, v_expectedID_1695_);
v___x_1756_ = v___x_1719_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_expectedID_1695_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_a_1754_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1758_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1756_);
v___x_1758_ = v___x_1701_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_1762_; uint8_t v_code_1763_; lean_object* v_message_1764_; lean_object* v_data_x3f_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___x_1797_; lean_object* v___y_1799_; 
lean_del_object(v___x_1706_);
lean_dec(v_expectedID_1695_);
v_id_1762_ = lean_ctor_get(v_a_1704_, 0);
lean_inc(v_id_1762_);
v_code_1763_ = lean_ctor_get_uint8(v_a_1704_, sizeof(void*)*3);
v_message_1764_ = lean_ctor_get(v_a_1704_, 1);
lean_inc_ref(v_message_1764_);
v_data_x3f_1765_ = lean_ctor_get(v_a_1704_, 2);
lean_inc(v_data_x3f_1765_);
lean_dec_ref_known(v_a_1704_, 3);
v___x_1766_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_1767_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_1797_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_1762_))
{
case 0:
{
lean_object* v_s_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
v_s_1815_ = lean_ctor_get(v_id_1762_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_id_1762_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v_id_1762_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_s_1815_);
lean_dec(v_id_1762_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 3);
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_s_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
v___y_1799_ = v___x_1820_;
goto v___jp_1798_;
}
}
}
case 1:
{
lean_object* v_n_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
v_n_1823_ = lean_ctor_get(v_id_1762_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_id_1762_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v_id_1762_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_n_1823_);
lean_dec(v_id_1762_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set_tag(v___x_1825_, 2);
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_n_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
v___y_1799_ = v___x_1828_;
goto v___jp_1798_;
}
}
}
default: 
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_box(0);
v___y_1799_ = v___x_1831_;
goto v___jp_1798_;
}
}
v___jp_1768_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
lean_inc(v___y_1772_);
lean_inc_ref(v___y_1771_);
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___y_1771_);
lean_ctor_set(v___x_1773_, 1, v___y_1772_);
v___x_1774_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_1775_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1775_, 0, v_message_1764_);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_box(0);
v___x_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___x_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1773_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_1781_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_1780_, v_data_x3f_1765_);
lean_dec(v_data_x3f_1765_);
v___x_1782_ = l_List_appendTR___redArg(v___x_1779_, v___x_1781_);
v___x_1783_ = l_Lean_Json_mkObj(v___x_1782_);
lean_dec(v___x_1782_);
lean_inc_ref(v___y_1770_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___y_1770_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___x_1777_);
v___x_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___y_1769_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1767_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_Json_mkObj(v___x_1787_);
lean_dec_ref_known(v___x_1787_, 2);
v___x_1789_ = l_Lean_Json_compress(v___x_1788_);
v___x_1790_ = lean_string_append(v___x_1766_, v___x_1789_);
lean_dec_ref(v___x_1789_);
v___x_1791_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1792_ = lean_string_append(v___x_1790_, v___x_1791_);
v___x_1793_ = lean_mk_io_user_error(v___x_1792_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set_tag(v___x_1701_, 1);
lean_ctor_set(v___x_1701_, 0, v___x_1793_);
v___x_1795_ = v___x_1701_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
v___jp_1798_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1797_);
lean_ctor_set(v___x_1800_, 1, v___y_1799_);
v___x_1801_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_1802_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_1763_)
{
case 0:
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1803_;
goto v___jp_1768_;
}
case 1:
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1804_;
goto v___jp_1768_;
}
case 2:
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1805_;
goto v___jp_1768_;
}
case 3:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1806_;
goto v___jp_1768_;
}
case 4:
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1807_;
goto v___jp_1768_;
}
case 5:
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1808_;
goto v___jp_1768_;
}
case 6:
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1809_;
goto v___jp_1768_;
}
case 7:
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1810_;
goto v___jp_1768_;
}
case 8:
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1811_;
goto v___jp_1768_;
}
case 9:
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1812_;
goto v___jp_1768_;
}
case 10:
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1813_;
goto v___jp_1768_;
}
default: 
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_1769_ = v___x_1800_;
v___y_1770_ = v___x_1801_;
v___y_1771_ = v___x_1802_;
v___y_1772_ = v___x_1814_;
goto v___jp_1768_;
}
}
}
}
default: 
{
lean_del_object(v___x_1706_);
lean_dec(v_a_1704_);
lean_del_object(v___x_1701_);
goto _start;
}
}
v___jp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1711_ = lean_string_append(v___y_1709_, v___y_1710_);
lean_dec_ref(v___y_1710_);
v___x_1712_ = lean_mk_io_user_error(v___x_1711_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 1);
lean_ctor_set(v___x_1706_, 0, v___x_1712_);
v___x_1714_ = v___x_1706_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
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
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_del_object(v___x_1701_);
lean_dec(v_expectedID_1695_);
v_a_1834_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1703_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1703_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_expectedID_1695_);
v_a_1843_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1698_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1698_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2___boxed(lean_object* v_expectedID_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v_expectedID_1851_, v_a_1852_);
lean_dec_ref(v_a_1852_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(lean_object* v_v_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = l_Lean_Lsp_instToJsonCallHierarchyIncomingCallsParams_toJson(v_v_1855_);
v___x_1857_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(lean_object* v_h_1858_, lean_object* v_r_1859_){
_start:
{
lean_object* v_id_1861_; lean_object* v_method_1862_; lean_object* v_param_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1883_; 
v_id_1861_ = lean_ctor_get(v_r_1859_, 0);
v_method_1862_ = lean_ctor_get(v_r_1859_, 1);
v_param_1863_ = lean_ctor_get(v_r_1859_, 2);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_r_1859_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1865_ = v_r_1859_;
v_isShared_1866_ = v_isSharedCheck_1883_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_param_1863_);
lean_inc(v_method_1862_);
lean_inc(v_id_1861_);
lean_dec(v_r_1859_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1883_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___y_1868_; lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(v_param_1863_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v___x_1874_; 
lean_dec_ref_known(v___x_1873_, 1);
v___x_1874_ = lean_box(0);
v___y_1868_ = v___x_1874_;
goto v___jp_1867_;
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_a_1875_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1873_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1873_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
v___y_1868_ = v___x_1880_;
goto v___jp_1867_;
}
}
}
v___jp_1867_:
{
lean_object* v___x_1870_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 2, v___y_1868_);
v___x_1870_ = v___x_1865_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_id_1861_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_method_1862_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v___y_1868_);
v___x_1870_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_IO_FS_Stream_writeLspMessage(v_h_1858_, v___x_1870_);
return v___x_1871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1___boxed(lean_object* v_h_1884_, lean_object* v_r_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_h_1884_, v_r_1885_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(lean_object* v_r_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v_a_1892_; lean_object* v___x_1893_; 
v___x_1891_ = l_Lean_Lsp_Ipc_stdin(v_a_1889_);
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref(v___x_1891_);
v___x_1893_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_a_1892_, v_r_1888_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1___boxed(lean_object* v_r_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v_r_1894_, v_a_1895_);
lean_dec_ref(v_a_1895_);
return v_res_1897_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(lean_object* v_k_1898_, lean_object* v_t_1899_){
_start:
{
if (lean_obj_tag(v_t_1899_) == 0)
{
lean_object* v_k_1900_; lean_object* v_l_1901_; lean_object* v_r_1902_; uint8_t v___x_1903_; 
v_k_1900_ = lean_ctor_get(v_t_1899_, 1);
v_l_1901_ = lean_ctor_get(v_t_1899_, 3);
v_r_1902_ = lean_ctor_get(v_t_1899_, 4);
v___x_1903_ = lean_string_compare(v_k_1898_, v_k_1900_);
switch(v___x_1903_)
{
case 0:
{
v_t_1899_ = v_l_1901_;
goto _start;
}
case 1:
{
uint8_t v___x_1905_; 
v___x_1905_ = 1;
return v___x_1905_;
}
default: 
{
v_t_1899_ = v_r_1902_;
goto _start;
}
}
}
else
{
uint8_t v___x_1907_; 
v___x_1907_ = 0;
return v___x_1907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg___boxed(lean_object* v_k_1908_, lean_object* v_t_1909_){
_start:
{
uint8_t v_res_1910_; lean_object* v_r_1911_; 
v_res_1910_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_1908_, v_t_1909_);
lean_dec(v_t_1909_);
lean_dec_ref(v_k_1908_);
v_r_1911_ = lean_box(v_res_1910_);
return v_r_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(lean_object* v_requestNo_1919_, lean_object* v_item_1920_, lean_object* v_fromRanges_1921_, lean_object* v_visited_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_name_1925_; uint8_t v___x_1926_; 
v_name_1925_ = lean_ctor_get(v_item_1920_, 0);
v___x_1926_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_1925_, v_visited_1922_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_inc(v_requestNo_1919_);
v___x_1927_ = l_Lean_JsonNumber_fromNat(v_requestNo_1919_);
v___x_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
v___x_1929_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_1920_);
lean_inc_ref(v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
lean_ctor_set(v___x_1930_, 2, v_item_1920_);
v___x_1931_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v___x_1930_, v_a_1923_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v___x_1932_; 
lean_dec_ref_known(v___x_1931_, 1);
v___x_1932_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v___x_1928_, v_a_1923_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1970_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
if (v___x_1926_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_box(0);
lean_inc_ref(v_name_1925_);
v___x_1977_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_1925_, v___x_1976_, v_visited_1922_);
v___y_1970_ = v___x_1977_;
goto v___jp_1969_;
}
else
{
v___y_1970_ = v_visited_1922_;
goto v___jp_1969_;
}
v___jp_1934_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; size_t v_sz_1940_; size_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1938_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___y_1935_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v_sz_1940_ = lean_array_size(v___y_1937_);
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___y_1936_, v___y_1937_, v_sz_1940_, v___x_1941_, v___x_1939_, v_a_1923_);
lean_dec_ref(v___y_1937_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1960_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1960_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1960_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_fst_1947_; lean_object* v_snd_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1959_; 
v_fst_1947_ = lean_ctor_get(v_a_1943_, 0);
v_snd_1948_ = lean_ctor_get(v_a_1943_, 1);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_a_1943_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1950_ = v_a_1943_;
v_isShared_1951_ = v_isSharedCheck_1959_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_snd_1948_);
lean_inc(v_fst_1947_);
lean_dec(v_a_1943_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1959_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1952_, 0, v_item_1920_);
lean_ctor_set(v___x_1952_, 1, v_fromRanges_1921_);
lean_ctor_set(v___x_1952_, 2, v_snd_1948_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v_fst_1947_);
lean_ctor_set(v___x_1950_, 0, v___x_1952_);
v___x_1954_ = v___x_1950_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_fst_1947_);
v___x_1954_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1956_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1954_);
v___x_1956_ = v___x_1945_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_fromRanges_1921_);
lean_dec_ref(v_item_1920_);
v_a_1961_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1942_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1942_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
v___jp_1969_:
{
lean_object* v_result_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_result_1971_ = lean_ctor_get(v_a_1933_, 1);
lean_inc(v_result_1971_);
lean_dec(v_a_1933_);
v___x_1972_ = lean_unsigned_to_nat(1u);
v___x_1973_ = lean_nat_add(v_requestNo_1919_, v___x_1972_);
lean_dec(v_requestNo_1919_);
if (lean_obj_tag(v_result_1971_) == 0)
{
lean_object* v___x_1974_; 
v___x_1974_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2));
v___y_1935_ = v___x_1973_;
v___y_1936_ = v___y_1970_;
v___y_1937_ = v___x_1974_;
goto v___jp_1934_;
}
else
{
lean_object* v_val_1975_; 
v_val_1975_ = lean_ctor_get(v_result_1971_, 0);
lean_inc(v_val_1975_);
lean_dec_ref_known(v_result_1971_, 1);
v___y_1935_ = v___x_1973_;
v___y_1936_ = v___y_1970_;
v___y_1937_ = v_val_1975_;
goto v___jp_1934_;
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v_visited_1922_);
lean_dec_ref(v_fromRanges_1921_);
lean_dec_ref(v_item_1920_);
lean_dec(v_requestNo_1919_);
v_a_1978_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1932_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1932_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref_known(v___x_1928_, 1);
lean_dec(v_visited_1922_);
lean_dec_ref(v_fromRanges_1921_);
lean_dec_ref(v_item_1920_);
lean_dec(v_requestNo_1919_);
v_a_1986_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1931_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1931_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_dec(v_visited_1922_);
lean_dec_ref(v_fromRanges_1921_);
v___x_1994_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_1995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1995_, 0, v_item_1920_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
lean_ctor_set(v___x_1995_, 2, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
lean_ctor_set(v___x_1996_, 1, v_requestNo_1919_);
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(lean_object* v___x_1998_, lean_object* v_as_1999_, size_t v_sz_2000_, size_t v_i_2001_, lean_object* v_b_2002_, lean_object* v___y_2003_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_lt(v_i_2001_, v_sz_2000_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_dec(v___x_1998_);
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_b_2002_);
return v___x_2006_;
}
else
{
lean_object* v_fst_2007_; lean_object* v_snd_2008_; lean_object* v_a_2009_; lean_object* v_from_2010_; lean_object* v_fromRanges_2011_; lean_object* v___x_2012_; 
v_fst_2007_ = lean_ctor_get(v_b_2002_, 0);
lean_inc(v_fst_2007_);
v_snd_2008_ = lean_ctor_get(v_b_2002_, 1);
lean_inc(v_snd_2008_);
lean_dec_ref(v_b_2002_);
v_a_2009_ = lean_array_uget_borrowed(v_as_1999_, v_i_2001_);
v_from_2010_ = lean_ctor_get(v_a_2009_, 0);
v_fromRanges_2011_ = lean_ctor_get(v_a_2009_, 1);
lean_inc(v___x_1998_);
lean_inc_ref(v_fromRanges_2011_);
lean_inc_ref(v_from_2010_);
v___x_2012_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2007_, v_from_2010_, v_fromRanges_2011_, v___x_1998_, v___y_2003_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v_fst_2014_; lean_object* v_snd_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2026_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v_fst_2014_ = lean_ctor_get(v_a_2013_, 0);
v_snd_2015_ = lean_ctor_get(v_a_2013_, 1);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_a_2013_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2017_ = v_a_2013_;
v_isShared_2018_ = v_isSharedCheck_2026_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_snd_2015_);
lean_inc(v_fst_2014_);
lean_dec(v_a_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2026_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_array_push(v_snd_2008_, v_fst_2014_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 1, v___x_2019_);
lean_ctor_set(v___x_2017_, 0, v_snd_2015_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_snd_2015_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
size_t v___x_2022_; size_t v___x_2023_; 
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_2001_, v___x_2022_);
v_i_2001_ = v___x_2023_;
v_b_2002_ = v___x_2021_;
goto _start;
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_snd_2008_);
lean_dec(v___x_1998_);
v_a_2027_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2012_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2012_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3___boxed(lean_object* v___x_2035_, lean_object* v_as_2036_, lean_object* v_sz_2037_, lean_object* v_i_2038_, lean_object* v_b_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
size_t v_sz_boxed_2042_; size_t v_i_boxed_2043_; lean_object* v_res_2044_; 
v_sz_boxed_2042_ = lean_unbox_usize(v_sz_2037_);
lean_dec(v_sz_2037_);
v_i_boxed_2043_ = lean_unbox_usize(v_i_2038_);
lean_dec(v_i_2038_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___x_2035_, v_as_2036_, v_sz_boxed_2042_, v_i_boxed_2043_, v_b_2039_, v___y_2040_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v_as_2036_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___boxed(lean_object* v_requestNo_2045_, lean_object* v_item_2046_, lean_object* v_fromRanges_2047_, lean_object* v_visited_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_requestNo_2045_, v_item_2046_, v_fromRanges_2047_, v_visited_2048_, v_a_2049_);
lean_dec_ref(v_a_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(lean_object* v_00_u03b2_2052_, lean_object* v_k_2053_, lean_object* v_t_2054_){
_start:
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_2053_, v_t_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___boxed(lean_object* v_00_u03b2_2056_, lean_object* v_k_2057_, lean_object* v_t_2058_){
_start:
{
uint8_t v_res_2059_; lean_object* v_r_2060_; 
v_res_2059_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(v_00_u03b2_2056_, v_k_2057_, v_t_2058_);
lean_dec(v_t_2058_);
lean_dec_ref(v_k_2057_);
v_r_2060_ = lean_box(v_res_2059_);
return v_r_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4(lean_object* v_00_u03b2_2061_, lean_object* v_k_2062_, lean_object* v_v_2063_, lean_object* v_t_2064_, lean_object* v_hl_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_2062_, v_v_2063_, v_t_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2067_, size_t v_i_2068_, lean_object* v_bs_2069_){
_start:
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_usize_dec_lt(v_i_2068_, v_sz_2067_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_bs_2069_);
return v___x_2071_;
}
else
{
lean_object* v_v_2072_; lean_object* v___x_2073_; 
v_v_2072_ = lean_array_uget_borrowed(v_bs_2069_, v_i_2068_);
lean_inc(v_v_2072_);
v___x_2073_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v_v_2072_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref(v_bs_2069_);
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2083_; lean_object* v_bs_x27_2084_; size_t v___x_2085_; size_t v___x_2086_; lean_object* v___x_2087_; 
v_a_2082_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2073_, 1);
v___x_2083_ = lean_unsigned_to_nat(0u);
v_bs_x27_2084_ = lean_array_uset(v_bs_2069_, v_i_2068_, v___x_2083_);
v___x_2085_ = ((size_t)1ULL);
v___x_2086_ = lean_usize_add(v_i_2068_, v___x_2085_);
v___x_2087_ = lean_array_uset(v_bs_x27_2084_, v_i_2068_, v_a_2082_);
v_i_2068_ = v___x_2086_;
v_bs_2069_ = v___x_2087_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2089_, lean_object* v_i_2090_, lean_object* v_bs_2091_){
_start:
{
size_t v_sz_boxed_2092_; size_t v_i_boxed_2093_; lean_object* v_res_2094_; 
v_sz_boxed_2092_ = lean_unbox_usize(v_sz_2089_);
lean_dec(v_sz_2089_);
v_i_boxed_2093_ = lean_unbox_usize(v_i_2090_);
lean_dec(v_i_2090_);
v_res_2094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2092_, v_i_boxed_2093_, v_bs_2091_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(lean_object* v_x_2095_){
_start:
{
if (lean_obj_tag(v_x_2095_) == 4)
{
lean_object* v_elems_2096_; size_t v_sz_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
v_elems_2096_ = lean_ctor_get(v_x_2095_, 0);
lean_inc_ref(v_elems_2096_);
lean_dec_ref_known(v_x_2095_, 1);
v_sz_2097_ = lean_array_size(v_elems_2096_);
v___x_2098_ = ((size_t)0ULL);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_2097_, v___x_2098_, v_elems_2096_);
return v___x_2099_;
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2100_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2101_ = lean_unsigned_to_nat(80u);
v___x_2102_ = l_Lean_Json_pretty(v_x_2095_, v___x_2101_);
v___x_2103_ = lean_string_append(v___x_2100_, v___x_2102_);
lean_dec_ref(v___x_2102_);
v___x_2104_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2105_ = lean_string_append(v___x_2103_, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
return v___x_2106_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(lean_object* v_x_2109_){
_start:
{
if (lean_obj_tag(v_x_2109_) == 0)
{
lean_object* v___x_2110_; 
v___x_2110_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0));
return v___x_2110_;
}
else
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(v_x_2109_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2128_; 
v_a_2120_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2122_ = v___x_2111_;
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2111_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v_a_2120_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2124_);
v___x_2126_ = v___x_2122_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(lean_object* v_expectedID_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Lsp_Ipc_stdout(v_a_2130_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2276_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2276_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2276_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_IO_FS_Stream_readLspMessage(v_a_2133_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2267_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2267_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2267_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___y_2143_; lean_object* v___y_2144_; 
switch(lean_obj_tag(v_a_2138_))
{
case 2:
{
lean_object* v_id_2150_; lean_object* v_result_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2195_; 
v_id_2150_ = lean_ctor_get(v_a_2138_, 0);
v_result_2151_ = lean_ctor_get(v_a_2138_, 1);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_a_2138_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2153_ = v_a_2138_;
v_isShared_2154_ = v_isSharedCheck_2195_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_result_2151_);
lean_inc(v_id_2150_);
lean_dec(v_a_2138_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2195_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
uint8_t v___x_2155_; 
v___x_2155_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2150_, v_expectedID_2129_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___y_2158_; 
lean_del_object(v___x_2153_);
lean_dec(v_result_2151_);
lean_del_object(v___x_2135_);
v___x_2156_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2129_))
{
case 0:
{
lean_object* v_s_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_s_2169_ = lean_ctor_get(v_expectedID_2129_, 0);
lean_inc_ref(v_s_2169_);
lean_dec_ref_known(v_expectedID_2129_, 1);
v___x_2170_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2171_ = lean_string_append(v___x_2170_, v_s_2169_);
lean_dec_ref(v_s_2169_);
v___x_2172_ = lean_string_append(v___x_2171_, v___x_2170_);
v___y_2158_ = v___x_2172_;
goto v___jp_2157_;
}
case 1:
{
lean_object* v_n_2173_; lean_object* v___x_2174_; 
v_n_2173_ = lean_ctor_get(v_expectedID_2129_, 0);
lean_inc_ref(v_n_2173_);
lean_dec_ref_known(v_expectedID_2129_, 1);
v___x_2174_ = l_Lean_JsonNumber_toString(v_n_2173_);
v___y_2158_ = v___x_2174_;
goto v___jp_2157_;
}
default: 
{
lean_object* v___x_2175_; 
v___x_2175_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2158_ = v___x_2175_;
goto v___jp_2157_;
}
}
v___jp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = lean_string_append(v___x_2156_, v___y_2158_);
lean_dec_ref(v___y_2158_);
v___x_2160_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2161_ = lean_string_append(v___x_2159_, v___x_2160_);
switch(lean_obj_tag(v_id_2150_))
{
case 0:
{
lean_object* v_s_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v_s_2162_ = lean_ctor_get(v_id_2150_, 0);
lean_inc_ref(v_s_2162_);
lean_dec_ref_known(v_id_2150_, 1);
v___x_2163_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2164_ = lean_string_append(v___x_2163_, v_s_2162_);
lean_dec_ref(v_s_2162_);
v___x_2165_ = lean_string_append(v___x_2164_, v___x_2163_);
v___y_2143_ = v___x_2161_;
v___y_2144_ = v___x_2165_;
goto v___jp_2142_;
}
case 1:
{
lean_object* v_n_2166_; lean_object* v___x_2167_; 
v_n_2166_ = lean_ctor_get(v_id_2150_, 0);
lean_inc_ref(v_n_2166_);
lean_dec_ref_known(v_id_2150_, 1);
v___x_2167_ = l_Lean_JsonNumber_toString(v_n_2166_);
v___y_2143_ = v___x_2161_;
v___y_2144_ = v___x_2167_;
goto v___jp_2142_;
}
default: 
{
lean_object* v___x_2168_; 
v___x_2168_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2143_ = v___x_2161_;
v___y_2144_ = v___x_2168_;
goto v___jp_2142_;
}
}
}
}
else
{
lean_object* v___x_2176_; 
lean_dec(v_id_2150_);
lean_del_object(v___x_2140_);
lean_inc(v_result_2151_);
v___x_2176_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(v_result_2151_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
lean_del_object(v___x_2153_);
lean_dec(v_expectedID_2129_);
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2179_ = l_Lean_Json_compress(v_result_2151_);
v___x_2180_ = lean_string_append(v___x_2178_, v___x_2179_);
lean_dec_ref(v___x_2179_);
v___x_2181_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2182_ = lean_string_append(v___x_2180_, v___x_2181_);
v___x_2183_ = lean_string_append(v___x_2182_, v_a_2177_);
lean_dec(v_a_2177_);
v___x_2184_ = lean_mk_io_user_error(v___x_2183_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 1);
lean_ctor_set(v___x_2135_, 0, v___x_2184_);
v___x_2186_ = v___x_2135_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; 
lean_dec(v_result_2151_);
v_a_2188_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2176_, 1);
if (v_isShared_2154_ == 0)
{
lean_ctor_set_tag(v___x_2153_, 0);
lean_ctor_set(v___x_2153_, 1, v_a_2188_);
lean_ctor_set(v___x_2153_, 0, v_expectedID_2129_);
v___x_2190_ = v___x_2153_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_expectedID_2129_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_a_2188_);
v___x_2190_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2192_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2190_);
v___x_2192_ = v___x_2135_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2196_; uint8_t v_code_2197_; lean_object* v_message_2198_; lean_object* v_data_x3f_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___x_2231_; lean_object* v___y_2233_; 
lean_del_object(v___x_2140_);
lean_dec(v_expectedID_2129_);
v_id_2196_ = lean_ctor_get(v_a_2138_, 0);
lean_inc(v_id_2196_);
v_code_2197_ = lean_ctor_get_uint8(v_a_2138_, sizeof(void*)*3);
v_message_2198_ = lean_ctor_get(v_a_2138_, 1);
lean_inc_ref(v_message_2198_);
v_data_x3f_2199_ = lean_ctor_get(v_a_2138_, 2);
lean_inc(v_data_x3f_2199_);
lean_dec_ref_known(v_a_2138_, 3);
v___x_2200_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2201_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2231_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2196_))
{
case 0:
{
lean_object* v_s_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
v_s_2249_ = lean_ctor_get(v_id_2196_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_id_2196_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v_id_2196_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_s_2249_);
lean_dec(v_id_2196_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
lean_ctor_set_tag(v___x_2251_, 3);
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_s_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
v___y_2233_ = v___x_2254_;
goto v___jp_2232_;
}
}
}
case 1:
{
lean_object* v_n_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
v_n_2257_ = lean_ctor_get(v_id_2196_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_id_2196_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v_id_2196_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_n_2257_);
lean_dec(v_id_2196_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 2);
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_n_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
v___y_2233_ = v___x_2262_;
goto v___jp_2232_;
}
}
}
default: 
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_box(0);
v___y_2233_ = v___x_2265_;
goto v___jp_2232_;
}
}
v___jp_2202_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
lean_inc(v___y_2206_);
lean_inc_ref(v___y_2205_);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___y_2205_);
lean_ctor_set(v___x_2207_, 1, v___y_2206_);
v___x_2208_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2209_, 0, v_message_2198_);
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2208_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2207_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2215_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2214_, v_data_x3f_2199_);
lean_dec(v_data_x3f_2199_);
v___x_2216_ = l_List_appendTR___redArg(v___x_2213_, v___x_2215_);
v___x_2217_ = l_Lean_Json_mkObj(v___x_2216_);
lean_dec(v___x_2216_);
lean_inc_ref(v___y_2204_);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___y_2204_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v___x_2211_);
v___x_2220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___y_2203_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2201_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = l_Lean_Json_mkObj(v___x_2221_);
lean_dec_ref_known(v___x_2221_, 2);
v___x_2223_ = l_Lean_Json_compress(v___x_2222_);
v___x_2224_ = lean_string_append(v___x_2200_, v___x_2223_);
lean_dec_ref(v___x_2223_);
v___x_2225_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2226_ = lean_string_append(v___x_2224_, v___x_2225_);
v___x_2227_ = lean_mk_io_user_error(v___x_2226_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 1);
lean_ctor_set(v___x_2135_, 0, v___x_2227_);
v___x_2229_ = v___x_2135_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
v___jp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2231_);
lean_ctor_set(v___x_2234_, 1, v___y_2233_);
v___x_2235_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2236_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2197_)
{
case 0:
{
lean_object* v___x_2237_; 
v___x_2237_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2237_;
goto v___jp_2202_;
}
case 1:
{
lean_object* v___x_2238_; 
v___x_2238_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2238_;
goto v___jp_2202_;
}
case 2:
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2239_;
goto v___jp_2202_;
}
case 3:
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2240_;
goto v___jp_2202_;
}
case 4:
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2241_;
goto v___jp_2202_;
}
case 5:
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2242_;
goto v___jp_2202_;
}
case 6:
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2243_;
goto v___jp_2202_;
}
case 7:
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2244_;
goto v___jp_2202_;
}
case 8:
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2245_;
goto v___jp_2202_;
}
case 9:
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2246_;
goto v___jp_2202_;
}
case 10:
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2247_;
goto v___jp_2202_;
}
default: 
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2203_ = v___x_2234_;
v___y_2204_ = v___x_2235_;
v___y_2205_ = v___x_2236_;
v___y_2206_ = v___x_2248_;
goto v___jp_2202_;
}
}
}
}
default: 
{
lean_del_object(v___x_2140_);
lean_dec(v_a_2138_);
lean_del_object(v___x_2135_);
goto _start;
}
}
v___jp_2142_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2145_ = lean_string_append(v___y_2143_, v___y_2144_);
lean_dec_ref(v___y_2144_);
v___x_2146_ = lean_mk_io_user_error(v___x_2145_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set_tag(v___x_2140_, 1);
lean_ctor_set(v___x_2140_, 0, v___x_2146_);
v___x_2148_ = v___x_2140_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_del_object(v___x_2135_);
lean_dec(v_expectedID_2129_);
v_a_2268_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2137_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2137_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v_expectedID_2129_);
v_a_2277_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2132_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2132_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1___boxed(lean_object* v_expectedID_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v_expectedID_2285_, v_a_2286_);
lean_dec_ref(v_a_2286_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(lean_object* v_as_2289_, size_t v_sz_2290_, size_t v_i_2291_, lean_object* v_b_2292_, lean_object* v___y_2293_){
_start:
{
uint8_t v___x_2295_; 
v___x_2295_ = lean_usize_dec_lt(v_i_2291_, v_sz_2290_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v_b_2292_);
return v___x_2296_;
}
else
{
lean_object* v_fst_2297_; lean_object* v_snd_2298_; lean_object* v_a_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_fst_2297_ = lean_ctor_get(v_b_2292_, 0);
lean_inc(v_fst_2297_);
v_snd_2298_ = lean_ctor_get(v_b_2292_, 1);
lean_inc(v_snd_2298_);
lean_dec_ref(v_b_2292_);
v_a_2299_ = lean_array_uget_borrowed(v_as_2289_, v_i_2291_);
v___x_2300_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2301_ = lean_box(1);
lean_inc(v_a_2299_);
v___x_2302_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2297_, v_a_2299_, v___x_2300_, v___x_2301_, v___y_2293_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v_fst_2304_; lean_object* v_snd_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2316_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v_fst_2304_ = lean_ctor_get(v_a_2303_, 0);
v_snd_2305_ = lean_ctor_get(v_a_2303_, 1);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_a_2303_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2307_ = v_a_2303_;
v_isShared_2308_ = v_isSharedCheck_2316_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_snd_2305_);
lean_inc(v_fst_2304_);
lean_dec(v_a_2303_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2316_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2309_ = lean_array_push(v_snd_2298_, v_fst_2304_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 1, v___x_2309_);
lean_ctor_set(v___x_2307_, 0, v_snd_2305_);
v___x_2311_ = v___x_2307_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_snd_2305_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
size_t v___x_2312_; size_t v___x_2313_; 
v___x_2312_ = ((size_t)1ULL);
v___x_2313_ = lean_usize_add(v_i_2291_, v___x_2312_);
v_i_2291_ = v___x_2313_;
v_b_2292_ = v___x_2311_;
goto _start;
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec(v_snd_2298_);
v_a_2317_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2302_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2302_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2___boxed(lean_object* v_as_2325_, lean_object* v_sz_2326_, lean_object* v_i_2327_, lean_object* v_b_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
size_t v_sz_boxed_2331_; size_t v_i_boxed_2332_; lean_object* v_res_2333_; 
v_sz_boxed_2331_ = lean_unbox_usize(v_sz_2326_);
lean_dec(v_sz_2326_);
v_i_boxed_2332_ = lean_unbox_usize(v_i_2327_);
lean_dec(v_i_2327_);
v_res_2333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v_as_2325_, v_sz_boxed_2331_, v_i_boxed_2332_, v_b_2328_, v___y_2329_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v_as_2325_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(lean_object* v_v_2334_){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = l_Lean_Lsp_instToJsonCallHierarchyPrepareParams_toJson(v_v_2334_);
v___x_2336_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(lean_object* v_h_2337_, lean_object* v_r_2338_){
_start:
{
lean_object* v_id_2340_; lean_object* v_method_2341_; lean_object* v_param_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2362_; 
v_id_2340_ = lean_ctor_get(v_r_2338_, 0);
v_method_2341_ = lean_ctor_get(v_r_2338_, 1);
v_param_2342_ = lean_ctor_get(v_r_2338_, 2);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_r_2338_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2344_ = v_r_2338_;
v_isShared_2345_ = v_isSharedCheck_2362_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_param_2342_);
lean_inc(v_method_2341_);
lean_inc(v_id_2340_);
lean_dec(v_r_2338_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2362_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___y_2347_; lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(v_param_2342_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v___x_2353_; 
lean_dec_ref_known(v___x_2352_, 1);
v___x_2353_ = lean_box(0);
v___y_2347_ = v___x_2353_;
goto v___jp_2346_;
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
v_a_2354_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2352_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2352_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
v___y_2347_ = v___x_2359_;
goto v___jp_2346_;
}
}
}
v___jp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 2, v___y_2347_);
v___x_2349_ = v___x_2344_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_id_2340_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_method_2341_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v___y_2347_);
v___x_2349_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_IO_FS_Stream_writeLspMessage(v_h_2337_, v___x_2349_);
return v___x_2350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0___boxed(lean_object* v_h_2363_, lean_object* v_r_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_h_2363_, v_r_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(lean_object* v_r_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___x_2370_; lean_object* v_a_2371_; lean_object* v___x_2372_; 
v___x_2370_ = l_Lean_Lsp_Ipc_stdin(v_a_2368_);
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_a_2371_, v_r_2367_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0___boxed(lean_object* v_r_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v_r_2373_, v_a_2374_);
lean_dec_ref(v_a_2374_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(lean_object* v_requestNo_2380_, lean_object* v_uri_2381_, lean_object* v_pos_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_inc(v_requestNo_2380_);
v___x_2385_ = l_Lean_JsonNumber_fromNat(v_requestNo_2380_);
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
v___x_2387_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v_uri_2381_);
lean_ctor_set(v___x_2388_, 1, v_pos_2382_);
lean_inc_ref(v___x_2386_);
v___x_2389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2386_);
lean_ctor_set(v___x_2389_, 1, v___x_2387_);
lean_ctor_set(v___x_2389_, 2, v___x_2388_);
v___x_2390_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2389_, v_a_2383_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v___x_2391_; 
lean_dec_ref_known(v___x_2390_, 1);
v___x_2391_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2386_, v_a_2383_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v_result_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2435_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v_result_2393_ = lean_ctor_get(v_a_2392_, 1);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_a_2392_);
if (v_isSharedCheck_2435_ == 0)
{
lean_object* v_unused_2436_; 
v_unused_2436_ = lean_ctor_get(v_a_2392_, 0);
lean_dec(v_unused_2436_);
v___x_2395_ = v_a_2392_;
v_isShared_2396_ = v_isSharedCheck_2435_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_result_2393_);
lean_dec(v_a_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2435_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___y_2400_; 
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_nat_add(v_requestNo_2380_, v___x_2397_);
lean_dec(v_requestNo_2380_);
if (lean_obj_tag(v_result_2393_) == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2400_ = v___x_2433_;
goto v___jp_2399_;
}
else
{
lean_object* v_val_2434_; 
v_val_2434_ = lean_ctor_get(v_result_2393_, 0);
lean_inc(v_val_2434_);
lean_dec_ref_known(v_result_2393_, 1);
v___y_2400_ = v_val_2434_;
goto v___jp_2399_;
}
v___jp_2399_:
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2401_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 1, v___x_2401_);
lean_ctor_set(v___x_2395_, 0, v___x_2398_);
v___x_2403_ = v___x_2395_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
size_t v_sz_2404_; size_t v___x_2405_; lean_object* v___x_2406_; 
v_sz_2404_ = lean_array_size(v___y_2400_);
v___x_2405_ = ((size_t)0ULL);
v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v___y_2400_, v_sz_2404_, v___x_2405_, v___x_2403_, v_a_2383_);
lean_dec_ref(v___y_2400_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2423_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2423_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2423_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v_fst_2411_; lean_object* v_snd_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2422_; 
v_fst_2411_ = lean_ctor_get(v_a_2407_, 0);
v_snd_2412_ = lean_ctor_get(v_a_2407_, 1);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_a_2407_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2414_ = v_a_2407_;
v_isShared_2415_ = v_isSharedCheck_2422_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_snd_2412_);
lean_inc(v_fst_2411_);
lean_dec(v_a_2407_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2422_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 1, v_fst_2411_);
lean_ctor_set(v___x_2414_, 0, v_snd_2412_);
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_snd_2412_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_fst_2411_);
v___x_2417_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2419_; 
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2417_);
v___x_2419_ = v___x_2409_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
v_a_2424_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2406_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2406_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v_requestNo_2380_);
v_a_2437_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2391_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2391_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref_known(v___x_2386_, 1);
lean_dec(v_requestNo_2380_);
v_a_2445_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2390_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2390_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___boxed(lean_object* v_requestNo_2453_, lean_object* v_uri_2454_, lean_object* v_pos_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(v_requestNo_2453_, v_uri_2454_, v_pos_2455_, v_a_2456_);
lean_dec_ref(v_a_2456_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2459_, size_t v_i_2460_, lean_object* v_bs_2461_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_usize_dec_lt(v_i_2460_, v_sz_2459_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2463_, 0, v_bs_2461_);
return v___x_2463_;
}
else
{
lean_object* v_v_2464_; lean_object* v___x_2465_; 
v_v_2464_ = lean_array_uget_borrowed(v_bs_2461_, v_i_2460_);
lean_inc(v_v_2464_);
v___x_2465_ = l_Lean_Lsp_instFromJsonCallHierarchyOutgoingCall_fromJson(v_v_2464_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v_bs_2461_);
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2475_; lean_object* v_bs_x27_2476_; size_t v___x_2477_; size_t v___x_2478_; lean_object* v___x_2479_; 
v_a_2474_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2475_ = lean_unsigned_to_nat(0u);
v_bs_x27_2476_ = lean_array_uset(v_bs_2461_, v_i_2460_, v___x_2475_);
v___x_2477_ = ((size_t)1ULL);
v___x_2478_ = lean_usize_add(v_i_2460_, v___x_2477_);
v___x_2479_ = lean_array_uset(v_bs_x27_2476_, v_i_2460_, v_a_2474_);
v_i_2460_ = v___x_2478_;
v_bs_2461_ = v___x_2479_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2481_, lean_object* v_i_2482_, lean_object* v_bs_2483_){
_start:
{
size_t v_sz_boxed_2484_; size_t v_i_boxed_2485_; lean_object* v_res_2486_; 
v_sz_boxed_2484_ = lean_unbox_usize(v_sz_2481_);
lean_dec(v_sz_2481_);
v_i_boxed_2485_ = lean_unbox_usize(v_i_2482_);
lean_dec(v_i_2482_);
v_res_2486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2484_, v_i_boxed_2485_, v_bs_2483_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(lean_object* v_x_2487_){
_start:
{
if (lean_obj_tag(v_x_2487_) == 4)
{
lean_object* v_elems_2488_; size_t v_sz_2489_; size_t v___x_2490_; lean_object* v___x_2491_; 
v_elems_2488_ = lean_ctor_get(v_x_2487_, 0);
lean_inc_ref(v_elems_2488_);
lean_dec_ref_known(v_x_2487_, 1);
v_sz_2489_ = lean_array_size(v_elems_2488_);
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_2489_, v___x_2490_, v_elems_2488_);
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2492_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2493_ = lean_unsigned_to_nat(80u);
v___x_2494_ = l_Lean_Json_pretty(v_x_2487_, v___x_2493_);
v___x_2495_ = lean_string_append(v___x_2492_, v___x_2494_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2497_ = lean_string_append(v___x_2495_, v___x_2496_);
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
return v___x_2498_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(lean_object* v_x_2501_){
_start:
{
if (lean_obj_tag(v_x_2501_) == 0)
{
lean_object* v___x_2502_; 
v___x_2502_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0));
return v___x_2502_;
}
else
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(v_x_2501_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2520_; 
v_a_2512_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2514_ = v___x_2503_;
v_isShared_2515_ = v_isSharedCheck_2520_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2503_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2520_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_a_2512_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2516_);
v___x_2518_ = v___x_2514_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(lean_object* v_expectedID_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_Lsp_Ipc_stdout(v_a_2522_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2668_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2668_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2668_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_IO_FS_Stream_readLspMessage(v_a_2525_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2659_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2659_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2659_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___y_2535_; lean_object* v___y_2536_; 
switch(lean_obj_tag(v_a_2530_))
{
case 2:
{
lean_object* v_id_2542_; lean_object* v_result_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2587_; 
v_id_2542_ = lean_ctor_get(v_a_2530_, 0);
v_result_2543_ = lean_ctor_get(v_a_2530_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_a_2530_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2545_ = v_a_2530_;
v_isShared_2546_ = v_isSharedCheck_2587_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_result_2543_);
lean_inc(v_id_2542_);
lean_dec(v_a_2530_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2587_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
uint8_t v___x_2547_; 
v___x_2547_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2542_, v_expectedID_2521_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; lean_object* v___y_2550_; 
lean_del_object(v___x_2545_);
lean_dec(v_result_2543_);
lean_del_object(v___x_2527_);
v___x_2548_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2521_))
{
case 0:
{
lean_object* v_s_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v_s_2561_ = lean_ctor_get(v_expectedID_2521_, 0);
lean_inc_ref(v_s_2561_);
lean_dec_ref_known(v_expectedID_2521_, 1);
v___x_2562_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2563_ = lean_string_append(v___x_2562_, v_s_2561_);
lean_dec_ref(v_s_2561_);
v___x_2564_ = lean_string_append(v___x_2563_, v___x_2562_);
v___y_2550_ = v___x_2564_;
goto v___jp_2549_;
}
case 1:
{
lean_object* v_n_2565_; lean_object* v___x_2566_; 
v_n_2565_ = lean_ctor_get(v_expectedID_2521_, 0);
lean_inc_ref(v_n_2565_);
lean_dec_ref_known(v_expectedID_2521_, 1);
v___x_2566_ = l_Lean_JsonNumber_toString(v_n_2565_);
v___y_2550_ = v___x_2566_;
goto v___jp_2549_;
}
default: 
{
lean_object* v___x_2567_; 
v___x_2567_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2550_ = v___x_2567_;
goto v___jp_2549_;
}
}
v___jp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = lean_string_append(v___x_2548_, v___y_2550_);
lean_dec_ref(v___y_2550_);
v___x_2552_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2553_ = lean_string_append(v___x_2551_, v___x_2552_);
switch(lean_obj_tag(v_id_2542_))
{
case 0:
{
lean_object* v_s_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_s_2554_ = lean_ctor_get(v_id_2542_, 0);
lean_inc_ref(v_s_2554_);
lean_dec_ref_known(v_id_2542_, 1);
v___x_2555_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2556_ = lean_string_append(v___x_2555_, v_s_2554_);
lean_dec_ref(v_s_2554_);
v___x_2557_ = lean_string_append(v___x_2556_, v___x_2555_);
v___y_2535_ = v___x_2553_;
v___y_2536_ = v___x_2557_;
goto v___jp_2534_;
}
case 1:
{
lean_object* v_n_2558_; lean_object* v___x_2559_; 
v_n_2558_ = lean_ctor_get(v_id_2542_, 0);
lean_inc_ref(v_n_2558_);
lean_dec_ref_known(v_id_2542_, 1);
v___x_2559_ = l_Lean_JsonNumber_toString(v_n_2558_);
v___y_2535_ = v___x_2553_;
v___y_2536_ = v___x_2559_;
goto v___jp_2534_;
}
default: 
{
lean_object* v___x_2560_; 
v___x_2560_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2535_ = v___x_2553_;
v___y_2536_ = v___x_2560_;
goto v___jp_2534_;
}
}
}
}
else
{
lean_object* v___x_2568_; 
lean_dec(v_id_2542_);
lean_del_object(v___x_2532_);
lean_inc(v_result_2543_);
v___x_2568_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(v_result_2543_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
lean_del_object(v___x_2545_);
lean_dec(v_expectedID_2521_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2570_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2571_ = l_Lean_Json_compress(v_result_2543_);
v___x_2572_ = lean_string_append(v___x_2570_, v___x_2571_);
lean_dec_ref(v___x_2571_);
v___x_2573_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2574_ = lean_string_append(v___x_2572_, v___x_2573_);
v___x_2575_ = lean_string_append(v___x_2574_, v_a_2569_);
lean_dec(v_a_2569_);
v___x_2576_ = lean_mk_io_user_error(v___x_2575_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set_tag(v___x_2527_, 1);
lean_ctor_set(v___x_2527_, 0, v___x_2576_);
v___x_2578_ = v___x_2527_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; 
lean_dec(v_result_2543_);
v_a_2580_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2568_, 1);
if (v_isShared_2546_ == 0)
{
lean_ctor_set_tag(v___x_2545_, 0);
lean_ctor_set(v___x_2545_, 1, v_a_2580_);
lean_ctor_set(v___x_2545_, 0, v_expectedID_2521_);
v___x_2582_ = v___x_2545_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_expectedID_2521_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_a_2580_);
v___x_2582_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2584_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2582_);
v___x_2584_ = v___x_2527_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2588_; uint8_t v_code_2589_; lean_object* v_message_2590_; lean_object* v_data_x3f_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___x_2623_; lean_object* v___y_2625_; 
lean_del_object(v___x_2532_);
lean_dec(v_expectedID_2521_);
v_id_2588_ = lean_ctor_get(v_a_2530_, 0);
lean_inc(v_id_2588_);
v_code_2589_ = lean_ctor_get_uint8(v_a_2530_, sizeof(void*)*3);
v_message_2590_ = lean_ctor_get(v_a_2530_, 1);
lean_inc_ref(v_message_2590_);
v_data_x3f_2591_ = lean_ctor_get(v_a_2530_, 2);
lean_inc(v_data_x3f_2591_);
lean_dec_ref_known(v_a_2530_, 3);
v___x_2592_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2593_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2623_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2588_))
{
case 0:
{
lean_object* v_s_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_s_2641_ = lean_ctor_get(v_id_2588_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_id_2588_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v_id_2588_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_s_2641_);
lean_dec(v_id_2588_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 3);
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_s_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
v___y_2625_ = v___x_2646_;
goto v___jp_2624_;
}
}
}
case 1:
{
lean_object* v_n_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
v_n_2649_ = lean_ctor_get(v_id_2588_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_id_2588_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v_id_2588_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_n_2649_);
lean_dec(v_id_2588_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set_tag(v___x_2651_, 2);
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_n_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
v___y_2625_ = v___x_2654_;
goto v___jp_2624_;
}
}
}
default: 
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_box(0);
v___y_2625_ = v___x_2657_;
goto v___jp_2624_;
}
}
v___jp_2594_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
lean_inc(v___y_2598_);
lean_inc_ref(v___y_2596_);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___y_2596_);
lean_ctor_set(v___x_2599_, 1, v___y_2598_);
v___x_2600_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_message_2590_);
v___x_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2599_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2607_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2606_, v_data_x3f_2591_);
lean_dec(v_data_x3f_2591_);
v___x_2608_ = l_List_appendTR___redArg(v___x_2605_, v___x_2607_);
v___x_2609_ = l_Lean_Json_mkObj(v___x_2608_);
lean_dec(v___x_2608_);
lean_inc_ref(v___y_2595_);
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___y_2595_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___x_2603_);
v___x_2612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___y_2597_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2593_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = l_Lean_Json_mkObj(v___x_2613_);
lean_dec_ref_known(v___x_2613_, 2);
v___x_2615_ = l_Lean_Json_compress(v___x_2614_);
v___x_2616_ = lean_string_append(v___x_2592_, v___x_2615_);
lean_dec_ref(v___x_2615_);
v___x_2617_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2618_ = lean_string_append(v___x_2616_, v___x_2617_);
v___x_2619_ = lean_mk_io_user_error(v___x_2618_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set_tag(v___x_2527_, 1);
lean_ctor_set(v___x_2527_, 0, v___x_2619_);
v___x_2621_ = v___x_2527_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
v___jp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2623_);
lean_ctor_set(v___x_2626_, 1, v___y_2625_);
v___x_2627_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2628_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2589_)
{
case 0:
{
lean_object* v___x_2629_; 
v___x_2629_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2629_;
goto v___jp_2594_;
}
case 1:
{
lean_object* v___x_2630_; 
v___x_2630_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2630_;
goto v___jp_2594_;
}
case 2:
{
lean_object* v___x_2631_; 
v___x_2631_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2631_;
goto v___jp_2594_;
}
case 3:
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2632_;
goto v___jp_2594_;
}
case 4:
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2633_;
goto v___jp_2594_;
}
case 5:
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2634_;
goto v___jp_2594_;
}
case 6:
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2635_;
goto v___jp_2594_;
}
case 7:
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2636_;
goto v___jp_2594_;
}
case 8:
{
lean_object* v___x_2637_; 
v___x_2637_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2637_;
goto v___jp_2594_;
}
case 9:
{
lean_object* v___x_2638_; 
v___x_2638_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2638_;
goto v___jp_2594_;
}
case 10:
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2639_;
goto v___jp_2594_;
}
default: 
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2595_ = v___x_2627_;
v___y_2596_ = v___x_2628_;
v___y_2597_ = v___x_2626_;
v___y_2598_ = v___x_2640_;
goto v___jp_2594_;
}
}
}
}
default: 
{
lean_del_object(v___x_2532_);
lean_dec(v_a_2530_);
lean_del_object(v___x_2527_);
goto _start;
}
}
v___jp_2534_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2537_ = lean_string_append(v___y_2535_, v___y_2536_);
lean_dec_ref(v___y_2536_);
v___x_2538_ = lean_mk_io_user_error(v___x_2537_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set_tag(v___x_2532_, 1);
lean_ctor_set(v___x_2532_, 0, v___x_2538_);
v___x_2540_ = v___x_2532_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_del_object(v___x_2527_);
lean_dec(v_expectedID_2521_);
v_a_2660_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2529_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2529_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec(v_expectedID_2521_);
v_a_2669_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2524_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2524_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1___boxed(lean_object* v_expectedID_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v_expectedID_2677_, v_a_2678_);
lean_dec_ref(v_a_2678_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(lean_object* v_v_2681_){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = l_Lean_Lsp_instToJsonCallHierarchyOutgoingCallsParams_toJson(v_v_2681_);
v___x_2683_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(lean_object* v_h_2684_, lean_object* v_r_2685_){
_start:
{
lean_object* v_id_2687_; lean_object* v_method_2688_; lean_object* v_param_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2709_; 
v_id_2687_ = lean_ctor_get(v_r_2685_, 0);
v_method_2688_ = lean_ctor_get(v_r_2685_, 1);
v_param_2689_ = lean_ctor_get(v_r_2685_, 2);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_r_2685_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2691_ = v_r_2685_;
v_isShared_2692_ = v_isSharedCheck_2709_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_param_2689_);
lean_inc(v_method_2688_);
lean_inc(v_id_2687_);
lean_dec(v_r_2685_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2709_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___y_2694_; lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(v_param_2689_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v___x_2700_; 
lean_dec_ref_known(v___x_2699_, 1);
v___x_2700_ = lean_box(0);
v___y_2694_ = v___x_2700_;
goto v___jp_2693_;
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
v_a_2701_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2699_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2699_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
v___y_2694_ = v___x_2706_;
goto v___jp_2693_;
}
}
}
v___jp_2693_:
{
lean_object* v___x_2696_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 2, v___y_2694_);
v___x_2696_ = v___x_2691_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_id_2687_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_method_2688_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v___y_2694_);
v___x_2696_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_IO_FS_Stream_writeLspMessage(v_h_2684_, v___x_2696_);
return v___x_2697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0___boxed(lean_object* v_h_2710_, lean_object* v_r_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_h_2710_, v_r_2711_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(lean_object* v_r_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v___x_2717_; lean_object* v_a_2718_; lean_object* v___x_2719_; 
v___x_2717_ = l_Lean_Lsp_Ipc_stdin(v_a_2715_);
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref(v___x_2717_);
v___x_2719_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_a_2718_, v_r_2714_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0___boxed(lean_object* v_r_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v_r_2720_, v_a_2721_);
lean_dec_ref(v_a_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(lean_object* v_requestNo_2727_, lean_object* v_item_2728_, lean_object* v_fromRanges_2729_, lean_object* v_visited_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v_name_2733_; uint8_t v___x_2734_; 
v_name_2733_ = lean_ctor_get(v_item_2728_, 0);
v___x_2734_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_2733_, v_visited_2730_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_inc(v_requestNo_2727_);
v___x_2735_ = l_Lean_JsonNumber_fromNat(v_requestNo_2727_);
v___x_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
v___x_2737_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_2728_);
lean_inc_ref(v___x_2736_);
v___x_2738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
lean_ctor_set(v___x_2738_, 2, v_item_2728_);
v___x_2739_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v___x_2738_, v_a_2731_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v___x_2740_; 
lean_dec_ref_known(v___x_2739_, 1);
v___x_2740_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v___x_2736_, v_a_2731_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2778_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
if (v___x_2734_ == 0)
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_box(0);
lean_inc_ref(v_name_2733_);
v___x_2785_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_2733_, v___x_2784_, v_visited_2730_);
v___y_2778_ = v___x_2785_;
goto v___jp_2777_;
}
else
{
v___y_2778_ = v_visited_2730_;
goto v___jp_2777_;
}
v___jp_2742_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; size_t v_sz_2748_; size_t v___x_2749_; lean_object* v___x_2750_; 
v___x_2746_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___y_2744_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v_sz_2748_ = lean_array_size(v___y_2745_);
v___x_2749_ = ((size_t)0ULL);
v___x_2750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___y_2743_, v___y_2745_, v_sz_2748_, v___x_2749_, v___x_2747_, v_a_2731_);
lean_dec_ref(v___y_2745_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2768_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2768_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2768_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v_fst_2755_; lean_object* v_snd_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2767_; 
v_fst_2755_ = lean_ctor_get(v_a_2751_, 0);
v_snd_2756_ = lean_ctor_get(v_a_2751_, 1);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_a_2751_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2758_ = v_a_2751_;
v_isShared_2759_ = v_isSharedCheck_2767_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_snd_2756_);
lean_inc(v_fst_2755_);
lean_dec(v_a_2751_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2767_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2760_, 0, v_item_2728_);
lean_ctor_set(v___x_2760_, 1, v_fromRanges_2729_);
lean_ctor_set(v___x_2760_, 2, v_snd_2756_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v_fst_2755_);
lean_ctor_set(v___x_2758_, 0, v___x_2760_);
v___x_2762_ = v___x_2758_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_fst_2755_);
v___x_2762_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2764_; 
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2762_);
v___x_2764_ = v___x_2753_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec_ref(v_fromRanges_2729_);
lean_dec_ref(v_item_2728_);
v_a_2769_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2750_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2750_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
v___jp_2777_:
{
lean_object* v_result_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v_result_2779_ = lean_ctor_get(v_a_2741_, 1);
lean_inc(v_result_2779_);
lean_dec(v_a_2741_);
v___x_2780_ = lean_unsigned_to_nat(1u);
v___x_2781_ = lean_nat_add(v_requestNo_2727_, v___x_2780_);
lean_dec(v_requestNo_2727_);
if (lean_obj_tag(v_result_2779_) == 0)
{
lean_object* v___x_2782_; 
v___x_2782_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1));
v___y_2743_ = v___y_2778_;
v___y_2744_ = v___x_2781_;
v___y_2745_ = v___x_2782_;
goto v___jp_2742_;
}
else
{
lean_object* v_val_2783_; 
v_val_2783_ = lean_ctor_get(v_result_2779_, 0);
lean_inc(v_val_2783_);
lean_dec_ref_known(v_result_2779_, 1);
v___y_2743_ = v___y_2778_;
v___y_2744_ = v___x_2781_;
v___y_2745_ = v_val_2783_;
goto v___jp_2742_;
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec(v_visited_2730_);
lean_dec_ref(v_fromRanges_2729_);
lean_dec_ref(v_item_2728_);
lean_dec(v_requestNo_2727_);
v_a_2786_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2740_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2740_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec_ref_known(v___x_2736_, 1);
lean_dec(v_visited_2730_);
lean_dec_ref(v_fromRanges_2729_);
lean_dec_ref(v_item_2728_);
lean_dec(v_requestNo_2727_);
v_a_2794_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2739_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2739_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
lean_dec(v_visited_2730_);
lean_dec_ref(v_fromRanges_2729_);
v___x_2802_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2803_, 0, v_item_2728_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
lean_ctor_set(v___x_2803_, 2, v___x_2802_);
v___x_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
lean_ctor_set(v___x_2804_, 1, v_requestNo_2727_);
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(lean_object* v___x_2806_, lean_object* v_as_2807_, size_t v_sz_2808_, size_t v_i_2809_, lean_object* v_b_2810_, lean_object* v___y_2811_){
_start:
{
uint8_t v___x_2813_; 
v___x_2813_ = lean_usize_dec_lt(v_i_2809_, v_sz_2808_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; 
lean_dec(v___x_2806_);
v___x_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2814_, 0, v_b_2810_);
return v___x_2814_;
}
else
{
lean_object* v_fst_2815_; lean_object* v_snd_2816_; lean_object* v_a_2817_; lean_object* v_to_2818_; lean_object* v_fromRanges_2819_; lean_object* v___x_2820_; 
v_fst_2815_ = lean_ctor_get(v_b_2810_, 0);
lean_inc(v_fst_2815_);
v_snd_2816_ = lean_ctor_get(v_b_2810_, 1);
lean_inc(v_snd_2816_);
lean_dec_ref(v_b_2810_);
v_a_2817_ = lean_array_uget_borrowed(v_as_2807_, v_i_2809_);
v_to_2818_ = lean_ctor_get(v_a_2817_, 0);
v_fromRanges_2819_ = lean_ctor_get(v_a_2817_, 1);
lean_inc(v___x_2806_);
lean_inc_ref(v_fromRanges_2819_);
lean_inc_ref(v_to_2818_);
v___x_2820_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2815_, v_to_2818_, v_fromRanges_2819_, v___x_2806_, v___y_2811_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v_fst_2822_; lean_object* v_snd_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2834_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v_fst_2822_ = lean_ctor_get(v_a_2821_, 0);
v_snd_2823_ = lean_ctor_get(v_a_2821_, 1);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_a_2821_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2825_ = v_a_2821_;
v_isShared_2826_ = v_isSharedCheck_2834_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_snd_2823_);
lean_inc(v_fst_2822_);
lean_dec(v_a_2821_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2834_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2829_; 
v___x_2827_ = lean_array_push(v_snd_2816_, v_fst_2822_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 1, v___x_2827_);
lean_ctor_set(v___x_2825_, 0, v_snd_2823_);
v___x_2829_ = v___x_2825_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_snd_2823_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___x_2827_);
v___x_2829_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
size_t v___x_2830_; size_t v___x_2831_; 
v___x_2830_ = ((size_t)1ULL);
v___x_2831_ = lean_usize_add(v_i_2809_, v___x_2830_);
v_i_2809_ = v___x_2831_;
v_b_2810_ = v___x_2829_;
goto _start;
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_snd_2816_);
lean_dec(v___x_2806_);
v_a_2835_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2820_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2820_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2___boxed(lean_object* v___x_2843_, lean_object* v_as_2844_, lean_object* v_sz_2845_, lean_object* v_i_2846_, lean_object* v_b_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
size_t v_sz_boxed_2850_; size_t v_i_boxed_2851_; lean_object* v_res_2852_; 
v_sz_boxed_2850_ = lean_unbox_usize(v_sz_2845_);
lean_dec(v_sz_2845_);
v_i_boxed_2851_ = lean_unbox_usize(v_i_2846_);
lean_dec(v_i_2846_);
v_res_2852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___x_2843_, v_as_2844_, v_sz_boxed_2850_, v_i_boxed_2851_, v_b_2847_, v___y_2848_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_as_2844_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___boxed(lean_object* v_requestNo_2853_, lean_object* v_item_2854_, lean_object* v_fromRanges_2855_, lean_object* v_visited_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_requestNo_2853_, v_item_2854_, v_fromRanges_2855_, v_visited_2856_, v_a_2857_);
lean_dec_ref(v_a_2857_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(lean_object* v_as_2860_, size_t v_sz_2861_, size_t v_i_2862_, lean_object* v_b_2863_, lean_object* v___y_2864_){
_start:
{
uint8_t v___x_2866_; 
v___x_2866_ = lean_usize_dec_lt(v_i_2862_, v_sz_2861_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_b_2863_);
return v___x_2867_;
}
else
{
lean_object* v_fst_2868_; lean_object* v_snd_2869_; lean_object* v_a_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_fst_2868_ = lean_ctor_get(v_b_2863_, 0);
lean_inc(v_fst_2868_);
v_snd_2869_ = lean_ctor_get(v_b_2863_, 1);
lean_inc(v_snd_2869_);
lean_dec_ref(v_b_2863_);
v_a_2870_ = lean_array_uget_borrowed(v_as_2860_, v_i_2862_);
v___x_2871_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2872_ = lean_box(1);
lean_inc(v_a_2870_);
v___x_2873_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2868_, v_a_2870_, v___x_2871_, v___x_2872_, v___y_2864_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v_fst_2875_; lean_object* v_snd_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2887_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v_fst_2875_ = lean_ctor_get(v_a_2874_, 0);
v_snd_2876_ = lean_ctor_get(v_a_2874_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_a_2874_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2878_ = v_a_2874_;
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_snd_2876_);
lean_inc(v_fst_2875_);
lean_dec(v_a_2874_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2880_ = lean_array_push(v_snd_2869_, v_fst_2875_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 1, v___x_2880_);
lean_ctor_set(v___x_2878_, 0, v_snd_2876_);
v___x_2882_ = v___x_2878_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_snd_2876_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
size_t v___x_2883_; size_t v___x_2884_; 
v___x_2883_ = ((size_t)1ULL);
v___x_2884_ = lean_usize_add(v_i_2862_, v___x_2883_);
v_i_2862_ = v___x_2884_;
v_b_2863_ = v___x_2882_;
goto _start;
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v_snd_2869_);
v_a_2888_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2873_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2873_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0___boxed(lean_object* v_as_2896_, lean_object* v_sz_2897_, lean_object* v_i_2898_, lean_object* v_b_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
size_t v_sz_boxed_2902_; size_t v_i_boxed_2903_; lean_object* v_res_2904_; 
v_sz_boxed_2902_ = lean_unbox_usize(v_sz_2897_);
lean_dec(v_sz_2897_);
v_i_boxed_2903_ = lean_unbox_usize(v_i_2898_);
lean_dec(v_i_2898_);
v_res_2904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v_as_2896_, v_sz_boxed_2902_, v_i_boxed_2903_, v_b_2899_, v___y_2900_);
lean_dec_ref(v___y_2900_);
lean_dec_ref(v_as_2896_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(lean_object* v_requestNo_2905_, lean_object* v_uri_2906_, lean_object* v_pos_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_inc(v_requestNo_2905_);
v___x_2910_ = l_Lean_JsonNumber_fromNat(v_requestNo_2905_);
v___x_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
v___x_2912_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2913_, 0, v_uri_2906_);
lean_ctor_set(v___x_2913_, 1, v_pos_2907_);
lean_inc_ref(v___x_2911_);
v___x_2914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2911_);
lean_ctor_set(v___x_2914_, 1, v___x_2912_);
lean_ctor_set(v___x_2914_, 2, v___x_2913_);
v___x_2915_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2914_, v_a_2908_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v___x_2916_; 
lean_dec_ref_known(v___x_2915_, 1);
v___x_2916_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2911_, v_a_2908_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v_result_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2960_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref_known(v___x_2916_, 1);
v_result_2918_ = lean_ctor_get(v_a_2917_, 1);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_a_2917_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; 
v_unused_2961_ = lean_ctor_get(v_a_2917_, 0);
lean_dec(v_unused_2961_);
v___x_2920_ = v_a_2917_;
v_isShared_2921_ = v_isSharedCheck_2960_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_result_2918_);
lean_dec(v_a_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2960_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___y_2925_; 
v___x_2922_ = lean_unsigned_to_nat(1u);
v___x_2923_ = lean_nat_add(v_requestNo_2905_, v___x_2922_);
lean_dec(v_requestNo_2905_);
if (lean_obj_tag(v_result_2918_) == 0)
{
lean_object* v___x_2958_; 
v___x_2958_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2925_ = v___x_2958_;
goto v___jp_2924_;
}
else
{
lean_object* v_val_2959_; 
v_val_2959_ = lean_ctor_get(v_result_2918_, 0);
lean_inc(v_val_2959_);
lean_dec_ref_known(v_result_2918_, 1);
v___y_2925_ = v_val_2959_;
goto v___jp_2924_;
}
v___jp_2924_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 1, v___x_2926_);
lean_ctor_set(v___x_2920_, 0, v___x_2923_);
v___x_2928_ = v___x_2920_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2923_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
size_t v_sz_2929_; size_t v___x_2930_; lean_object* v___x_2931_; 
v_sz_2929_ = lean_array_size(v___y_2925_);
v___x_2930_ = ((size_t)0ULL);
v___x_2931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v___y_2925_, v_sz_2929_, v___x_2930_, v___x_2928_, v_a_2908_);
lean_dec_ref(v___y_2925_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2948_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2934_ = v___x_2931_;
v_isShared_2935_ = v_isSharedCheck_2948_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2948_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v_fst_2936_; lean_object* v_snd_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2947_; 
v_fst_2936_ = lean_ctor_get(v_a_2932_, 0);
v_snd_2937_ = lean_ctor_get(v_a_2932_, 1);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_a_2932_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2939_ = v_a_2932_;
v_isShared_2940_ = v_isSharedCheck_2947_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_snd_2937_);
lean_inc(v_fst_2936_);
lean_dec(v_a_2932_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2947_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 1, v_fst_2936_);
lean_ctor_set(v___x_2939_, 0, v_snd_2937_);
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_snd_2937_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_fst_2936_);
v___x_2942_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2944_; 
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 0, v___x_2942_);
v___x_2944_ = v___x_2934_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_a_2949_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2931_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2931_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec(v_requestNo_2905_);
v_a_2962_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2916_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2916_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref_known(v___x_2911_, 1);
lean_dec(v_requestNo_2905_);
v_a_2970_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2915_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2915_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy___boxed(lean_object* v_requestNo_2978_, lean_object* v_uri_2979_, lean_object* v_pos_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(v_requestNo_2978_, v_uri_2979_, v_pos_2980_, v_a_2981_);
lean_dec_ref(v_a_2981_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(lean_object* v_j_2984_, lean_object* v_k_2985_){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = l_Lean_Json_getObjValD(v_j_2984_, v_k_2985_);
v___x_2987_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v___x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0___boxed(lean_object* v_j_2988_, lean_object* v_k_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_j_2988_, v_k_2989_);
lean_dec_ref(v_k_2989_);
return v_res_2990_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2997_ = 1;
v___x_2998_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1));
v___x_2999_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2998_, v___x_2997_);
return v___x_2999_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3000_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_3001_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2);
v___x_3002_ = lean_string_append(v___x_3001_, v___x_3000_);
return v___x_3002_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3003_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_3004_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3005_ = lean_string_append(v___x_3004_, v___x_3003_);
return v___x_3005_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3006_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3007_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4);
v___x_3008_ = lean_string_append(v___x_3007_, v___x_3006_);
return v___x_3008_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_3010_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3011_ = lean_string_append(v___x_3010_, v___x_3009_);
return v___x_3011_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3013_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6);
v___x_3014_ = lean_string_append(v___x_3013_, v___x_3012_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(lean_object* v_json_3015_){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_3015_);
v___x_3017_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_json_3015_, v___x_3016_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v_json_3015_);
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3027_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3027_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3022_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5);
v___x_3023_ = lean_string_append(v___x_3022_, v_a_3018_);
lean_dec(v_a_3018_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3023_);
v___x_3025_ = v___x_3020_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
else
{
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v_json_3015_);
v_a_3028_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3017_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3017_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
lean_ctor_set_tag(v___x_3030_, 0);
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v_a_3036_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3037_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3038_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_json_3015_, v___x_3037_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3048_; 
lean_dec(v_a_3036_);
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3048_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3048_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3043_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7);
v___x_3044_ = lean_string_append(v___x_3043_, v_a_3039_);
lean_dec(v_a_3039_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3044_);
v___x_3046_ = v___x_3041_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
else
{
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec(v_a_3036_);
v_a_3049_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3038_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3038_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set_tag(v___x_3051_, 0);
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3065_; 
v_a_3057_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3059_ = v___x_3038_;
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3038_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3065_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v_a_3036_);
lean_ctor_set(v___x_3061_, 1, v_a_3057_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3061_);
v___x_3063_ = v___x_3059_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_3066_, size_t v_i_3067_, lean_object* v_bs_3068_){
_start:
{
uint8_t v___x_3069_; 
v___x_3069_ = lean_usize_dec_lt(v_i_3067_, v_sz_3066_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3070_, 0, v_bs_3068_);
return v___x_3070_;
}
else
{
lean_object* v_v_3071_; lean_object* v___x_3072_; 
v_v_3071_ = lean_array_uget_borrowed(v_bs_3068_, v_i_3067_);
lean_inc(v_v_3071_);
v___x_3072_ = l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(v_v_3071_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec_ref(v_bs_3068_);
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3082_; lean_object* v_bs_x27_3083_; size_t v___x_3084_; size_t v___x_3085_; lean_object* v___x_3086_; 
v_a_3081_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3072_, 1);
v___x_3082_ = lean_unsigned_to_nat(0u);
v_bs_x27_3083_ = lean_array_uset(v_bs_3068_, v_i_3067_, v___x_3082_);
v___x_3084_ = ((size_t)1ULL);
v___x_3085_ = lean_usize_add(v_i_3067_, v___x_3084_);
v___x_3086_ = lean_array_uset(v_bs_x27_3083_, v_i_3067_, v_a_3081_);
v_i_3067_ = v___x_3085_;
v_bs_3068_ = v___x_3086_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_3088_){
_start:
{
if (lean_obj_tag(v_x_3088_) == 4)
{
lean_object* v_elems_3089_; size_t v_sz_3090_; size_t v___x_3091_; lean_object* v___x_3092_; 
v_elems_3089_ = lean_ctor_get(v_x_3088_, 0);
lean_inc_ref(v_elems_3089_);
lean_dec_ref_known(v_x_3088_, 1);
v_sz_3090_ = lean_array_size(v_elems_3089_);
v___x_3091_ = ((size_t)0ULL);
v___x_3092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_3090_, v___x_3091_, v_elems_3089_);
return v___x_3092_;
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3093_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3094_ = lean_unsigned_to_nat(80u);
v___x_3095_ = l_Lean_Json_pretty(v_x_3088_, v___x_3094_);
v___x_3096_ = lean_string_append(v___x_3093_, v___x_3095_);
lean_dec_ref(v___x_3095_);
v___x_3097_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3098_ = lean_string_append(v___x_3096_, v___x_3097_);
v___x_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
return v___x_3099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(lean_object* v_j_3100_, lean_object* v_k_3101_){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = l_Lean_Json_getObjValD(v_j_3100_, v_k_3101_);
v___x_3103_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1___boxed(lean_object* v_j_3104_, lean_object* v_k_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_j_3104_, v_k_3105_);
lean_dec_ref(v_k_3105_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_3107_, lean_object* v_i_3108_, lean_object* v_bs_3109_){
_start:
{
size_t v_sz_boxed_3110_; size_t v_i_boxed_3111_; lean_object* v_res_3112_; 
v_sz_boxed_3110_ = lean_unbox_usize(v_sz_3107_);
lean_dec(v_sz_3107_);
v_i_boxed_3111_ = lean_unbox_usize(v_i_3108_);
lean_dec(v_i_3108_);
v_res_3112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_3110_, v_i_boxed_3111_, v_bs_3109_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(lean_object* v_x_3115_){
_start:
{
lean_object* v_item_3116_; lean_object* v_children_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3137_; 
v_item_3116_ = lean_ctor_get(v_x_3115_, 0);
v_children_3117_ = lean_ctor_get(v_x_3115_, 1);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_x_3115_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3119_ = v_x_3115_;
v_isShared_3120_ = v_isSharedCheck_3137_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_children_3117_);
lean_inc(v_item_3116_);
lean_dec(v_x_3115_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3137_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3121_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_3122_ = l_Lean_Lsp_instToJsonLeanImport_toJson(v_item_3116_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 1, v___x_3122_);
lean_ctor_set(v___x_3119_, 0, v___x_3121_);
v___x_3124_ = v___x_3119_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3125_ = lean_box(0);
v___x_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3124_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3128_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(v_children_3117_);
v___x_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
lean_ctor_set(v___x_3130_, 1, v___x_3125_);
v___x_3131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
lean_ctor_set(v___x_3131_, 1, v___x_3125_);
v___x_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3126_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_3134_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_3132_, v___x_3133_);
v___x_3135_ = l_Lean_Json_mkObj(v___x_3134_);
lean_dec(v___x_3134_);
return v___x_3135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(size_t v_sz_3138_, size_t v_i_3139_, lean_object* v_bs_3140_){
_start:
{
uint8_t v___x_3141_; 
v___x_3141_ = lean_usize_dec_lt(v_i_3139_, v_sz_3138_);
if (v___x_3141_ == 0)
{
return v_bs_3140_;
}
else
{
lean_object* v_v_3142_; lean_object* v___x_3143_; lean_object* v_bs_x27_3144_; lean_object* v___x_3145_; size_t v___x_3146_; size_t v___x_3147_; lean_object* v___x_3148_; 
v_v_3142_ = lean_array_uget(v_bs_3140_, v_i_3139_);
v___x_3143_ = lean_unsigned_to_nat(0u);
v_bs_x27_3144_ = lean_array_uset(v_bs_3140_, v_i_3139_, v___x_3143_);
v___x_3145_ = l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(v_v_3142_);
v___x_3146_ = ((size_t)1ULL);
v___x_3147_ = lean_usize_add(v_i_3139_, v___x_3146_);
v___x_3148_ = lean_array_uset(v_bs_x27_3144_, v_i_3139_, v___x_3145_);
v_i_3139_ = v___x_3147_;
v_bs_3140_ = v___x_3148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(lean_object* v_a_3150_){
_start:
{
size_t v_sz_3151_; size_t v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v_sz_3151_ = lean_array_size(v_a_3150_);
v___x_3152_ = ((size_t)0ULL);
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_3151_, v___x_3152_, v_a_3150_);
v___x_3154_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3155_, lean_object* v_i_3156_, lean_object* v_bs_3157_){
_start:
{
size_t v_sz_boxed_3158_; size_t v_i_boxed_3159_; lean_object* v_res_3160_; 
v_sz_boxed_3158_ = lean_unbox_usize(v_sz_3155_);
lean_dec(v_sz_3155_);
v_i_boxed_3159_ = lean_unbox_usize(v_i_3156_);
lean_dec(v_i_3156_);
v_res_3160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_boxed_3158_, v_i_boxed_3159_, v_bs_3157_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(size_t v_sz_3163_, size_t v_i_3164_, lean_object* v_bs_3165_){
_start:
{
uint8_t v___x_3166_; 
v___x_3166_ = lean_usize_dec_lt(v_i_3164_, v_sz_3163_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; 
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v_bs_3165_);
return v___x_3167_;
}
else
{
lean_object* v_v_3168_; lean_object* v___x_3169_; 
v_v_3168_ = lean_array_uget_borrowed(v_bs_3165_, v_i_3164_);
lean_inc(v_v_3168_);
v___x_3169_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v_v_3168_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec_ref(v_bs_3165_);
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3179_; lean_object* v_bs_x27_3180_; size_t v___x_3181_; size_t v___x_3182_; lean_object* v___x_3183_; 
v_a_3178_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3169_, 1);
v___x_3179_ = lean_unsigned_to_nat(0u);
v_bs_x27_3180_ = lean_array_uset(v_bs_3165_, v_i_3164_, v___x_3179_);
v___x_3181_ = ((size_t)1ULL);
v___x_3182_ = lean_usize_add(v_i_3164_, v___x_3181_);
v___x_3183_ = lean_array_uset(v_bs_x27_3180_, v_i_3164_, v_a_3178_);
v_i_3164_ = v___x_3182_;
v_bs_3165_ = v___x_3183_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_3185_, lean_object* v_i_3186_, lean_object* v_bs_3187_){
_start:
{
size_t v_sz_boxed_3188_; size_t v_i_boxed_3189_; lean_object* v_res_3190_; 
v_sz_boxed_3188_ = lean_unbox_usize(v_sz_3185_);
lean_dec(v_sz_3185_);
v_i_boxed_3189_ = lean_unbox_usize(v_i_3186_);
lean_dec(v_i_3186_);
v_res_3190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_boxed_3188_, v_i_boxed_3189_, v_bs_3187_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(lean_object* v_x_3191_){
_start:
{
if (lean_obj_tag(v_x_3191_) == 4)
{
lean_object* v_elems_3192_; size_t v_sz_3193_; size_t v___x_3194_; lean_object* v___x_3195_; 
v_elems_3192_ = lean_ctor_get(v_x_3191_, 0);
lean_inc_ref(v_elems_3192_);
lean_dec_ref_known(v_x_3191_, 1);
v_sz_3193_ = lean_array_size(v_elems_3192_);
v___x_3194_ = ((size_t)0ULL);
v___x_3195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_3193_, v___x_3194_, v_elems_3192_);
return v___x_3195_;
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3196_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3197_ = lean_unsigned_to_nat(80u);
v___x_3198_ = l_Lean_Json_pretty(v_x_3191_, v___x_3197_);
v___x_3199_ = lean_string_append(v___x_3196_, v___x_3198_);
lean_dec_ref(v___x_3198_);
v___x_3200_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3201_ = lean_string_append(v___x_3199_, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
return v___x_3202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(lean_object* v_expectedID_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_Lsp_Ipc_stdout(v_a_3204_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3350_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3209_ = v___x_3206_;
v_isShared_3210_ = v_isSharedCheck_3350_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3206_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3350_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_IO_FS_Stream_readLspMessage(v_a_3207_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3341_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3341_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3341_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___y_3217_; lean_object* v___y_3218_; 
switch(lean_obj_tag(v_a_3212_))
{
case 2:
{
lean_object* v_id_3224_; lean_object* v_result_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3269_; 
v_id_3224_ = lean_ctor_get(v_a_3212_, 0);
v_result_3225_ = lean_ctor_get(v_a_3212_, 1);
v_isSharedCheck_3269_ = !lean_is_exclusive(v_a_3212_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3227_ = v_a_3212_;
v_isShared_3228_ = v_isSharedCheck_3269_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_result_3225_);
lean_inc(v_id_3224_);
lean_dec(v_a_3212_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3269_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
uint8_t v___x_3229_; 
v___x_3229_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3224_, v_expectedID_3203_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___y_3232_; 
lean_del_object(v___x_3227_);
lean_dec(v_result_3225_);
lean_del_object(v___x_3209_);
v___x_3230_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3203_))
{
case 0:
{
lean_object* v_s_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v_s_3243_ = lean_ctor_get(v_expectedID_3203_, 0);
lean_inc_ref(v_s_3243_);
lean_dec_ref_known(v_expectedID_3203_, 1);
v___x_3244_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3245_ = lean_string_append(v___x_3244_, v_s_3243_);
lean_dec_ref(v_s_3243_);
v___x_3246_ = lean_string_append(v___x_3245_, v___x_3244_);
v___y_3232_ = v___x_3246_;
goto v___jp_3231_;
}
case 1:
{
lean_object* v_n_3247_; lean_object* v___x_3248_; 
v_n_3247_ = lean_ctor_get(v_expectedID_3203_, 0);
lean_inc_ref(v_n_3247_);
lean_dec_ref_known(v_expectedID_3203_, 1);
v___x_3248_ = l_Lean_JsonNumber_toString(v_n_3247_);
v___y_3232_ = v___x_3248_;
goto v___jp_3231_;
}
default: 
{
lean_object* v___x_3249_; 
v___x_3249_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3232_ = v___x_3249_;
goto v___jp_3231_;
}
}
v___jp_3231_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = lean_string_append(v___x_3230_, v___y_3232_);
lean_dec_ref(v___y_3232_);
v___x_3234_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3235_ = lean_string_append(v___x_3233_, v___x_3234_);
switch(lean_obj_tag(v_id_3224_))
{
case 0:
{
lean_object* v_s_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v_s_3236_ = lean_ctor_get(v_id_3224_, 0);
lean_inc_ref(v_s_3236_);
lean_dec_ref_known(v_id_3224_, 1);
v___x_3237_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3238_ = lean_string_append(v___x_3237_, v_s_3236_);
lean_dec_ref(v_s_3236_);
v___x_3239_ = lean_string_append(v___x_3238_, v___x_3237_);
v___y_3217_ = v___x_3235_;
v___y_3218_ = v___x_3239_;
goto v___jp_3216_;
}
case 1:
{
lean_object* v_n_3240_; lean_object* v___x_3241_; 
v_n_3240_ = lean_ctor_get(v_id_3224_, 0);
lean_inc_ref(v_n_3240_);
lean_dec_ref_known(v_id_3224_, 1);
v___x_3241_ = l_Lean_JsonNumber_toString(v_n_3240_);
v___y_3217_ = v___x_3235_;
v___y_3218_ = v___x_3241_;
goto v___jp_3216_;
}
default: 
{
lean_object* v___x_3242_; 
v___x_3242_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3217_ = v___x_3235_;
v___y_3218_ = v___x_3242_;
goto v___jp_3216_;
}
}
}
}
else
{
lean_object* v___x_3250_; 
lean_dec(v_id_3224_);
lean_del_object(v___x_3214_);
lean_inc(v_result_3225_);
v___x_3250_ = l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(v_result_3225_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
lean_del_object(v___x_3227_);
lean_dec(v_expectedID_3203_);
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
v___x_3252_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3253_ = l_Lean_Json_compress(v_result_3225_);
v___x_3254_ = lean_string_append(v___x_3252_, v___x_3253_);
lean_dec_ref(v___x_3253_);
v___x_3255_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3256_ = lean_string_append(v___x_3254_, v___x_3255_);
v___x_3257_ = lean_string_append(v___x_3256_, v_a_3251_);
lean_dec(v_a_3251_);
v___x_3258_ = lean_mk_io_user_error(v___x_3257_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 1);
lean_ctor_set(v___x_3209_, 0, v___x_3258_);
v___x_3260_ = v___x_3209_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; 
lean_dec(v_result_3225_);
v_a_3262_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3262_);
lean_dec_ref_known(v___x_3250_, 1);
if (v_isShared_3228_ == 0)
{
lean_ctor_set_tag(v___x_3227_, 0);
lean_ctor_set(v___x_3227_, 1, v_a_3262_);
lean_ctor_set(v___x_3227_, 0, v_expectedID_3203_);
v___x_3264_ = v___x_3227_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_expectedID_3203_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_a_3262_);
v___x_3264_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3266_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___x_3264_);
v___x_3266_ = v___x_3209_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3270_; uint8_t v_code_3271_; lean_object* v_message_3272_; lean_object* v_data_x3f_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___x_3305_; lean_object* v___y_3307_; 
lean_del_object(v___x_3214_);
lean_dec(v_expectedID_3203_);
v_id_3270_ = lean_ctor_get(v_a_3212_, 0);
lean_inc(v_id_3270_);
v_code_3271_ = lean_ctor_get_uint8(v_a_3212_, sizeof(void*)*3);
v_message_3272_ = lean_ctor_get(v_a_3212_, 1);
lean_inc_ref(v_message_3272_);
v_data_x3f_3273_ = lean_ctor_get(v_a_3212_, 2);
lean_inc(v_data_x3f_3273_);
lean_dec_ref_known(v_a_3212_, 3);
v___x_3274_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3275_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3305_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3270_))
{
case 0:
{
lean_object* v_s_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
v_s_3323_ = lean_ctor_get(v_id_3270_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_id_3270_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v_id_3270_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_s_3323_);
lean_dec(v_id_3270_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
lean_ctor_set_tag(v___x_3325_, 3);
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_s_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
v___y_3307_ = v___x_3328_;
goto v___jp_3306_;
}
}
}
case 1:
{
lean_object* v_n_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
v_n_3331_ = lean_ctor_get(v_id_3270_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v_id_3270_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v_id_3270_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_n_3331_);
lean_dec(v_id_3270_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set_tag(v___x_3333_, 2);
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_n_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
v___y_3307_ = v___x_3336_;
goto v___jp_3306_;
}
}
}
default: 
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_box(0);
v___y_3307_ = v___x_3339_;
goto v___jp_3306_;
}
}
v___jp_3276_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3303_; 
lean_inc(v___y_3280_);
lean_inc_ref(v___y_3278_);
v___x_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___y_3278_);
lean_ctor_set(v___x_3281_, 1, v___y_3280_);
v___x_3282_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3283_, 0, v_message_3272_);
v___x_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3282_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = lean_box(0);
v___x_3286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3281_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3289_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3288_, v_data_x3f_3273_);
lean_dec(v_data_x3f_3273_);
v___x_3290_ = l_List_appendTR___redArg(v___x_3287_, v___x_3289_);
v___x_3291_ = l_Lean_Json_mkObj(v___x_3290_);
lean_dec(v___x_3290_);
lean_inc_ref(v___y_3277_);
v___x_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___y_3277_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
lean_ctor_set(v___x_3293_, 1, v___x_3285_);
v___x_3294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___y_3279_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3275_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = l_Lean_Json_mkObj(v___x_3295_);
lean_dec_ref_known(v___x_3295_, 2);
v___x_3297_ = l_Lean_Json_compress(v___x_3296_);
v___x_3298_ = lean_string_append(v___x_3274_, v___x_3297_);
lean_dec_ref(v___x_3297_);
v___x_3299_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3300_ = lean_string_append(v___x_3298_, v___x_3299_);
v___x_3301_ = lean_mk_io_user_error(v___x_3300_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 1);
lean_ctor_set(v___x_3209_, 0, v___x_3301_);
v___x_3303_ = v___x_3209_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3301_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
v___jp_3306_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3305_);
lean_ctor_set(v___x_3308_, 1, v___y_3307_);
v___x_3309_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3310_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3271_)
{
case 0:
{
lean_object* v___x_3311_; 
v___x_3311_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3311_;
goto v___jp_3276_;
}
case 1:
{
lean_object* v___x_3312_; 
v___x_3312_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3312_;
goto v___jp_3276_;
}
case 2:
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3313_;
goto v___jp_3276_;
}
case 3:
{
lean_object* v___x_3314_; 
v___x_3314_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3314_;
goto v___jp_3276_;
}
case 4:
{
lean_object* v___x_3315_; 
v___x_3315_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3315_;
goto v___jp_3276_;
}
case 5:
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3316_;
goto v___jp_3276_;
}
case 6:
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3317_;
goto v___jp_3276_;
}
case 7:
{
lean_object* v___x_3318_; 
v___x_3318_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3318_;
goto v___jp_3276_;
}
case 8:
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3319_;
goto v___jp_3276_;
}
case 9:
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3320_;
goto v___jp_3276_;
}
case 10:
{
lean_object* v___x_3321_; 
v___x_3321_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3321_;
goto v___jp_3276_;
}
default: 
{
lean_object* v___x_3322_; 
v___x_3322_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3277_ = v___x_3309_;
v___y_3278_ = v___x_3310_;
v___y_3279_ = v___x_3308_;
v___y_3280_ = v___x_3322_;
goto v___jp_3276_;
}
}
}
}
default: 
{
lean_del_object(v___x_3214_);
lean_dec(v_a_3212_);
lean_del_object(v___x_3209_);
goto _start;
}
}
v___jp_3216_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3219_ = lean_string_append(v___y_3217_, v___y_3218_);
lean_dec_ref(v___y_3218_);
v___x_3220_ = lean_mk_io_user_error(v___x_3219_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set_tag(v___x_3214_, 1);
lean_ctor_set(v___x_3214_, 0, v___x_3220_);
v___x_3222_ = v___x_3214_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_del_object(v___x_3209_);
lean_dec(v_expectedID_3203_);
v_a_3342_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3211_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3211_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v_expectedID_3203_);
v_a_3351_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3206_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3206_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1___boxed(lean_object* v_expectedID_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v_expectedID_3359_, v_a_3360_);
lean_dec_ref(v_a_3360_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(lean_object* v_v_3363_){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_v_3363_);
v___x_3365_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_v_3366_);
lean_dec_ref(v_v_3366_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(lean_object* v_h_3368_, lean_object* v_r_3369_){
_start:
{
lean_object* v_id_3371_; lean_object* v_method_3372_; lean_object* v_param_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3393_; 
v_id_3371_ = lean_ctor_get(v_r_3369_, 0);
v_method_3372_ = lean_ctor_get(v_r_3369_, 1);
v_param_3373_ = lean_ctor_get(v_r_3369_, 2);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_r_3369_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3375_ = v_r_3369_;
v_isShared_3376_ = v_isSharedCheck_3393_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_param_3373_);
lean_inc(v_method_3372_);
lean_inc(v_id_3371_);
lean_dec(v_r_3369_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3393_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___y_3378_; lean_object* v___x_3383_; 
v___x_3383_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_param_3373_);
lean_dec(v_param_3373_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v___x_3384_; 
lean_dec_ref_known(v___x_3383_, 1);
v___x_3384_ = lean_box(0);
v___y_3378_ = v___x_3384_;
goto v___jp_3377_;
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
v_a_3385_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3383_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3383_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
v___y_3378_ = v___x_3390_;
goto v___jp_3377_;
}
}
}
v___jp_3377_:
{
lean_object* v___x_3380_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 2, v___y_3378_);
v___x_3380_ = v___x_3375_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_id_3371_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_method_3372_);
lean_ctor_set(v_reuseFailAlloc_3382_, 2, v___y_3378_);
v___x_3380_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_IO_FS_Stream_writeLspMessage(v_h_3368_, v___x_3380_);
return v___x_3381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0___boxed(lean_object* v_h_3394_, lean_object* v_r_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_h_3394_, v_r_3395_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(lean_object* v_r_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v___x_3401_; lean_object* v_a_3402_; lean_object* v___x_3403_; 
v___x_3401_ = l_Lean_Lsp_Ipc_stdin(v_a_3399_);
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref(v___x_3401_);
v___x_3403_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_a_3402_, v_r_3398_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0___boxed(lean_object* v_r_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v_r_3404_, v_a_3405_);
lean_dec_ref(v_a_3405_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(lean_object* v_requestNo_3411_, lean_object* v_item_3412_, lean_object* v_visited_3413_, lean_object* v_a_3414_){
_start:
{
lean_object* v_module_3416_; lean_object* v_name_3417_; uint8_t v___x_3418_; 
v_module_3416_ = lean_ctor_get(v_item_3412_, 0);
v_name_3417_ = lean_ctor_get(v_module_3416_, 0);
v___x_3418_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3417_, v_visited_3413_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
lean_inc(v_requestNo_3411_);
v___x_3419_ = l_Lean_JsonNumber_fromNat(v_requestNo_3411_);
v___x_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
v___x_3421_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0));
lean_inc_ref(v_module_3416_);
lean_inc_ref(v___x_3420_);
v___x_3422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
lean_ctor_set(v___x_3422_, 2, v_module_3416_);
v___x_3423_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v___x_3422_, v_a_3414_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v___x_3424_; 
lean_dec_ref_known(v___x_3423_, 1);
v___x_3424_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3420_, v_a_3414_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___y_3427_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
if (v___x_3418_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = lean_box(0);
lean_inc_ref(v_name_3417_);
v___x_3470_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3417_, v___x_3469_, v_visited_3413_);
v___y_3427_ = v___x_3470_;
goto v___jp_3426_;
}
else
{
v___y_3427_ = v_visited_3413_;
goto v___jp_3426_;
}
v___jp_3426_:
{
lean_object* v_result_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3467_; 
v_result_3428_ = lean_ctor_get(v_a_3425_, 1);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_a_3425_);
if (v_isSharedCheck_3467_ == 0)
{
lean_object* v_unused_3468_; 
v_unused_3468_ = lean_ctor_get(v_a_3425_, 0);
lean_dec(v_unused_3468_);
v___x_3430_ = v_a_3425_;
v_isShared_3431_ = v_isSharedCheck_3467_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_result_3428_);
lean_dec(v_a_3425_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3467_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3432_ = lean_unsigned_to_nat(1u);
v___x_3433_ = lean_nat_add(v_requestNo_3411_, v___x_3432_);
lean_dec(v_requestNo_3411_);
v___x_3434_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 1, v___x_3434_);
lean_ctor_set(v___x_3430_, 0, v___x_3433_);
v___x_3436_ = v___x_3430_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
size_t v_sz_3437_; size_t v___x_3438_; lean_object* v___x_3439_; 
v_sz_3437_ = lean_array_size(v_result_3428_);
v___x_3438_ = ((size_t)0ULL);
v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___y_3427_, v_result_3428_, v_sz_3437_, v___x_3438_, v___x_3436_, v_a_3414_);
lean_dec(v_result_3428_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3457_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3457_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3457_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v_fst_3444_; lean_object* v_snd_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3456_; 
v_fst_3444_ = lean_ctor_get(v_a_3440_, 0);
v_snd_3445_ = lean_ctor_get(v_a_3440_, 1);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_a_3440_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3447_ = v_a_3440_;
v_isShared_3448_ = v_isSharedCheck_3456_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_snd_3445_);
lean_inc(v_fst_3444_);
lean_dec(v_a_3440_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3456_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3449_, 0, v_item_3412_);
lean_ctor_set(v___x_3449_, 1, v_snd_3445_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 1, v_fst_3444_);
lean_ctor_set(v___x_3447_, 0, v___x_3449_);
v___x_3451_ = v___x_3447_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_fst_3444_);
v___x_3451_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3453_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3451_);
v___x_3453_ = v___x_3442_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec_ref(v_item_3412_);
v_a_3458_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3439_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3439_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v_visited_3413_);
lean_dec_ref(v_item_3412_);
lean_dec(v_requestNo_3411_);
v_a_3471_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3424_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3424_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec_ref_known(v___x_3420_, 1);
lean_dec(v_visited_3413_);
lean_dec_ref(v_item_3412_);
lean_dec(v_requestNo_3411_);
v_a_3479_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3423_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3423_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
lean_dec(v_visited_3413_);
v___x_3487_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v_item_3412_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
v___x_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
lean_ctor_set(v___x_3489_, 1, v_requestNo_3411_);
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
return v___x_3490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(lean_object* v___x_3491_, lean_object* v_as_3492_, size_t v_sz_3493_, size_t v_i_3494_, lean_object* v_b_3495_, lean_object* v___y_3496_){
_start:
{
uint8_t v___x_3498_; 
v___x_3498_ = lean_usize_dec_lt(v_i_3494_, v_sz_3493_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
lean_dec(v___x_3491_);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v_b_3495_);
return v___x_3499_;
}
else
{
lean_object* v_fst_3500_; lean_object* v_snd_3501_; lean_object* v_a_3502_; lean_object* v___x_3503_; 
v_fst_3500_ = lean_ctor_get(v_b_3495_, 0);
lean_inc(v_fst_3500_);
v_snd_3501_ = lean_ctor_get(v_b_3495_, 1);
lean_inc(v_snd_3501_);
lean_dec_ref(v_b_3495_);
v_a_3502_ = lean_array_uget_borrowed(v_as_3492_, v_i_3494_);
lean_inc(v___x_3491_);
lean_inc(v_a_3502_);
v___x_3503_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_fst_3500_, v_a_3502_, v___x_3491_, v___y_3496_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v_fst_3505_; lean_object* v_snd_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3517_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v_fst_3505_ = lean_ctor_get(v_a_3504_, 0);
v_snd_3506_ = lean_ctor_get(v_a_3504_, 1);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_a_3504_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3508_ = v_a_3504_;
v_isShared_3509_ = v_isSharedCheck_3517_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_snd_3506_);
lean_inc(v_fst_3505_);
lean_dec(v_a_3504_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3517_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3512_; 
v___x_3510_ = lean_array_push(v_snd_3501_, v_fst_3505_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v___x_3510_);
lean_ctor_set(v___x_3508_, 0, v_snd_3506_);
v___x_3512_ = v___x_3508_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_snd_3506_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
size_t v___x_3513_; size_t v___x_3514_; 
v___x_3513_ = ((size_t)1ULL);
v___x_3514_ = lean_usize_add(v_i_3494_, v___x_3513_);
v_i_3494_ = v___x_3514_;
v_b_3495_ = v___x_3512_;
goto _start;
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec(v_snd_3501_);
lean_dec(v___x_3491_);
v_a_3518_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3503_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3503_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2___boxed(lean_object* v___x_3526_, lean_object* v_as_3527_, lean_object* v_sz_3528_, lean_object* v_i_3529_, lean_object* v_b_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
size_t v_sz_boxed_3533_; size_t v_i_boxed_3534_; lean_object* v_res_3535_; 
v_sz_boxed_3533_ = lean_unbox_usize(v_sz_3528_);
lean_dec(v_sz_3528_);
v_i_boxed_3534_ = lean_unbox_usize(v_i_3529_);
lean_dec(v_i_3529_);
v_res_3535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___x_3526_, v_as_3527_, v_sz_boxed_3533_, v_i_boxed_3534_, v_b_3530_, v___y_3531_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v_as_3527_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___boxed(lean_object* v_requestNo_3536_, lean_object* v_item_3537_, lean_object* v_visited_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_requestNo_3536_, v_item_3537_, v_visited_3538_, v_a_3539_);
lean_dec_ref(v_a_3539_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(lean_object* v_v_3542_){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(v_v_3542_);
v___x_3544_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(lean_object* v_h_3545_, lean_object* v_r_3546_){
_start:
{
lean_object* v_id_3548_; lean_object* v_method_3549_; lean_object* v_param_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3570_; 
v_id_3548_ = lean_ctor_get(v_r_3546_, 0);
v_method_3549_ = lean_ctor_get(v_r_3546_, 1);
v_param_3550_ = lean_ctor_get(v_r_3546_, 2);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_r_3546_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3552_ = v_r_3546_;
v_isShared_3553_ = v_isSharedCheck_3570_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_param_3550_);
lean_inc(v_method_3549_);
lean_inc(v_id_3548_);
lean_dec(v_r_3546_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3570_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___y_3555_; lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(v_param_3550_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v___x_3561_; 
lean_dec_ref_known(v___x_3560_, 1);
v___x_3561_ = lean_box(0);
v___y_3555_ = v___x_3561_;
goto v___jp_3554_;
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
v_a_3562_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3560_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3560_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
v___y_3555_ = v___x_3567_;
goto v___jp_3554_;
}
}
}
v___jp_3554_:
{
lean_object* v___x_3557_; 
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 2, v___y_3555_);
v___x_3557_ = v___x_3552_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_id_3548_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_method_3549_);
lean_ctor_set(v_reuseFailAlloc_3559_, 2, v___y_3555_);
v___x_3557_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_IO_FS_Stream_writeLspMessage(v_h_3545_, v___x_3557_);
return v___x_3558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0___boxed(lean_object* v_h_3571_, lean_object* v_r_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_h_3571_, v_r_3572_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(lean_object* v_r_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v___x_3578_; lean_object* v_a_3579_; lean_object* v___x_3580_; 
v___x_3578_ = l_Lean_Lsp_Ipc_stdin(v_a_3576_);
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_a_3579_);
lean_dec_ref(v___x_3578_);
v___x_3580_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_a_3579_, v_r_3575_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0___boxed(lean_object* v_r_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v_r_3581_, v_a_3582_);
lean_dec_ref(v_a_3582_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(lean_object* v_x_3587_){
_start:
{
if (lean_obj_tag(v_x_3587_) == 0)
{
lean_object* v___x_3588_; 
v___x_3588_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0));
return v___x_3588_;
}
else
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v_x_3587_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3606_; 
v_a_3598_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3600_ = v___x_3589_;
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3589_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3602_, 0, v_a_3598_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3602_);
v___x_3604_ = v___x_3600_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(lean_object* v_expectedID_3607_, lean_object* v_a_3608_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_Lsp_Ipc_stdout(v_a_3608_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3754_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3754_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3754_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_IO_FS_Stream_readLspMessage(v_a_3611_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3745_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3618_ = v___x_3615_;
v_isShared_3619_ = v_isSharedCheck_3745_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3615_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3745_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___y_3621_; lean_object* v___y_3622_; 
switch(lean_obj_tag(v_a_3616_))
{
case 2:
{
lean_object* v_id_3628_; lean_object* v_result_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3673_; 
v_id_3628_ = lean_ctor_get(v_a_3616_, 0);
v_result_3629_ = lean_ctor_get(v_a_3616_, 1);
v_isSharedCheck_3673_ = !lean_is_exclusive(v_a_3616_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3631_ = v_a_3616_;
v_isShared_3632_ = v_isSharedCheck_3673_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_result_3629_);
lean_inc(v_id_3628_);
lean_dec(v_a_3616_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3673_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
uint8_t v___x_3633_; 
v___x_3633_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3628_, v_expectedID_3607_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; lean_object* v___y_3636_; 
lean_del_object(v___x_3631_);
lean_dec(v_result_3629_);
lean_del_object(v___x_3613_);
v___x_3634_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3607_))
{
case 0:
{
lean_object* v_s_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v_s_3647_ = lean_ctor_get(v_expectedID_3607_, 0);
lean_inc_ref(v_s_3647_);
lean_dec_ref_known(v_expectedID_3607_, 1);
v___x_3648_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3649_ = lean_string_append(v___x_3648_, v_s_3647_);
lean_dec_ref(v_s_3647_);
v___x_3650_ = lean_string_append(v___x_3649_, v___x_3648_);
v___y_3636_ = v___x_3650_;
goto v___jp_3635_;
}
case 1:
{
lean_object* v_n_3651_; lean_object* v___x_3652_; 
v_n_3651_ = lean_ctor_get(v_expectedID_3607_, 0);
lean_inc_ref(v_n_3651_);
lean_dec_ref_known(v_expectedID_3607_, 1);
v___x_3652_ = l_Lean_JsonNumber_toString(v_n_3651_);
v___y_3636_ = v___x_3652_;
goto v___jp_3635_;
}
default: 
{
lean_object* v___x_3653_; 
v___x_3653_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3636_ = v___x_3653_;
goto v___jp_3635_;
}
}
v___jp_3635_:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3637_ = lean_string_append(v___x_3634_, v___y_3636_);
lean_dec_ref(v___y_3636_);
v___x_3638_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3639_ = lean_string_append(v___x_3637_, v___x_3638_);
switch(lean_obj_tag(v_id_3628_))
{
case 0:
{
lean_object* v_s_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v_s_3640_ = lean_ctor_get(v_id_3628_, 0);
lean_inc_ref(v_s_3640_);
lean_dec_ref_known(v_id_3628_, 1);
v___x_3641_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3642_ = lean_string_append(v___x_3641_, v_s_3640_);
lean_dec_ref(v_s_3640_);
v___x_3643_ = lean_string_append(v___x_3642_, v___x_3641_);
v___y_3621_ = v___x_3639_;
v___y_3622_ = v___x_3643_;
goto v___jp_3620_;
}
case 1:
{
lean_object* v_n_3644_; lean_object* v___x_3645_; 
v_n_3644_ = lean_ctor_get(v_id_3628_, 0);
lean_inc_ref(v_n_3644_);
lean_dec_ref_known(v_id_3628_, 1);
v___x_3645_ = l_Lean_JsonNumber_toString(v_n_3644_);
v___y_3621_ = v___x_3639_;
v___y_3622_ = v___x_3645_;
goto v___jp_3620_;
}
default: 
{
lean_object* v___x_3646_; 
v___x_3646_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3621_ = v___x_3639_;
v___y_3622_ = v___x_3646_;
goto v___jp_3620_;
}
}
}
}
else
{
lean_object* v___x_3654_; 
lean_dec(v_id_3628_);
lean_del_object(v___x_3618_);
lean_inc(v_result_3629_);
v___x_3654_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(v_result_3629_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3664_; 
lean_del_object(v___x_3631_);
lean_dec(v_expectedID_3607_);
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3655_);
lean_dec_ref_known(v___x_3654_, 1);
v___x_3656_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3657_ = l_Lean_Json_compress(v_result_3629_);
v___x_3658_ = lean_string_append(v___x_3656_, v___x_3657_);
lean_dec_ref(v___x_3657_);
v___x_3659_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3660_ = lean_string_append(v___x_3658_, v___x_3659_);
v___x_3661_ = lean_string_append(v___x_3660_, v_a_3655_);
lean_dec(v_a_3655_);
v___x_3662_ = lean_mk_io_user_error(v___x_3661_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set_tag(v___x_3613_, 1);
lean_ctor_set(v___x_3613_, 0, v___x_3662_);
v___x_3664_ = v___x_3613_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; 
lean_dec(v_result_3629_);
v_a_3666_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3654_, 1);
if (v_isShared_3632_ == 0)
{
lean_ctor_set_tag(v___x_3631_, 0);
lean_ctor_set(v___x_3631_, 1, v_a_3666_);
lean_ctor_set(v___x_3631_, 0, v_expectedID_3607_);
v___x_3668_ = v___x_3631_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_expectedID_3607_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_a_3666_);
v___x_3668_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3670_; 
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v___x_3668_);
v___x_3670_ = v___x_3613_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3674_; uint8_t v_code_3675_; lean_object* v_message_3676_; lean_object* v_data_x3f_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___x_3709_; lean_object* v___y_3711_; 
lean_del_object(v___x_3618_);
lean_dec(v_expectedID_3607_);
v_id_3674_ = lean_ctor_get(v_a_3616_, 0);
lean_inc(v_id_3674_);
v_code_3675_ = lean_ctor_get_uint8(v_a_3616_, sizeof(void*)*3);
v_message_3676_ = lean_ctor_get(v_a_3616_, 1);
lean_inc_ref(v_message_3676_);
v_data_x3f_3677_ = lean_ctor_get(v_a_3616_, 2);
lean_inc(v_data_x3f_3677_);
lean_dec_ref_known(v_a_3616_, 3);
v___x_3678_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3679_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3709_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3674_))
{
case 0:
{
lean_object* v_s_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
v_s_3727_ = lean_ctor_get(v_id_3674_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_id_3674_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v_id_3674_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_s_3727_);
lean_dec(v_id_3674_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
lean_ctor_set_tag(v___x_3729_, 3);
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_s_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
v___y_3711_ = v___x_3732_;
goto v___jp_3710_;
}
}
}
case 1:
{
lean_object* v_n_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_n_3735_ = lean_ctor_get(v_id_3674_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_id_3674_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v_id_3674_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_n_3735_);
lean_dec(v_id_3674_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set_tag(v___x_3737_, 2);
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_n_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
v___y_3711_ = v___x_3740_;
goto v___jp_3710_;
}
}
}
default: 
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_box(0);
v___y_3711_ = v___x_3743_;
goto v___jp_3710_;
}
}
v___jp_3680_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3707_; 
lean_inc(v___y_3684_);
lean_inc_ref(v___y_3681_);
v___x_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___y_3681_);
lean_ctor_set(v___x_3685_, 1, v___y_3684_);
v___x_3686_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3687_, 0, v_message_3676_);
v___x_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3686_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = lean_box(0);
v___x_3690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3685_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
v___x_3692_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3693_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3692_, v_data_x3f_3677_);
lean_dec(v_data_x3f_3677_);
v___x_3694_ = l_List_appendTR___redArg(v___x_3691_, v___x_3693_);
v___x_3695_ = l_Lean_Json_mkObj(v___x_3694_);
lean_dec(v___x_3694_);
lean_inc_ref(v___y_3683_);
v___x_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___y_3683_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
lean_ctor_set(v___x_3697_, 1, v___x_3689_);
v___x_3698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___y_3682_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3679_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v___x_3700_ = l_Lean_Json_mkObj(v___x_3699_);
lean_dec_ref_known(v___x_3699_, 2);
v___x_3701_ = l_Lean_Json_compress(v___x_3700_);
v___x_3702_ = lean_string_append(v___x_3678_, v___x_3701_);
lean_dec_ref(v___x_3701_);
v___x_3703_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3704_ = lean_string_append(v___x_3702_, v___x_3703_);
v___x_3705_ = lean_mk_io_user_error(v___x_3704_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set_tag(v___x_3613_, 1);
lean_ctor_set(v___x_3613_, 0, v___x_3705_);
v___x_3707_ = v___x_3613_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
v___jp_3710_:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3709_);
lean_ctor_set(v___x_3712_, 1, v___y_3711_);
v___x_3713_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3714_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3675_)
{
case 0:
{
lean_object* v___x_3715_; 
v___x_3715_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3715_;
goto v___jp_3680_;
}
case 1:
{
lean_object* v___x_3716_; 
v___x_3716_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3716_;
goto v___jp_3680_;
}
case 2:
{
lean_object* v___x_3717_; 
v___x_3717_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3717_;
goto v___jp_3680_;
}
case 3:
{
lean_object* v___x_3718_; 
v___x_3718_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3718_;
goto v___jp_3680_;
}
case 4:
{
lean_object* v___x_3719_; 
v___x_3719_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3719_;
goto v___jp_3680_;
}
case 5:
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3720_;
goto v___jp_3680_;
}
case 6:
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3721_;
goto v___jp_3680_;
}
case 7:
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3722_;
goto v___jp_3680_;
}
case 8:
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3723_;
goto v___jp_3680_;
}
case 9:
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3724_;
goto v___jp_3680_;
}
case 10:
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3725_;
goto v___jp_3680_;
}
default: 
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3681_ = v___x_3714_;
v___y_3682_ = v___x_3712_;
v___y_3683_ = v___x_3713_;
v___y_3684_ = v___x_3726_;
goto v___jp_3680_;
}
}
}
}
default: 
{
lean_del_object(v___x_3618_);
lean_dec(v_a_3616_);
lean_del_object(v___x_3613_);
goto _start;
}
}
v___jp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3626_; 
v___x_3623_ = lean_string_append(v___y_3621_, v___y_3622_);
lean_dec_ref(v___y_3622_);
v___x_3624_ = lean_mk_io_user_error(v___x_3623_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set_tag(v___x_3618_, 1);
lean_ctor_set(v___x_3618_, 0, v___x_3624_);
v___x_3626_ = v___x_3618_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_del_object(v___x_3613_);
lean_dec(v_expectedID_3607_);
v_a_3746_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3615_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3615_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec(v_expectedID_3607_);
v_a_3755_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3610_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3610_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1___boxed(lean_object* v_expectedID_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v_expectedID_3763_, v_a_3764_);
lean_dec_ref(v_a_3764_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports(lean_object* v_requestNo_3771_, lean_object* v_uri_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
lean_inc(v_requestNo_3771_);
v___x_3775_ = l_Lean_JsonNumber_fromNat(v_requestNo_3771_);
v___x_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
v___x_3777_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_3776_);
v___x_3778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3776_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
lean_ctor_set(v___x_3778_, 2, v_uri_3772_);
v___x_3779_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_3778_, v_a_3773_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v___x_3780_; 
lean_dec_ref_known(v___x_3779_, 1);
v___x_3780_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_3776_, v_a_3773_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3839_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3783_ = v___x_3780_;
v_isShared_3784_ = v_isSharedCheck_3839_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3780_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3839_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v_result_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3837_; 
v_result_3785_ = lean_ctor_get(v_a_3781_, 1);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_a_3781_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; 
v_unused_3838_ = lean_ctor_get(v_a_3781_, 0);
lean_dec(v_unused_3838_);
v___x_3787_ = v_a_3781_;
v_isShared_3788_ = v_isSharedCheck_3837_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_result_3785_);
lean_dec(v_a_3781_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3837_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = lean_unsigned_to_nat(1u);
v___x_3790_ = lean_nat_add(v_requestNo_3771_, v___x_3789_);
lean_dec(v_requestNo_3771_);
if (lean_obj_tag(v_result_3785_) == 1)
{
lean_object* v_val_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3829_; 
lean_del_object(v___x_3783_);
v_val_3791_ = lean_ctor_get(v_result_3785_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_result_3785_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3793_ = v_result_3785_;
v_isShared_3794_ = v_isSharedCheck_3829_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_val_3791_);
lean_dec(v_result_3785_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3829_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3795_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 1, v___x_3795_);
lean_ctor_set(v___x_3787_, 0, v_val_3791_);
v___x_3797_ = v___x_3787_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_val_3791_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = lean_box(1);
v___x_3799_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v___x_3790_, v___x_3797_, v___x_3798_, v_a_3773_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3819_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3802_ = v___x_3799_;
v_isShared_3803_ = v_isSharedCheck_3819_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3819_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v_fst_3804_; lean_object* v_snd_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3818_; 
v_fst_3804_ = lean_ctor_get(v_a_3800_, 0);
v_snd_3805_ = lean_ctor_get(v_a_3800_, 1);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_a_3800_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3807_ = v_a_3800_;
v_isShared_3808_ = v_isSharedCheck_3818_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_snd_3805_);
lean_inc(v_fst_3804_);
lean_dec(v_a_3800_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3818_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 0, v_fst_3804_);
v___x_3810_ = v___x_3793_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_fst_3804_);
v___x_3810_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___x_3812_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3810_);
v___x_3812_ = v___x_3807_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3810_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_snd_3805_);
v___x_3812_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3814_; 
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v___x_3812_);
v___x_3814_ = v___x_3802_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_del_object(v___x_3793_);
v_a_3820_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3799_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3799_);
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
}
else
{
lean_object* v___x_3830_; lean_object* v___x_3832_; 
lean_dec(v_result_3785_);
v___x_3830_ = lean_box(0);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 1, v___x_3790_);
lean_ctor_set(v___x_3787_, 0, v___x_3830_);
v___x_3832_ = v___x_3787_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3830_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v___x_3790_);
v___x_3832_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
lean_object* v___x_3834_; 
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v___x_3832_);
v___x_3834_ = v___x_3783_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_dec(v_requestNo_3771_);
v_a_3840_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3780_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3780_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
lean_dec_ref_known(v___x_3776_, 1);
lean_dec(v_requestNo_3771_);
v_a_3848_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3779_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3779_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___boxed(lean_object* v_requestNo_3856_, lean_object* v_uri_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImports(v_requestNo_3856_, v_uri_3857_, v_a_3858_);
lean_dec_ref(v_a_3858_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(lean_object* v_v_3861_){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_v_3861_);
v___x_3863_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3862_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_v_3864_);
lean_dec_ref(v_v_3864_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(lean_object* v_h_3866_, lean_object* v_r_3867_){
_start:
{
lean_object* v_id_3869_; lean_object* v_method_3870_; lean_object* v_param_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3891_; 
v_id_3869_ = lean_ctor_get(v_r_3867_, 0);
v_method_3870_ = lean_ctor_get(v_r_3867_, 1);
v_param_3871_ = lean_ctor_get(v_r_3867_, 2);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_r_3867_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3873_ = v_r_3867_;
v_isShared_3874_ = v_isSharedCheck_3891_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_param_3871_);
lean_inc(v_method_3870_);
lean_inc(v_id_3869_);
lean_dec(v_r_3867_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3891_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___y_3876_; lean_object* v___x_3881_; 
v___x_3881_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_param_3871_);
lean_dec(v_param_3871_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v___x_3882_; 
lean_dec_ref_known(v___x_3881_, 1);
v___x_3882_ = lean_box(0);
v___y_3876_ = v___x_3882_;
goto v___jp_3875_;
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
v_a_3883_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3881_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3881_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
v___y_3876_ = v___x_3888_;
goto v___jp_3875_;
}
}
}
v___jp_3875_:
{
lean_object* v___x_3878_; 
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 2, v___y_3876_);
v___x_3878_ = v___x_3873_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_id_3869_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v_method_3870_);
lean_ctor_set(v_reuseFailAlloc_3880_, 2, v___y_3876_);
v___x_3878_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3879_; 
v___x_3879_ = l_IO_FS_Stream_writeLspMessage(v_h_3866_, v___x_3878_);
return v___x_3879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0___boxed(lean_object* v_h_3892_, lean_object* v_r_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_h_3892_, v_r_3893_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(lean_object* v_r_3896_, lean_object* v_a_3897_){
_start:
{
lean_object* v___x_3899_; lean_object* v_a_3900_; lean_object* v___x_3901_; 
v___x_3899_ = l_Lean_Lsp_Ipc_stdin(v_a_3897_);
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref(v___x_3899_);
v___x_3901_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_a_3900_, v_r_3896_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0___boxed(lean_object* v_r_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v_r_3902_, v_a_3903_);
lean_dec_ref(v_a_3903_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(lean_object* v_requestNo_3907_, lean_object* v_item_3908_, lean_object* v_visited_3909_, lean_object* v_a_3910_){
_start:
{
lean_object* v_module_3912_; lean_object* v_name_3913_; uint8_t v___x_3914_; 
v_module_3912_ = lean_ctor_get(v_item_3908_, 0);
v_name_3913_ = lean_ctor_get(v_module_3912_, 0);
v___x_3914_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3913_, v_visited_3909_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
lean_inc(v_requestNo_3907_);
v___x_3915_ = l_Lean_JsonNumber_fromNat(v_requestNo_3907_);
v___x_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
v___x_3917_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0));
lean_inc_ref(v_module_3912_);
lean_inc_ref(v___x_3916_);
v___x_3918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3916_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
lean_ctor_set(v___x_3918_, 2, v_module_3912_);
v___x_3919_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v___x_3918_, v_a_3910_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v___x_3920_; 
lean_dec_ref_known(v___x_3919_, 1);
v___x_3920_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3916_, v_a_3910_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v___y_3923_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_a_3921_);
lean_dec_ref_known(v___x_3920_, 1);
if (v___x_3914_ == 0)
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3965_ = lean_box(0);
lean_inc_ref(v_name_3913_);
v___x_3966_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3913_, v___x_3965_, v_visited_3909_);
v___y_3923_ = v___x_3966_;
goto v___jp_3922_;
}
else
{
v___y_3923_ = v_visited_3909_;
goto v___jp_3922_;
}
v___jp_3922_:
{
lean_object* v_result_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3963_; 
v_result_3924_ = lean_ctor_get(v_a_3921_, 1);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_a_3921_);
if (v_isSharedCheck_3963_ == 0)
{
lean_object* v_unused_3964_; 
v_unused_3964_ = lean_ctor_get(v_a_3921_, 0);
lean_dec(v_unused_3964_);
v___x_3926_ = v_a_3921_;
v_isShared_3927_ = v_isSharedCheck_3963_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_result_3924_);
lean_dec(v_a_3921_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3963_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3932_; 
v___x_3928_ = lean_unsigned_to_nat(1u);
v___x_3929_ = lean_nat_add(v_requestNo_3907_, v___x_3928_);
lean_dec(v_requestNo_3907_);
v___x_3930_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 1, v___x_3930_);
lean_ctor_set(v___x_3926_, 0, v___x_3929_);
v___x_3932_ = v___x_3926_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v___x_3930_);
v___x_3932_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
size_t v_sz_3933_; size_t v___x_3934_; lean_object* v___x_3935_; 
v_sz_3933_ = lean_array_size(v_result_3924_);
v___x_3934_ = ((size_t)0ULL);
v___x_3935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___y_3923_, v_result_3924_, v_sz_3933_, v___x_3934_, v___x_3932_, v_a_3910_);
lean_dec(v_result_3924_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3953_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3938_ = v___x_3935_;
v_isShared_3939_ = v_isSharedCheck_3953_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3935_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3953_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v_fst_3940_; lean_object* v_snd_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3952_; 
v_fst_3940_ = lean_ctor_get(v_a_3936_, 0);
v_snd_3941_ = lean_ctor_get(v_a_3936_, 1);
v_isSharedCheck_3952_ = !lean_is_exclusive(v_a_3936_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3943_ = v_a_3936_;
v_isShared_3944_ = v_isSharedCheck_3952_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_snd_3941_);
lean_inc(v_fst_3940_);
lean_dec(v_a_3936_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3952_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3945_; lean_object* v___x_3947_; 
v___x_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3945_, 0, v_item_3908_);
lean_ctor_set(v___x_3945_, 1, v_snd_3941_);
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 1, v_fst_3940_);
lean_ctor_set(v___x_3943_, 0, v___x_3945_);
v___x_3947_ = v___x_3943_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3945_);
lean_ctor_set(v_reuseFailAlloc_3951_, 1, v_fst_3940_);
v___x_3947_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v___x_3949_; 
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3947_);
v___x_3949_ = v___x_3938_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3947_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec_ref(v_item_3908_);
v_a_3954_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3935_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3935_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec(v_visited_3909_);
lean_dec_ref(v_item_3908_);
lean_dec(v_requestNo_3907_);
v_a_3967_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3920_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3920_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec_ref_known(v___x_3916_, 1);
lean_dec(v_visited_3909_);
lean_dec_ref(v_item_3908_);
lean_dec(v_requestNo_3907_);
v_a_3975_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3919_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3919_);
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
else
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
lean_dec(v_visited_3909_);
v___x_3983_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3984_, 0, v_item_3908_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
lean_ctor_set(v___x_3985_, 1, v_requestNo_3907_);
v___x_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
return v___x_3986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(lean_object* v___x_3987_, lean_object* v_as_3988_, size_t v_sz_3989_, size_t v_i_3990_, lean_object* v_b_3991_, lean_object* v___y_3992_){
_start:
{
uint8_t v___x_3994_; 
v___x_3994_ = lean_usize_dec_lt(v_i_3990_, v_sz_3989_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3995_; 
lean_dec(v___x_3987_);
v___x_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3995_, 0, v_b_3991_);
return v___x_3995_;
}
else
{
lean_object* v_fst_3996_; lean_object* v_snd_3997_; lean_object* v_a_3998_; lean_object* v___x_3999_; 
v_fst_3996_ = lean_ctor_get(v_b_3991_, 0);
lean_inc(v_fst_3996_);
v_snd_3997_ = lean_ctor_get(v_b_3991_, 1);
lean_inc(v_snd_3997_);
lean_dec_ref(v_b_3991_);
v_a_3998_ = lean_array_uget_borrowed(v_as_3988_, v_i_3990_);
lean_inc(v___x_3987_);
lean_inc(v_a_3998_);
v___x_3999_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_fst_3996_, v_a_3998_, v___x_3987_, v___y_3992_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v_fst_4001_; lean_object* v_snd_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4013_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___x_3999_, 1);
v_fst_4001_ = lean_ctor_get(v_a_4000_, 0);
v_snd_4002_ = lean_ctor_get(v_a_4000_, 1);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_a_4000_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4004_ = v_a_4000_;
v_isShared_4005_ = v_isSharedCheck_4013_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_snd_4002_);
lean_inc(v_fst_4001_);
lean_dec(v_a_4000_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4013_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4006_; lean_object* v___x_4008_; 
v___x_4006_ = lean_array_push(v_snd_3997_, v_fst_4001_);
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 1, v___x_4006_);
lean_ctor_set(v___x_4004_, 0, v_snd_4002_);
v___x_4008_ = v___x_4004_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_snd_4002_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v___x_4006_);
v___x_4008_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
size_t v___x_4009_; size_t v___x_4010_; 
v___x_4009_ = ((size_t)1ULL);
v___x_4010_ = lean_usize_add(v_i_3990_, v___x_4009_);
v_i_3990_ = v___x_4010_;
v_b_3991_ = v___x_4008_;
goto _start;
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec(v_snd_3997_);
lean_dec(v___x_3987_);
v_a_4014_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3999_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3999_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1___boxed(lean_object* v___x_4022_, lean_object* v_as_4023_, lean_object* v_sz_4024_, lean_object* v_i_4025_, lean_object* v_b_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
size_t v_sz_boxed_4029_; size_t v_i_boxed_4030_; lean_object* v_res_4031_; 
v_sz_boxed_4029_ = lean_unbox_usize(v_sz_4024_);
lean_dec(v_sz_4024_);
v_i_boxed_4030_ = lean_unbox_usize(v_i_4025_);
lean_dec(v_i_4025_);
v_res_4031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___x_4022_, v_as_4023_, v_sz_boxed_4029_, v_i_boxed_4030_, v_b_4026_, v___y_4027_);
lean_dec_ref(v___y_4027_);
lean_dec_ref(v_as_4023_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___boxed(lean_object* v_requestNo_4032_, lean_object* v_item_4033_, lean_object* v_visited_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_requestNo_4032_, v_item_4033_, v_visited_4034_, v_a_4035_);
lean_dec_ref(v_a_4035_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(lean_object* v_requestNo_4038_, lean_object* v_uri_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
lean_inc(v_requestNo_4038_);
v___x_4042_ = l_Lean_JsonNumber_fromNat(v_requestNo_4038_);
v___x_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
v___x_4044_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_4043_);
v___x_4045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4043_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
lean_ctor_set(v___x_4045_, 2, v_uri_4039_);
v___x_4046_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_4045_, v_a_4040_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v___x_4047_; 
lean_dec_ref_known(v___x_4046_, 1);
v___x_4047_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_4043_, v_a_4040_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4106_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4050_ = v___x_4047_;
v_isShared_4051_ = v_isSharedCheck_4106_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4047_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4106_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v_result_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4104_; 
v_result_4052_ = lean_ctor_get(v_a_4048_, 1);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_a_4048_);
if (v_isSharedCheck_4104_ == 0)
{
lean_object* v_unused_4105_; 
v_unused_4105_ = lean_ctor_get(v_a_4048_, 0);
lean_dec(v_unused_4105_);
v___x_4054_ = v_a_4048_;
v_isShared_4055_ = v_isSharedCheck_4104_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_result_4052_);
lean_dec(v_a_4048_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4104_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4056_ = lean_unsigned_to_nat(1u);
v___x_4057_ = lean_nat_add(v_requestNo_4038_, v___x_4056_);
lean_dec(v_requestNo_4038_);
if (lean_obj_tag(v_result_4052_) == 1)
{
lean_object* v_val_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4096_; 
lean_del_object(v___x_4050_);
v_val_4058_ = lean_ctor_get(v_result_4052_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_result_4052_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4060_ = v_result_4052_;
v_isShared_4061_ = v_isSharedCheck_4096_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_val_4058_);
lean_dec(v_result_4052_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4096_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4062_; lean_object* v___x_4064_; 
v___x_4062_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 1, v___x_4062_);
lean_ctor_set(v___x_4054_, 0, v_val_4058_);
v___x_4064_ = v___x_4054_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_val_4058_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v___x_4062_);
v___x_4064_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = lean_box(1);
v___x_4066_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v___x_4057_, v___x_4064_, v___x_4065_, v_a_4040_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4086_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4069_ = v___x_4066_;
v_isShared_4070_ = v_isSharedCheck_4086_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4066_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4086_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v_fst_4071_; lean_object* v_snd_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4085_; 
v_fst_4071_ = lean_ctor_get(v_a_4067_, 0);
v_snd_4072_ = lean_ctor_get(v_a_4067_, 1);
v_isSharedCheck_4085_ = !lean_is_exclusive(v_a_4067_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4074_ = v_a_4067_;
v_isShared_4075_ = v_isSharedCheck_4085_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_snd_4072_);
lean_inc(v_fst_4071_);
lean_dec(v_a_4067_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4085_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4061_ == 0)
{
lean_ctor_set(v___x_4060_, 0, v_fst_4071_);
v___x_4077_ = v___x_4060_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_fst_4071_);
v___x_4077_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
lean_object* v___x_4079_; 
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4077_);
v___x_4079_ = v___x_4074_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v_snd_4072_);
v___x_4079_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
lean_object* v___x_4081_; 
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 0, v___x_4079_);
v___x_4081_ = v___x_4069_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4079_);
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
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_del_object(v___x_4060_);
v_a_4087_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4066_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4066_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
}
}
else
{
lean_object* v___x_4097_; lean_object* v___x_4099_; 
lean_dec(v_result_4052_);
v___x_4097_ = lean_box(0);
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 1, v___x_4057_);
lean_ctor_set(v___x_4054_, 0, v___x_4097_);
v___x_4099_ = v___x_4054_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4097_);
lean_ctor_set(v_reuseFailAlloc_4103_, 1, v___x_4057_);
v___x_4099_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
lean_object* v___x_4101_; 
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v___x_4099_);
v___x_4101_ = v___x_4050_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4099_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec(v_requestNo_4038_);
v_a_4107_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4047_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4047_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
lean_dec_ref_known(v___x_4043_, 1);
lean_dec(v_requestNo_4038_);
v_a_4115_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4046_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4046_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy___boxed(lean_object* v_requestNo_4123_, lean_object* v_uri_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(v_requestNo_4123_, v_uri_4124_, v_a_4125_);
lean_dec_ref(v_a_4125_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object* v_lean_4130_, lean_object* v_args_4131_, lean_object* v_test_4132_){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; uint8_t v___x_4137_; uint8_t v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4134_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_4135_ = lean_box(0);
v___x_4136_ = ((lean_object*)(l_Lean_Lsp_Ipc_runWith___redArg___closed__0));
v___x_4137_ = 1;
v___x_4138_ = 0;
v___x_4139_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4139_, 0, v___x_4134_);
lean_ctor_set(v___x_4139_, 1, v_lean_4130_);
lean_ctor_set(v___x_4139_, 2, v_args_4131_);
lean_ctor_set(v___x_4139_, 3, v___x_4135_);
lean_ctor_set(v___x_4139_, 4, v___x_4136_);
lean_ctor_set_uint8(v___x_4139_, sizeof(void*)*5, v___x_4137_);
lean_ctor_set_uint8(v___x_4139_, sizeof(void*)*5 + 1, v___x_4138_);
v___x_4140_ = lean_io_process_spawn(v___x_4139_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4142_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v___x_4142_ = lean_apply_2(v_test_4132_, v_a_4141_, lean_box(0));
return v___x_4142_;
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_dec_ref(v_test_4132_);
v_a_4143_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4140_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4140_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg___boxed(lean_object* v_lean_4151_, lean_object* v_args_4152_, lean_object* v_test_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4151_, v_args_4152_, v_test_4153_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object* v_00_u03b1_4156_, lean_object* v_lean_4157_, lean_object* v_args_4158_, lean_object* v_test_4159_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4157_, v_args_4158_, v_test_4159_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___boxed(lean_object* v_00_u03b1_4162_, lean_object* v_lean_4163_, lean_object* v_args_4164_, lean_object* v_test_4165_, lean_object* v_a_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l_Lean_Lsp_Ipc_runWith(v_00_u03b1_4162_, v_lean_4163_, v_args_4164_, v_test_4165_);
return v_res_4167_;
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
