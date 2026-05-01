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
lean_object* v___x_74_; lean_object* v___f_75_; lean_object* v___x_2956__overap_76_; lean_object* v___x_77_; 
v___x_74_ = lean_obj_once(&l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0, &l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0_once, _init_l_panic___at___00Lean_Lsp_Ipc_shutdown_spec__2___closed__0);
v___f_75_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_75_, 0, v___x_74_);
v___x_2956__overap_76_ = lean_panic_fn_borrowed(v___f_75_, v_msg_71_);
lean_dec_ref(v___f_75_);
lean_inc_ref(v___y_72_);
v___x_77_ = lean_apply_2(v___x_2956__overap_76_, v___y_72_, lean_box(0));
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
lean_inc_ref(v___y_516_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v___y_516_);
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
lean_dec(v___x_527_);
lean_inc_ref(v___y_515_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___y_515_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___x_522_);
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v___y_514_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_512_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_Json_mkObj(v___x_532_);
lean_dec_ref(v___x_532_);
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
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_548_;
goto v___jp_513_;
}
case 1:
{
lean_object* v___x_549_; 
v___x_549_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_549_;
goto v___jp_513_;
}
case 2:
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_550_;
goto v___jp_513_;
}
case 3:
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_551_;
goto v___jp_513_;
}
case 4:
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_552_;
goto v___jp_513_;
}
case 5:
{
lean_object* v___x_553_; 
v___x_553_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_553_;
goto v___jp_513_;
}
case 6:
{
lean_object* v___x_554_; 
v___x_554_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_554_;
goto v___jp_513_;
}
case 7:
{
lean_object* v___x_555_; 
v___x_555_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_555_;
goto v___jp_513_;
}
case 8:
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_556_;
goto v___jp_513_;
}
case 9:
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_557_;
goto v___jp_513_;
}
case 10:
{
lean_object* v___x_558_; 
v___x_558_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
v___y_517_ = v___x_558_;
goto v___jp_513_;
}
default: 
{
lean_object* v___x_559_; 
v___x_559_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_514_ = v___x_545_;
v___y_515_ = v___x_546_;
v___y_516_ = v___x_547_;
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
lean_dec_ref(v_prev_x3f_657_);
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
lean_dec_ref(v_isIncremental_x3f_661_);
v___x_670_ = lean_unbox(v_val_669_);
lean_dec(v_val_669_);
if (v___x_670_ == 0)
{
lean_dec_ref(v_prev_x3f_657_);
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
lean_dec_ref(v_prev_x3f_657_);
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
lean_dec_ref(v_a_694_);
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
lean_dec_ref(v_a_694_);
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
lean_dec_ref(v___x_746_);
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
lean_dec_ref(v___x_746_);
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
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(lean_object* v_v_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = l_Lean_Lsp_instToJsonWaitForDiagnosticsParams_toJson(v_v_777_);
v___x_779_ = l_Lean_Json_Structured_fromJson_x3f(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object* v_h_780_, lean_object* v_r_781_){
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
v___x_795_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__1(v_param_785_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; 
lean_dec_ref(v___x_795_);
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
v___x_793_ = l_IO_FS_Stream_writeLspMessage(v_h_780_, v___x_792_);
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0___boxed(lean_object* v_h_806_, lean_object* v_r_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_h_806_, v_r_807_);
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
v___x_815_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(v_a_814_, v_r_810_);
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
lean_dec_ref(v___x_829_);
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
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(lean_object* v_v_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = l_Lean_Lsp_instToJsonWaitForILeansParams_toJson(v_v_846_);
v___x_848_ = l_Lean_Json_Structured_fromJson_x3f(v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object* v_h_849_, lean_object* v_r_850_){
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
v___x_864_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__1(v_param_854_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v___x_865_; 
lean_dec_ref(v___x_864_);
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
v___x_862_ = l_IO_FS_Stream_writeLspMessage(v_h_849_, v___x_861_);
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0___boxed(lean_object* v_h_875_, lean_object* v_r_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_h_875_, v_r_876_);
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
v___x_884_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(v_a_883_, v_r_879_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(lean_object* v_waitForILeansId_895_, lean_object* v___y_896_){
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
lean_dec_ref(v_a_899_);
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
v___x_906_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__1));
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
lean_dec_ref(v_a_899_);
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
v___x_914_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___closed__2));
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg___boxed(lean_object* v_waitForILeansId_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_930_, v___y_931_);
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
lean_object* v___x_946_; 
lean_dec_ref(v___x_945_);
v___x_946_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_935_, v_a_938_);
lean_dec(v_waitForILeansId_935_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_960_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_960_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_960_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_960_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v_fst_951_; 
v_fst_951_ = lean_ctor_get(v_a_947_, 0);
lean_inc(v_fst_951_);
lean_dec(v_a_947_);
if (lean_obj_tag(v_fst_951_) == 0)
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_box(0);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_952_);
v___x_954_ = v___x_949_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
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
v_val_956_ = lean_ctor_get(v_fst_951_, 0);
lean_inc(v_val_956_);
lean_dec_ref(v_fst_951_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v_val_956_);
v___x_958_ = v___x_949_;
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
v_a_961_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_946_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_946_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(lean_object* v_waitForILeansId_975_, lean_object* v_b_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_975_, v___y_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___boxed(lean_object* v_waitForILeansId_980_, lean_object* v_b_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1(v_waitForILeansId_980_, v_b_981_, v___y_982_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v_b_981_);
lean_dec(v_waitForILeansId_980_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans(lean_object* v_waitForILeansId_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_990_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForILeans___closed__0));
v___x_991_ = ((lean_object*)(l_Lean_Lsp_Ipc_waitForWatchdogILeans___closed__0));
lean_inc(v_waitForILeansId_987_);
v___x_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_992_, 0, v_waitForILeansId_987_);
lean_ctor_set(v___x_992_, 1, v___x_990_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
v___x_993_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_waitForILeans_spec__0(v___x_992_, v_a_988_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_994_; 
lean_dec_ref(v___x_993_);
v___x_994_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_waitForILeans_spec__1___redArg(v_waitForILeansId_987_, v_a_988_);
lean_dec(v_waitForILeansId_987_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1008_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1008_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1008_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_fst_999_; 
v_fst_999_ = lean_ctor_get(v_a_995_, 0);
lean_inc(v_fst_999_);
lean_dec(v_a_995_);
if (lean_obj_tag(v_fst_999_) == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_box(0);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1000_);
v___x_1002_ = v___x_997_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1006_; 
v_val_1004_ = lean_ctor_get(v_fst_999_, 0);
lean_inc(v_val_1004_);
lean_dec_ref(v_fst_999_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_val_1004_);
v___x_1006_ = v___x_997_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_val_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_a_1009_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_994_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_994_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_dec(v_waitForILeansId_987_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForWatchdogILeans___boxed(lean_object* v_waitForILeansId_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Lsp_Ipc_waitForWatchdogILeans(v_waitForILeansId_1017_, v_a_1018_);
lean_dec_ref(v_a_1018_);
return v_res_1020_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(lean_object* v_msg_1021_, lean_object* v_as_1022_, size_t v_i_1023_, size_t v_stop_1024_){
_start:
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_usize_dec_eq(v_i_1023_, v_stop_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v_message_1027_; uint8_t v___x_1028_; 
v___x_1026_ = lean_array_uget_borrowed(v_as_1022_, v_i_1023_);
v_message_1027_ = lean_ctor_get(v___x_1026_, 6);
v___x_1028_ = lean_string_dec_eq(v_message_1027_, v_msg_1021_);
if (v___x_1028_ == 0)
{
size_t v___x_1029_; size_t v___x_1030_; 
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_add(v_i_1023_, v___x_1029_);
v_i_1023_ = v___x_1030_;
goto _start;
}
else
{
return v___x_1028_;
}
}
else
{
uint8_t v___x_1032_; 
v___x_1032_ = 0;
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0___boxed(lean_object* v_msg_1033_, lean_object* v_as_1034_, lean_object* v_i_1035_, lean_object* v_stop_1036_){
_start:
{
size_t v_i_boxed_1037_; size_t v_stop_boxed_1038_; uint8_t v_res_1039_; lean_object* v_r_1040_; 
v_i_boxed_1037_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_stop_boxed_1038_ = lean_unbox_usize(v_stop_1036_);
lean_dec(v_stop_1036_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(v_msg_1033_, v_as_1034_, v_i_boxed_1037_, v_stop_boxed_1038_);
lean_dec_ref(v_as_1034_);
lean_dec_ref(v_msg_1033_);
v_r_1040_ = lean_box(v_res_1039_);
return v_r_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(lean_object* v_msg_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Lsp_Ipc_readMessage(v_a_1042_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1081_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1081_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1081_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
if (lean_obj_tag(v_a_1045_) == 1)
{
lean_object* v_method_1049_; lean_object* v_params_x3f_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_method_1049_ = lean_ctor_get(v_a_1045_, 0);
lean_inc_ref(v_method_1049_);
v_params_x3f_1050_ = lean_ctor_get(v_a_1045_, 1);
lean_inc(v_params_x3f_1050_);
lean_dec_ref(v_a_1045_);
v___x_1051_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0));
v___x_1052_ = lean_string_dec_eq(v_method_1049_, v___x_1051_);
lean_dec_ref(v_method_1049_);
if (v___x_1052_ == 0)
{
lean_dec(v_params_x3f_1050_);
lean_del_object(v___x_1047_);
goto _start;
}
else
{
if (lean_obj_tag(v_params_x3f_1050_) == 1)
{
lean_object* v_val_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_val_1054_ = lean_ctor_get(v_params_x3f_1050_, 0);
lean_inc(v_val_1054_);
lean_dec_ref(v_params_x3f_1050_);
v___x_1055_ = l_Lean_Json_Structured_toJson(v_val_1054_);
v___x_1056_ = l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(v___x_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2));
v___x_1059_ = lean_string_append(v___x_1058_, v_a_1057_);
lean_dec(v_a_1057_);
v___x_1060_ = lean_mk_io_user_error(v___x_1059_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 1);
lean_ctor_set(v___x_1047_, 0, v___x_1060_);
v___x_1062_ = v___x_1047_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_object* v_a_1064_; lean_object* v_diagnostics_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_a_1064_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1064_);
lean_dec_ref(v___x_1056_);
v_diagnostics_1065_ = lean_ctor_get(v_a_1064_, 3);
lean_inc_ref(v_diagnostics_1065_);
lean_dec(v_a_1064_);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_array_get_size(v_diagnostics_1065_);
v___x_1068_ = lean_nat_dec_lt(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_dec_ref(v_diagnostics_1065_);
lean_del_object(v___x_1047_);
goto _start;
}
else
{
if (v___x_1068_ == 0)
{
lean_dec_ref(v_diagnostics_1065_);
lean_del_object(v___x_1047_);
goto _start;
}
else
{
size_t v___x_1071_; size_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = lean_usize_of_nat(v___x_1067_);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(v_msg_1041_, v_diagnostics_1065_, v___x_1071_, v___x_1072_);
lean_dec_ref(v_diagnostics_1065_);
if (v___x_1073_ == 0)
{
lean_del_object(v___x_1047_);
goto _start;
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = lean_box(0);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1075_);
v___x_1077_ = v___x_1047_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
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
}
}
else
{
lean_dec(v_params_x3f_1050_);
lean_del_object(v___x_1047_);
goto _start;
}
}
}
else
{
lean_del_object(v___x_1047_);
lean_dec(v_a_1045_);
goto _start;
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1082_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1044_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1044_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop___boxed(lean_object* v_msg_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(v_msg_1090_, v_a_1091_);
lean_dec_ref(v_a_1091_);
lean_dec_ref(v_msg_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage(lean_object* v_msg_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(v_msg_1094_, v_a_1095_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage___boxed(lean_object* v_msg_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Lsp_Ipc_waitForMessage(v_msg_1098_, v_a_1099_);
lean_dec_ref(v_a_1099_);
lean_dec_ref(v_msg_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(lean_object* v_j_1102_, lean_object* v_k_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = l_Lean_Json_getObjValD(v_j_1102_, v_k_1103_);
v___x_1105_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0___boxed(lean_object* v_j_1106_, lean_object* v_k_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_j_1106_, v_k_1107_);
lean_dec_ref(v_k_1107_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_1109_, size_t v_i_1110_, lean_object* v_bs_1111_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_usize_dec_lt(v_i_1110_, v_sz_1109_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_bs_1111_);
return v___x_1113_;
}
else
{
lean_object* v_v_1114_; lean_object* v___x_1115_; 
v_v_1114_ = lean_array_uget_borrowed(v_bs_1111_, v_i_1110_);
lean_inc(v_v_1114_);
v___x_1115_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_v_1114_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_bs_1111_);
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
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
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1124_; lean_object* v___x_1125_; lean_object* v_bs_x27_1126_; size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
v_a_1124_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1124_);
lean_dec_ref(v___x_1115_);
v___x_1125_ = lean_unsigned_to_nat(0u);
v_bs_x27_1126_ = lean_array_uset(v_bs_1111_, v_i_1110_, v___x_1125_);
v___x_1127_ = ((size_t)1ULL);
v___x_1128_ = lean_usize_add(v_i_1110_, v___x_1127_);
v___x_1129_ = lean_array_uset(v_bs_x27_1126_, v_i_1110_, v_a_1124_);
v_i_1110_ = v___x_1128_;
v_bs_1111_ = v___x_1129_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_1131_, lean_object* v_i_1132_, lean_object* v_bs_1133_){
_start:
{
size_t v_sz_boxed_1134_; size_t v_i_boxed_1135_; lean_object* v_res_1136_; 
v_sz_boxed_1134_ = lean_unbox_usize(v_sz_1131_);
lean_dec(v_sz_1131_);
v_i_boxed_1135_ = lean_unbox_usize(v_i_1132_);
lean_dec(v_i_1132_);
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_1134_, v_i_boxed_1135_, v_bs_1133_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_1138_){
_start:
{
if (lean_obj_tag(v_x_1138_) == 4)
{
lean_object* v_elems_1139_; size_t v_sz_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
v_elems_1139_ = lean_ctor_get(v_x_1138_, 0);
lean_inc_ref(v_elems_1139_);
lean_dec_ref(v_x_1138_);
v_sz_1140_ = lean_array_size(v_elems_1139_);
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_1140_, v___x_1141_, v_elems_1139_);
return v___x_1142_;
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1143_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1144_ = lean_unsigned_to_nat(80u);
v___x_1145_ = l_Lean_Json_pretty(v_x_1138_, v___x_1144_);
v___x_1146_ = lean_string_append(v___x_1143_, v___x_1145_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1148_ = lean_string_append(v___x_1146_, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(lean_object* v_j_1150_, lean_object* v_k_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = l_Lean_Json_getObjValD(v_j_1150_, v_k_1151_);
v___x_1153_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1(v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1___boxed(lean_object* v_j_1154_, lean_object* v_k_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_j_1154_, v_k_1155_);
lean_dec_ref(v_k_1155_);
return v_res_1156_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10(void){
_start:
{
uint8_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = 1;
v___x_1162_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__9));
v___x_1163_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1162_, v___x_1161_);
return v___x_1163_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = 1;
v___x_1175_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__5));
v___x_1176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1175_, v___x_1174_);
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_1178_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__6);
v___x_1179_ = lean_string_append(v___x_1178_, v___x_1177_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_1181_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1182_ = lean_string_append(v___x_1181_, v___x_1180_);
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1184_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__11);
v___x_1185_ = lean_string_append(v___x_1184_, v___x_1183_);
return v___x_1185_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = 1;
v___x_1190_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__15));
v___x_1191_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1190_, v___x_1189_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__16);
v___x_1193_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1194_ = lean_string_append(v___x_1193_, v___x_1192_);
return v___x_1194_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1196_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__17);
v___x_1197_ = lean_string_append(v___x_1196_, v___x_1195_);
return v___x_1197_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = 1;
v___x_1202_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__20));
v___x_1203_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1202_, v___x_1201_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_1205_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__8);
v___x_1206_ = lean_string_append(v___x_1205_, v___x_1204_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_1208_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__22);
v___x_1209_ = lean_string_append(v___x_1208_, v___x_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(lean_object* v_json_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_1210_);
v___x_1212_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__0(v_json_1210_, v___x_1211_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_json_1210_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1222_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1222_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1217_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__13);
v___x_1218_ = lean_string_append(v___x_1217_, v_a_1213_);
lean_dec(v_a_1213_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1218_);
v___x_1220_ = v___x_1215_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
else
{
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_json_1210_);
v_a_1223_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1212_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1212_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 0);
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_a_1231_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1231_);
lean_dec_ref(v___x_1212_);
v___x_1232_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
lean_inc(v_json_1210_);
v___x_1233_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1(v_json_1210_, v___x_1232_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1243_; 
lean_dec(v_a_1231_);
lean_dec(v_json_1210_);
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1243_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1243_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1238_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__18);
v___x_1239_ = lean_string_append(v___x_1238_, v_a_1234_);
lean_dec(v_a_1234_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1239_);
v___x_1241_ = v___x_1236_;
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
else
{
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec(v_a_1231_);
lean_dec(v_json_1210_);
v_a_1244_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1233_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1233_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set_tag(v___x_1246_, 0);
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_a_1252_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1233_);
v___x_1253_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1254_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_json_1210_, v___x_1253_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_a_1252_);
lean_dec(v_a_1231_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1259_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__23);
v___x_1260_ = lean_string_append(v___x_1259_, v_a_1255_);
lean_dec(v_a_1255_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1260_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_a_1252_);
lean_dec(v_a_1231_);
v_a_1265_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1254_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1254_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 0);
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1281_; 
v_a_1273_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1275_ = v___x_1254_;
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1254_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1277_, 0, v_a_1231_);
lean_ctor_set(v___x_1277_, 1, v_a_1252_);
lean_ctor_set(v___x_1277_, 2, v_a_1273_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1277_);
v___x_1279_ = v___x_1275_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(size_t v_sz_1282_, size_t v_i_1283_, lean_object* v_bs_1284_){
_start:
{
uint8_t v___x_1285_; 
v___x_1285_ = lean_usize_dec_lt(v_i_1283_, v_sz_1282_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1286_, 0, v_bs_1284_);
return v___x_1286_;
}
else
{
lean_object* v_v_1287_; lean_object* v___x_1288_; 
v_v_1287_ = lean_array_uget_borrowed(v_bs_1284_, v_i_1283_);
lean_inc(v_v_1287_);
v___x_1288_ = l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson(v_v_1287_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v_bs_1284_);
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
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
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1297_; lean_object* v___x_1298_; lean_object* v_bs_x27_1299_; size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v_a_1297_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1297_);
lean_dec_ref(v___x_1288_);
v___x_1298_ = lean_unsigned_to_nat(0u);
v_bs_x27_1299_ = lean_array_uset(v_bs_1284_, v_i_1283_, v___x_1298_);
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_add(v_i_1283_, v___x_1300_);
v___x_1302_ = lean_array_uset(v_bs_x27_1299_, v_i_1283_, v_a_1297_);
v_i_1283_ = v___x_1301_;
v_bs_1284_ = v___x_1302_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(lean_object* v_x_1304_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 4)
{
lean_object* v_elems_1305_; size_t v_sz_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v_elems_1305_ = lean_ctor_get(v_x_1304_, 0);
lean_inc_ref(v_elems_1305_);
lean_dec_ref(v_x_1304_);
v_sz_1306_ = lean_array_size(v_elems_1305_);
v___x_1307_ = ((size_t)0ULL);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_1306_, v___x_1307_, v_elems_1305_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1309_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1310_ = lean_unsigned_to_nat(80u);
v___x_1311_ = l_Lean_Json_pretty(v_x_1304_, v___x_1310_);
v___x_1312_ = lean_string_append(v___x_1309_, v___x_1311_);
lean_dec_ref(v___x_1311_);
v___x_1313_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1314_ = lean_string_append(v___x_1312_, v___x_1313_);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(lean_object* v_j_1316_, lean_object* v_k_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = l_Lean_Json_getObjValD(v_j_1316_, v_k_1317_);
v___x_1319_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3(v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2___boxed(lean_object* v_j_1320_, lean_object* v_k_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2(v_j_1320_, v_k_1321_);
lean_dec_ref(v_k_1321_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5___boxed(lean_object* v_sz_1323_, lean_object* v_i_1324_, lean_object* v_bs_1325_){
_start:
{
size_t v_sz_boxed_1326_; size_t v_i_boxed_1327_; lean_object* v_res_1328_; 
v_sz_boxed_1326_ = lean_unbox_usize(v_sz_1323_);
lean_dec(v_sz_1323_);
v_i_boxed_1327_ = lean_unbox_usize(v_i_1324_);
lean_dec(v_i_1324_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__2_spec__3_spec__5(v_sz_boxed_1326_, v_i_boxed_1327_, v_bs_1325_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
if (lean_obj_tag(v_a_1331_) == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_array_to_list(v_a_1332_);
return v___x_1333_;
}
else
{
lean_object* v_head_1334_; lean_object* v_tail_1335_; lean_object* v___x_1336_; 
v_head_1334_ = lean_ctor_get(v_a_1331_, 0);
lean_inc(v_head_1334_);
v_tail_1335_ = lean_ctor_get(v_a_1331_, 1);
lean_inc(v_tail_1335_);
lean_dec_ref(v_a_1331_);
v___x_1336_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1332_, v_head_1334_);
v_a_1331_ = v_tail_1335_;
v_a_1332_ = v___x_1336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(size_t v_sz_1338_, size_t v_i_1339_, lean_object* v_bs_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_usize_dec_lt(v_i_1339_, v_sz_1338_);
if (v___x_1341_ == 0)
{
return v_bs_1340_;
}
else
{
lean_object* v_v_1342_; lean_object* v___x_1343_; lean_object* v_bs_x27_1344_; lean_object* v___x_1345_; size_t v___x_1346_; size_t v___x_1347_; lean_object* v___x_1348_; 
v_v_1342_ = lean_array_uget(v_bs_1340_, v_i_1339_);
v___x_1343_ = lean_unsigned_to_nat(0u);
v_bs_x27_1344_ = lean_array_uset(v_bs_1340_, v_i_1339_, v___x_1343_);
v___x_1345_ = l_Lean_Lsp_instToJsonRange_toJson(v_v_1342_);
v___x_1346_ = ((size_t)1ULL);
v___x_1347_ = lean_usize_add(v_i_1339_, v___x_1346_);
v___x_1348_ = lean_array_uset(v_bs_x27_1344_, v_i_1339_, v___x_1345_);
v_i_1339_ = v___x_1347_;
v_bs_1340_ = v___x_1348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_1350_, lean_object* v_i_1351_, lean_object* v_bs_1352_){
_start:
{
size_t v_sz_boxed_1353_; size_t v_i_boxed_1354_; lean_object* v_res_1355_; 
v_sz_boxed_1353_ = lean_unbox_usize(v_sz_1350_);
lean_dec(v_sz_1350_);
v_i_boxed_1354_ = lean_unbox_usize(v_i_1351_);
lean_dec(v_i_1351_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_boxed_1353_, v_i_boxed_1354_, v_bs_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(lean_object* v_a_1356_){
_start:
{
size_t v_sz_1357_; size_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_sz_1357_ = lean_array_size(v_a_1356_);
v___x_1358_ = ((size_t)0ULL);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0_spec__0(v_sz_1357_, v___x_1358_, v_a_1356_);
v___x_1360_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(lean_object* v_x_1363_){
_start:
{
lean_object* v_item_1364_; lean_object* v_fromRanges_1365_; lean_object* v_children_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_item_1364_ = lean_ctor_get(v_x_1363_, 0);
lean_inc_ref(v_item_1364_);
v_fromRanges_1365_ = lean_ctor_get(v_x_1363_, 1);
lean_inc_ref(v_fromRanges_1365_);
v_children_1366_ = lean_ctor_get(v_x_1363_, 2);
lean_inc_ref(v_children_1366_);
lean_dec_ref(v_x_1363_);
v___x_1367_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_1368_ = l_Lean_Lsp_instToJsonCallHierarchyItem_toJson(v_item_1364_);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1367_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = lean_box(0);
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__14));
v___x_1373_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__0(v_fromRanges_1365_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___x_1370_);
v___x_1376_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_1377_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(v_children_1366_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v___x_1370_);
v___x_1380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v___x_1370_);
v___x_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1375_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1371_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_1384_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_1382_, v___x_1383_);
v___x_1385_ = l_Lean_Json_mkObj(v___x_1384_);
lean_dec(v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(size_t v_sz_1386_, size_t v_i_1387_, lean_object* v_bs_1388_){
_start:
{
uint8_t v___x_1389_; 
v___x_1389_ = lean_usize_dec_lt(v_i_1387_, v_sz_1386_);
if (v___x_1389_ == 0)
{
return v_bs_1388_;
}
else
{
lean_object* v_v_1390_; lean_object* v___x_1391_; lean_object* v_bs_x27_1392_; lean_object* v___x_1393_; size_t v___x_1394_; size_t v___x_1395_; lean_object* v___x_1396_; 
v_v_1390_ = lean_array_uget(v_bs_1388_, v_i_1387_);
v___x_1391_ = lean_unsigned_to_nat(0u);
v_bs_x27_1392_ = lean_array_uset(v_bs_1388_, v_i_1387_, v___x_1391_);
v___x_1393_ = l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson(v_v_1390_);
v___x_1394_ = ((size_t)1ULL);
v___x_1395_ = lean_usize_add(v_i_1387_, v___x_1394_);
v___x_1396_ = lean_array_uset(v_bs_x27_1392_, v_i_1387_, v___x_1393_);
v_i_1387_ = v___x_1395_;
v_bs_1388_ = v___x_1396_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1(lean_object* v_a_1398_){
_start:
{
size_t v_sz_1399_; size_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v_sz_1399_ = lean_array_size(v_a_1398_);
v___x_1400_ = ((size_t)0ULL);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_1399_, v___x_1400_, v_a_1398_);
v___x_1402_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2___boxed(lean_object* v_sz_1403_, lean_object* v_i_1404_, lean_object* v_bs_1405_){
_start:
{
size_t v_sz_boxed_1406_; size_t v_i_boxed_1407_; lean_object* v_res_1408_; 
v_sz_boxed_1406_ = lean_unbox_usize(v_sz_1403_);
lean_dec(v_sz_1403_);
v_i_boxed_1407_ = lean_unbox_usize(v_i_1404_);
lean_dec(v_i_1404_);
v_res_1408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__1_spec__2(v_sz_boxed_1406_, v_i_boxed_1407_, v_bs_1405_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(lean_object* v_k_1411_, lean_object* v_v_1412_, lean_object* v_t_1413_){
_start:
{
if (lean_obj_tag(v_t_1413_) == 0)
{
lean_object* v_size_1414_; lean_object* v_k_1415_; lean_object* v_v_1416_; lean_object* v_l_1417_; lean_object* v_r_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1699_; 
v_size_1414_ = lean_ctor_get(v_t_1413_, 0);
v_k_1415_ = lean_ctor_get(v_t_1413_, 1);
v_v_1416_ = lean_ctor_get(v_t_1413_, 2);
v_l_1417_ = lean_ctor_get(v_t_1413_, 3);
v_r_1418_ = lean_ctor_get(v_t_1413_, 4);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_t_1413_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1420_ = v_t_1413_;
v_isShared_1421_ = v_isSharedCheck_1699_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_r_1418_);
lean_inc(v_l_1417_);
lean_inc(v_v_1416_);
lean_inc(v_k_1415_);
lean_inc(v_size_1414_);
lean_dec(v_t_1413_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1699_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_string_dec_lt(v_k_1411_, v_k_1415_);
if (v___x_1422_ == 0)
{
uint8_t v___x_1423_; 
v___x_1423_ = lean_string_dec_eq(v_k_1411_, v_k_1415_);
if (v___x_1423_ == 0)
{
lean_object* v_impl_1424_; lean_object* v___x_1425_; 
lean_dec(v_size_1414_);
v_impl_1424_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1411_, v_v_1412_, v_r_1418_);
v___x_1425_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1417_) == 0)
{
lean_object* v_size_1426_; lean_object* v_size_1427_; lean_object* v_k_1428_; lean_object* v_v_1429_; lean_object* v_l_1430_; lean_object* v_r_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_size_1426_ = lean_ctor_get(v_l_1417_, 0);
v_size_1427_ = lean_ctor_get(v_impl_1424_, 0);
lean_inc(v_size_1427_);
v_k_1428_ = lean_ctor_get(v_impl_1424_, 1);
lean_inc(v_k_1428_);
v_v_1429_ = lean_ctor_get(v_impl_1424_, 2);
lean_inc(v_v_1429_);
v_l_1430_ = lean_ctor_get(v_impl_1424_, 3);
lean_inc(v_l_1430_);
v_r_1431_ = lean_ctor_get(v_impl_1424_, 4);
lean_inc(v_r_1431_);
v___x_1432_ = lean_unsigned_to_nat(3u);
v___x_1433_ = lean_nat_mul(v___x_1432_, v_size_1426_);
v___x_1434_ = lean_nat_dec_lt(v___x_1433_, v_size_1427_);
lean_dec(v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_dec(v_r_1431_);
lean_dec(v_l_1430_);
lean_dec(v_v_1429_);
lean_dec(v_k_1428_);
v___x_1435_ = lean_nat_add(v___x_1425_, v_size_1426_);
v___x_1436_ = lean_nat_add(v___x_1435_, v_size_1427_);
lean_dec(v_size_1427_);
lean_dec(v___x_1435_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_impl_1424_);
lean_ctor_set(v___x_1420_, 0, v___x_1436_);
v___x_1438_ = v___x_1420_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v_l_1417_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v_impl_1424_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
else
{
lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1503_; 
v_isSharedCheck_1503_ = !lean_is_exclusive(v_impl_1424_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; lean_object* v_unused_1508_; 
v_unused_1504_ = lean_ctor_get(v_impl_1424_, 4);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_impl_1424_, 3);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_impl_1424_, 2);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_impl_1424_, 1);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_impl_1424_, 0);
lean_dec(v_unused_1508_);
v___x_1441_ = v_impl_1424_;
v_isShared_1442_ = v_isSharedCheck_1503_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v_impl_1424_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1503_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v_size_1443_; lean_object* v_k_1444_; lean_object* v_v_1445_; lean_object* v_l_1446_; lean_object* v_r_1447_; lean_object* v_size_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_size_1443_ = lean_ctor_get(v_l_1430_, 0);
v_k_1444_ = lean_ctor_get(v_l_1430_, 1);
v_v_1445_ = lean_ctor_get(v_l_1430_, 2);
v_l_1446_ = lean_ctor_get(v_l_1430_, 3);
v_r_1447_ = lean_ctor_get(v_l_1430_, 4);
v_size_1448_ = lean_ctor_get(v_r_1431_, 0);
v___x_1449_ = lean_unsigned_to_nat(2u);
v___x_1450_ = lean_nat_mul(v___x_1449_, v_size_1448_);
v___x_1451_ = lean_nat_dec_lt(v_size_1443_, v___x_1450_);
lean_dec(v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1479_; 
lean_inc(v_r_1447_);
lean_inc(v_l_1446_);
lean_inc(v_v_1445_);
lean_inc(v_k_1444_);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_l_1430_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; lean_object* v_unused_1481_; lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; 
v_unused_1480_ = lean_ctor_get(v_l_1430_, 4);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_l_1430_, 3);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v_l_1430_, 2);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_l_1430_, 1);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_l_1430_, 0);
lean_dec(v_unused_1484_);
v___x_1453_ = v_l_1430_;
v_isShared_1454_ = v_isSharedCheck_1479_;
goto v_resetjp_1452_;
}
else
{
lean_dec(v_l_1430_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1479_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1469_; 
v___x_1455_ = lean_nat_add(v___x_1425_, v_size_1426_);
v___x_1456_ = lean_nat_add(v___x_1455_, v_size_1427_);
lean_dec(v_size_1427_);
if (lean_obj_tag(v_l_1446_) == 0)
{
lean_object* v_size_1477_; 
v_size_1477_ = lean_ctor_get(v_l_1446_, 0);
lean_inc(v_size_1477_);
v___y_1469_ = v_size_1477_;
goto v___jp_1468_;
}
else
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_unsigned_to_nat(0u);
v___y_1469_ = v___x_1478_;
goto v___jp_1468_;
}
v___jp_1457_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = lean_nat_add(v___y_1458_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec(v___y_1458_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 4, v_r_1431_);
lean_ctor_set(v___x_1453_, 3, v_r_1447_);
lean_ctor_set(v___x_1453_, 2, v_v_1429_);
lean_ctor_set(v___x_1453_, 1, v_k_1428_);
lean_ctor_set(v___x_1453_, 0, v___x_1461_);
v___x_1463_ = v___x_1453_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_k_1428_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_v_1429_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v_r_1447_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v_r_1431_);
v___x_1463_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v___x_1463_);
lean_ctor_set(v___x_1441_, 3, v___y_1459_);
lean_ctor_set(v___x_1441_, 2, v_v_1445_);
lean_ctor_set(v___x_1441_, 1, v_k_1444_);
lean_ctor_set(v___x_1441_, 0, v___x_1456_);
v___x_1465_ = v___x_1441_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_k_1444_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v_v_1445_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v___y_1459_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
v___jp_1468_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_nat_add(v___x_1455_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec(v___x_1455_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_l_1446_);
lean_ctor_set(v___x_1420_, 0, v___x_1470_);
v___x_1472_ = v___x_1420_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_l_1417_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_l_1446_);
v___x_1472_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_nat_add(v___x_1425_, v_size_1448_);
if (lean_obj_tag(v_r_1447_) == 0)
{
lean_object* v_size_1474_; 
v_size_1474_ = lean_ctor_get(v_r_1447_, 0);
lean_inc(v_size_1474_);
v___y_1458_ = v___x_1473_;
v___y_1459_ = v___x_1472_;
v___y_1460_ = v_size_1474_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_unsigned_to_nat(0u);
v___y_1458_ = v___x_1473_;
v___y_1459_ = v___x_1472_;
v___y_1460_ = v___x_1475_;
goto v___jp_1457_;
}
}
}
}
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
lean_del_object(v___x_1420_);
v___x_1485_ = lean_nat_add(v___x_1425_, v_size_1426_);
v___x_1486_ = lean_nat_add(v___x_1485_, v_size_1427_);
lean_dec(v_size_1427_);
v___x_1487_ = lean_nat_add(v___x_1485_, v_size_1443_);
lean_dec(v___x_1485_);
lean_inc_ref(v_l_1417_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 4, v_l_1430_);
lean_ctor_set(v___x_1441_, 3, v_l_1417_);
lean_ctor_set(v___x_1441_, 2, v_v_1416_);
lean_ctor_set(v___x_1441_, 1, v_k_1415_);
lean_ctor_set(v___x_1441_, 0, v___x_1487_);
v___x_1489_ = v___x_1441_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_l_1417_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_l_1430_);
v___x_1489_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_isSharedCheck_1496_ = !lean_is_exclusive(v_l_1417_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; lean_object* v_unused_1499_; lean_object* v_unused_1500_; lean_object* v_unused_1501_; 
v_unused_1497_ = lean_ctor_get(v_l_1417_, 4);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_l_1417_, 3);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_l_1417_, 2);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_l_1417_, 1);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_l_1417_, 0);
lean_dec(v_unused_1501_);
v___x_1491_ = v_l_1417_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_dec(v_l_1417_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 4, v_r_1431_);
lean_ctor_set(v___x_1491_, 3, v___x_1489_);
lean_ctor_set(v___x_1491_, 2, v_v_1429_);
lean_ctor_set(v___x_1491_, 1, v_k_1428_);
lean_ctor_set(v___x_1491_, 0, v___x_1486_);
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_k_1428_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_v_1429_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_r_1431_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1509_; 
v_l_1509_ = lean_ctor_get(v_impl_1424_, 3);
lean_inc(v_l_1509_);
if (lean_obj_tag(v_l_1509_) == 0)
{
lean_object* v_r_1510_; lean_object* v_k_1511_; lean_object* v_v_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1535_; 
v_r_1510_ = lean_ctor_get(v_impl_1424_, 4);
v_k_1511_ = lean_ctor_get(v_impl_1424_, 1);
v_v_1512_ = lean_ctor_get(v_impl_1424_, 2);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_impl_1424_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; lean_object* v_unused_1537_; 
v_unused_1536_ = lean_ctor_get(v_impl_1424_, 3);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v_impl_1424_, 0);
lean_dec(v_unused_1537_);
v___x_1514_ = v_impl_1424_;
v_isShared_1515_ = v_isSharedCheck_1535_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_r_1510_);
lean_inc(v_v_1512_);
lean_inc(v_k_1511_);
lean_dec(v_impl_1424_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1535_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v_k_1516_; lean_object* v_v_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1531_; 
v_k_1516_ = lean_ctor_get(v_l_1509_, 1);
v_v_1517_ = lean_ctor_get(v_l_1509_, 2);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_l_1509_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; 
v_unused_1532_ = lean_ctor_get(v_l_1509_, 4);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_l_1509_, 3);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_l_1509_, 0);
lean_dec(v_unused_1534_);
v___x_1519_ = v_l_1509_;
v_isShared_1520_ = v_isSharedCheck_1531_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_v_1517_);
lean_inc(v_k_1516_);
lean_dec(v_l_1509_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1531_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1510_, 2);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 4, v_r_1510_);
lean_ctor_set(v___x_1519_, 3, v_r_1510_);
lean_ctor_set(v___x_1519_, 2, v_v_1416_);
lean_ctor_set(v___x_1519_, 1, v_k_1415_);
lean_ctor_set(v___x_1519_, 0, v___x_1425_);
v___x_1523_ = v___x_1519_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_r_1510_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_r_1510_);
v___x_1523_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1525_; 
lean_inc(v_r_1510_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 3, v_r_1510_);
lean_ctor_set(v___x_1514_, 0, v___x_1425_);
v___x_1525_ = v___x_1514_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1511_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1512_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_r_1510_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v_r_1510_);
v___x_1525_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1527_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v___x_1525_);
lean_ctor_set(v___x_1420_, 3, v___x_1523_);
lean_ctor_set(v___x_1420_, 2, v_v_1517_);
lean_ctor_set(v___x_1420_, 1, v_k_1516_);
lean_ctor_set(v___x_1420_, 0, v___x_1521_);
v___x_1527_ = v___x_1420_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1521_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_k_1516_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_v_1517_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
}
else
{
lean_object* v_r_1538_; 
v_r_1538_ = lean_ctor_get(v_impl_1424_, 4);
lean_inc(v_r_1538_);
if (lean_obj_tag(v_r_1538_) == 0)
{
lean_object* v_k_1539_; lean_object* v_v_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1551_; 
v_k_1539_ = lean_ctor_get(v_impl_1424_, 1);
v_v_1540_ = lean_ctor_get(v_impl_1424_, 2);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_impl_1424_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; lean_object* v_unused_1553_; lean_object* v_unused_1554_; 
v_unused_1552_ = lean_ctor_get(v_impl_1424_, 4);
lean_dec(v_unused_1552_);
v_unused_1553_ = lean_ctor_get(v_impl_1424_, 3);
lean_dec(v_unused_1553_);
v_unused_1554_ = lean_ctor_get(v_impl_1424_, 0);
lean_dec(v_unused_1554_);
v___x_1542_ = v_impl_1424_;
v_isShared_1543_ = v_isSharedCheck_1551_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_v_1540_);
lean_inc(v_k_1539_);
lean_dec(v_impl_1424_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1551_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1544_ = lean_unsigned_to_nat(3u);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 4, v_l_1509_);
lean_ctor_set(v___x_1542_, 2, v_v_1416_);
lean_ctor_set(v___x_1542_, 1, v_k_1415_);
lean_ctor_set(v___x_1542_, 0, v___x_1425_);
v___x_1546_ = v___x_1542_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_l_1509_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_l_1509_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_r_1538_);
lean_ctor_set(v___x_1420_, 3, v___x_1546_);
lean_ctor_set(v___x_1420_, 2, v_v_1540_);
lean_ctor_set(v___x_1420_, 1, v_k_1539_);
lean_ctor_set(v___x_1420_, 0, v___x_1544_);
v___x_1548_ = v___x_1420_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1539_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1540_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_r_1538_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1555_ = lean_unsigned_to_nat(2u);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_impl_1424_);
lean_ctor_set(v___x_1420_, 3, v_r_1538_);
lean_ctor_set(v___x_1420_, 0, v___x_1555_);
v___x_1557_ = v___x_1420_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_r_1538_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_impl_1424_);
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
else
{
lean_object* v___x_1560_; 
lean_dec(v_v_1416_);
lean_dec(v_k_1415_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 2, v_v_1412_);
lean_ctor_set(v___x_1420_, 1, v_k_1411_);
v___x_1560_ = v___x_1420_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_size_1414_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v_k_1411_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_v_1412_);
lean_ctor_set(v_reuseFailAlloc_1561_, 3, v_l_1417_);
lean_ctor_set(v_reuseFailAlloc_1561_, 4, v_r_1418_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
else
{
lean_object* v_impl_1562_; lean_object* v___x_1563_; 
lean_dec(v_size_1414_);
v_impl_1562_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_1411_, v_v_1412_, v_l_1417_);
v___x_1563_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1418_) == 0)
{
lean_object* v_size_1564_; lean_object* v_size_1565_; lean_object* v_k_1566_; lean_object* v_v_1567_; lean_object* v_l_1568_; lean_object* v_r_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v_size_1564_ = lean_ctor_get(v_r_1418_, 0);
v_size_1565_ = lean_ctor_get(v_impl_1562_, 0);
lean_inc(v_size_1565_);
v_k_1566_ = lean_ctor_get(v_impl_1562_, 1);
lean_inc(v_k_1566_);
v_v_1567_ = lean_ctor_get(v_impl_1562_, 2);
lean_inc(v_v_1567_);
v_l_1568_ = lean_ctor_get(v_impl_1562_, 3);
lean_inc(v_l_1568_);
v_r_1569_ = lean_ctor_get(v_impl_1562_, 4);
lean_inc(v_r_1569_);
v___x_1570_ = lean_unsigned_to_nat(3u);
v___x_1571_ = lean_nat_mul(v___x_1570_, v_size_1564_);
v___x_1572_ = lean_nat_dec_lt(v___x_1571_, v_size_1565_);
lean_dec(v___x_1571_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
lean_dec(v_r_1569_);
lean_dec(v_l_1568_);
lean_dec(v_v_1567_);
lean_dec(v_k_1566_);
v___x_1573_ = lean_nat_add(v___x_1563_, v_size_1565_);
lean_dec(v_size_1565_);
v___x_1574_ = lean_nat_add(v___x_1573_, v_size_1564_);
lean_dec(v___x_1573_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 3, v_impl_1562_);
lean_ctor_set(v___x_1420_, 0, v___x_1574_);
v___x_1576_ = v___x_1420_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_impl_1562_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v_r_1418_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
else
{
lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1643_; 
v_isSharedCheck_1643_ = !lean_is_exclusive(v_impl_1562_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; lean_object* v_unused_1645_; lean_object* v_unused_1646_; lean_object* v_unused_1647_; lean_object* v_unused_1648_; 
v_unused_1644_ = lean_ctor_get(v_impl_1562_, 4);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_impl_1562_, 3);
lean_dec(v_unused_1645_);
v_unused_1646_ = lean_ctor_get(v_impl_1562_, 2);
lean_dec(v_unused_1646_);
v_unused_1647_ = lean_ctor_get(v_impl_1562_, 1);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_impl_1562_, 0);
lean_dec(v_unused_1648_);
v___x_1579_ = v_impl_1562_;
v_isShared_1580_ = v_isSharedCheck_1643_;
goto v_resetjp_1578_;
}
else
{
lean_dec(v_impl_1562_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1643_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_size_1581_; lean_object* v_size_1582_; lean_object* v_k_1583_; lean_object* v_v_1584_; lean_object* v_l_1585_; lean_object* v_r_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v_size_1581_ = lean_ctor_get(v_l_1568_, 0);
v_size_1582_ = lean_ctor_get(v_r_1569_, 0);
v_k_1583_ = lean_ctor_get(v_r_1569_, 1);
v_v_1584_ = lean_ctor_get(v_r_1569_, 2);
v_l_1585_ = lean_ctor_get(v_r_1569_, 3);
v_r_1586_ = lean_ctor_get(v_r_1569_, 4);
v___x_1587_ = lean_unsigned_to_nat(2u);
v___x_1588_ = lean_nat_mul(v___x_1587_, v_size_1581_);
v___x_1589_ = lean_nat_dec_lt(v_size_1582_, v___x_1588_);
lean_dec(v___x_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1618_; 
lean_inc(v_r_1586_);
lean_inc(v_l_1585_);
lean_inc(v_v_1584_);
lean_inc(v_k_1583_);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_r_1569_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; lean_object* v_unused_1620_; lean_object* v_unused_1621_; lean_object* v_unused_1622_; lean_object* v_unused_1623_; 
v_unused_1619_ = lean_ctor_get(v_r_1569_, 4);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v_r_1569_, 3);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v_r_1569_, 2);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v_r_1569_, 1);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_r_1569_, 0);
lean_dec(v_unused_1623_);
v___x_1591_ = v_r_1569_;
v_isShared_1592_ = v_isSharedCheck_1618_;
goto v_resetjp_1590_;
}
else
{
lean_dec(v_r_1569_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1618_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___x_1606_; lean_object* v___y_1608_; 
v___x_1593_ = lean_nat_add(v___x_1563_, v_size_1565_);
lean_dec(v_size_1565_);
v___x_1594_ = lean_nat_add(v___x_1593_, v_size_1564_);
lean_dec(v___x_1593_);
v___x_1606_ = lean_nat_add(v___x_1563_, v_size_1581_);
if (lean_obj_tag(v_l_1585_) == 0)
{
lean_object* v_size_1616_; 
v_size_1616_ = lean_ctor_get(v_l_1585_, 0);
lean_inc(v_size_1616_);
v___y_1608_ = v_size_1616_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_unsigned_to_nat(0u);
v___y_1608_ = v___x_1617_;
goto v___jp_1607_;
}
v___jp_1595_:
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1599_ = lean_nat_add(v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec(v___y_1597_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 4, v_r_1418_);
lean_ctor_set(v___x_1591_, 3, v_r_1586_);
lean_ctor_set(v___x_1591_, 2, v_v_1416_);
lean_ctor_set(v___x_1591_, 1, v_k_1415_);
lean_ctor_set(v___x_1591_, 0, v___x_1599_);
v___x_1601_ = v___x_1591_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_r_1586_);
lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_r_1418_);
v___x_1601_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1603_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v___x_1601_);
lean_ctor_set(v___x_1579_, 3, v___y_1596_);
lean_ctor_set(v___x_1579_, 2, v_v_1584_);
lean_ctor_set(v___x_1579_, 1, v_k_1583_);
lean_ctor_set(v___x_1579_, 0, v___x_1594_);
v___x_1603_ = v___x_1579_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1583_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1584_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v___y_1596_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
v___jp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_nat_add(v___x_1606_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec(v___x_1606_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_l_1585_);
lean_ctor_set(v___x_1420_, 3, v_l_1568_);
lean_ctor_set(v___x_1420_, 2, v_v_1567_);
lean_ctor_set(v___x_1420_, 1, v_k_1566_);
lean_ctor_set(v___x_1420_, 0, v___x_1609_);
v___x_1611_ = v___x_1420_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_l_1568_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_l_1585_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_nat_add(v___x_1563_, v_size_1564_);
if (lean_obj_tag(v_r_1586_) == 0)
{
lean_object* v_size_1613_; 
v_size_1613_ = lean_ctor_get(v_r_1586_, 0);
lean_inc(v_size_1613_);
v___y_1596_ = v___x_1611_;
v___y_1597_ = v___x_1612_;
v___y_1598_ = v_size_1613_;
goto v___jp_1595_;
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_unsigned_to_nat(0u);
v___y_1596_ = v___x_1611_;
v___y_1597_ = v___x_1612_;
v___y_1598_ = v___x_1614_;
goto v___jp_1595_;
}
}
}
}
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_del_object(v___x_1420_);
v___x_1624_ = lean_nat_add(v___x_1563_, v_size_1565_);
lean_dec(v_size_1565_);
v___x_1625_ = lean_nat_add(v___x_1624_, v_size_1564_);
lean_dec(v___x_1624_);
v___x_1626_ = lean_nat_add(v___x_1563_, v_size_1564_);
v___x_1627_ = lean_nat_add(v___x_1626_, v_size_1582_);
lean_dec(v___x_1626_);
lean_inc_ref(v_r_1418_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 4, v_r_1418_);
lean_ctor_set(v___x_1579_, 3, v_r_1569_);
lean_ctor_set(v___x_1579_, 2, v_v_1416_);
lean_ctor_set(v___x_1579_, 1, v_k_1415_);
lean_ctor_set(v___x_1579_, 0, v___x_1627_);
v___x_1629_ = v___x_1579_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1642_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1642_, 3, v_r_1569_);
lean_ctor_set(v_reuseFailAlloc_1642_, 4, v_r_1418_);
v___x_1629_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
v_isSharedCheck_1636_ = !lean_is_exclusive(v_r_1418_);
if (v_isSharedCheck_1636_ == 0)
{
lean_object* v_unused_1637_; lean_object* v_unused_1638_; lean_object* v_unused_1639_; lean_object* v_unused_1640_; lean_object* v_unused_1641_; 
v_unused_1637_ = lean_ctor_get(v_r_1418_, 4);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_r_1418_, 3);
lean_dec(v_unused_1638_);
v_unused_1639_ = lean_ctor_get(v_r_1418_, 2);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_r_1418_, 1);
lean_dec(v_unused_1640_);
v_unused_1641_ = lean_ctor_get(v_r_1418_, 0);
lean_dec(v_unused_1641_);
v___x_1631_ = v_r_1418_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_dec(v_r_1418_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 4, v___x_1629_);
lean_ctor_set(v___x_1631_, 3, v_l_1568_);
lean_ctor_set(v___x_1631_, 2, v_v_1567_);
lean_ctor_set(v___x_1631_, 1, v_k_1566_);
lean_ctor_set(v___x_1631_, 0, v___x_1625_);
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v_l_1568_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v___x_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1649_; 
v_l_1649_ = lean_ctor_get(v_impl_1562_, 3);
lean_inc(v_l_1649_);
if (lean_obj_tag(v_l_1649_) == 0)
{
lean_object* v_r_1650_; lean_object* v_k_1651_; lean_object* v_v_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1663_; 
v_r_1650_ = lean_ctor_get(v_impl_1562_, 4);
v_k_1651_ = lean_ctor_get(v_impl_1562_, 1);
v_v_1652_ = lean_ctor_get(v_impl_1562_, 2);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_impl_1562_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; lean_object* v_unused_1665_; 
v_unused_1664_ = lean_ctor_get(v_impl_1562_, 3);
lean_dec(v_unused_1664_);
v_unused_1665_ = lean_ctor_get(v_impl_1562_, 0);
lean_dec(v_unused_1665_);
v___x_1654_ = v_impl_1562_;
v_isShared_1655_ = v_isSharedCheck_1663_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_r_1650_);
lean_inc(v_v_1652_);
lean_inc(v_k_1651_);
lean_dec(v_impl_1562_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1663_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1656_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1650_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 3, v_r_1650_);
lean_ctor_set(v___x_1654_, 2, v_v_1416_);
lean_ctor_set(v___x_1654_, 1, v_k_1415_);
lean_ctor_set(v___x_1654_, 0, v___x_1563_);
v___x_1658_ = v___x_1654_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1662_, 3, v_r_1650_);
lean_ctor_set(v_reuseFailAlloc_1662_, 4, v_r_1650_);
v___x_1658_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v___x_1658_);
lean_ctor_set(v___x_1420_, 3, v_l_1649_);
lean_ctor_set(v___x_1420_, 2, v_v_1652_);
lean_ctor_set(v___x_1420_, 1, v_k_1651_);
lean_ctor_set(v___x_1420_, 0, v___x_1656_);
v___x_1660_ = v___x_1420_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1656_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_k_1651_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_v_1652_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_l_1649_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_object* v_r_1666_; 
v_r_1666_ = lean_ctor_get(v_impl_1562_, 4);
lean_inc(v_r_1666_);
if (lean_obj_tag(v_r_1666_) == 0)
{
lean_object* v_k_1667_; lean_object* v_v_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1691_; 
v_k_1667_ = lean_ctor_get(v_impl_1562_, 1);
v_v_1668_ = lean_ctor_get(v_impl_1562_, 2);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_impl_1562_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; lean_object* v_unused_1693_; lean_object* v_unused_1694_; 
v_unused_1692_ = lean_ctor_get(v_impl_1562_, 4);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_impl_1562_, 3);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v_impl_1562_, 0);
lean_dec(v_unused_1694_);
v___x_1670_ = v_impl_1562_;
v_isShared_1671_ = v_isSharedCheck_1691_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_v_1668_);
lean_inc(v_k_1667_);
lean_dec(v_impl_1562_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1691_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v_k_1672_; lean_object* v_v_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1687_; 
v_k_1672_ = lean_ctor_get(v_r_1666_, 1);
v_v_1673_ = lean_ctor_get(v_r_1666_, 2);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_r_1666_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; lean_object* v_unused_1689_; lean_object* v_unused_1690_; 
v_unused_1688_ = lean_ctor_get(v_r_1666_, 4);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_r_1666_, 3);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_r_1666_, 0);
lean_dec(v_unused_1690_);
v___x_1675_ = v_r_1666_;
v_isShared_1676_ = v_isSharedCheck_1687_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_v_1673_);
lean_inc(v_k_1672_);
lean_dec(v_r_1666_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1687_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_unsigned_to_nat(3u);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 4, v_l_1649_);
lean_ctor_set(v___x_1675_, 3, v_l_1649_);
lean_ctor_set(v___x_1675_, 2, v_v_1668_);
lean_ctor_set(v___x_1675_, 1, v_k_1667_);
lean_ctor_set(v___x_1675_, 0, v___x_1563_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_k_1667_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_v_1668_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_l_1649_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_l_1649_);
v___x_1679_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 4, v_l_1649_);
lean_ctor_set(v___x_1670_, 2, v_v_1416_);
lean_ctor_set(v___x_1670_, 1, v_k_1415_);
lean_ctor_set(v___x_1670_, 0, v___x_1563_);
v___x_1681_ = v___x_1670_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_l_1649_);
lean_ctor_set(v_reuseFailAlloc_1685_, 4, v_l_1649_);
v___x_1681_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v___x_1681_);
lean_ctor_set(v___x_1420_, 3, v___x_1679_);
lean_ctor_set(v___x_1420_, 2, v_v_1673_);
lean_ctor_set(v___x_1420_, 1, v_k_1672_);
lean_ctor_set(v___x_1420_, 0, v___x_1677_);
v___x_1683_ = v___x_1420_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_k_1672_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_v_1673_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v___x_1681_);
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
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = lean_unsigned_to_nat(2u);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 4, v_r_1666_);
lean_ctor_set(v___x_1420_, 3, v_impl_1562_);
lean_ctor_set(v___x_1420_, 0, v___x_1695_);
v___x_1697_ = v___x_1420_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_impl_1562_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v_r_1666_);
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
}
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
lean_ctor_set(v___x_1701_, 1, v_k_1411_);
lean_ctor_set(v___x_1701_, 2, v_v_1412_);
lean_ctor_set(v___x_1701_, 3, v_t_1413_);
lean_ctor_set(v___x_1701_, 4, v_t_1413_);
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(lean_object* v_k_1702_, lean_object* v_x_1703_){
_start:
{
if (lean_obj_tag(v_x_1703_) == 0)
{
lean_object* v___x_1704_; 
lean_dec_ref(v_k_1702_);
v___x_1704_ = lean_box(0);
return v___x_1704_;
}
else
{
lean_object* v_val_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_val_1705_ = lean_ctor_get(v_x_1703_, 0);
lean_inc(v_val_1705_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_k_1702_);
lean_ctor_set(v___x_1706_, 1, v_val_1705_);
v___x_1707_ = lean_box(0);
v___x_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4___boxed(lean_object* v_k_1709_, lean_object* v_x_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v_k_1709_, v_x_1710_);
lean_dec(v_x_1710_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(size_t v_sz_1712_, size_t v_i_1713_, lean_object* v_bs_1714_){
_start:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_usize_dec_lt(v_i_1713_, v_sz_1712_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1716_, 0, v_bs_1714_);
return v___x_1716_;
}
else
{
lean_object* v_v_1717_; lean_object* v___x_1718_; 
v_v_1717_ = lean_array_uget_borrowed(v_bs_1714_, v_i_1713_);
lean_inc(v_v_1717_);
v___x_1718_ = l_Lean_Lsp_instFromJsonCallHierarchyIncomingCall_fromJson(v_v_1717_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec_ref(v_bs_1714_);
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1728_; lean_object* v_bs_x27_1729_; size_t v___x_1730_; size_t v___x_1731_; lean_object* v___x_1732_; 
v_a_1727_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1727_);
lean_dec_ref(v___x_1718_);
v___x_1728_ = lean_unsigned_to_nat(0u);
v_bs_x27_1729_ = lean_array_uset(v_bs_1714_, v_i_1713_, v___x_1728_);
v___x_1730_ = ((size_t)1ULL);
v___x_1731_ = lean_usize_add(v_i_1713_, v___x_1730_);
v___x_1732_ = lean_array_uset(v_bs_x27_1729_, v_i_1713_, v_a_1727_);
v_i_1713_ = v___x_1731_;
v_bs_1714_ = v___x_1732_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_sz_1734_, lean_object* v_i_1735_, lean_object* v_bs_1736_){
_start:
{
size_t v_sz_boxed_1737_; size_t v_i_boxed_1738_; lean_object* v_res_1739_; 
v_sz_boxed_1737_ = lean_unbox_usize(v_sz_1734_);
lean_dec(v_sz_1734_);
v_i_boxed_1738_ = lean_unbox_usize(v_i_1735_);
lean_dec(v_i_1735_);
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_boxed_1737_, v_i_boxed_1738_, v_bs_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(lean_object* v_x_1740_){
_start:
{
if (lean_obj_tag(v_x_1740_) == 4)
{
lean_object* v_elems_1741_; size_t v_sz_1742_; size_t v___x_1743_; lean_object* v___x_1744_; 
v_elems_1741_ = lean_ctor_get(v_x_1740_, 0);
lean_inc_ref(v_elems_1741_);
lean_dec_ref(v_x_1740_);
v_sz_1742_ = lean_array_size(v_elems_1741_);
v___x_1743_ = ((size_t)0ULL);
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5_spec__9(v_sz_1742_, v___x_1743_, v_elems_1741_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1745_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_1746_ = lean_unsigned_to_nat(80u);
v___x_1747_ = l_Lean_Json_pretty(v_x_1740_, v___x_1746_);
v___x_1748_ = lean_string_append(v___x_1745_, v___x_1747_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1750_ = lean_string_append(v___x_1748_, v___x_1749_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(lean_object* v_x_1754_){
_start:
{
if (lean_obj_tag(v_x_1754_) == 0)
{
lean_object* v___x_1755_; 
v___x_1755_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3___closed__0));
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3_spec__5(v_x_1754_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1773_; 
v_a_1765_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1767_ = v___x_1756_;
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1756_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_a_1765_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1769_);
v___x_1771_ = v___x_1767_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(lean_object* v_expectedID_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Lsp_Ipc_stdout(v_a_1775_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1921_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1921_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1921_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_IO_FS_Stream_readLspMessage(v_a_1778_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1912_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1912_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1912_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___y_1788_; lean_object* v___y_1789_; 
switch(lean_obj_tag(v_a_1783_))
{
case 2:
{
lean_object* v_id_1795_; lean_object* v_result_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1840_; 
v_id_1795_ = lean_ctor_get(v_a_1783_, 0);
v_result_1796_ = lean_ctor_get(v_a_1783_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_a_1783_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1798_ = v_a_1783_;
v_isShared_1799_ = v_isSharedCheck_1840_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_result_1796_);
lean_inc(v_id_1795_);
lean_dec(v_a_1783_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1840_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
uint8_t v___x_1800_; 
v___x_1800_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_1795_, v_expectedID_1774_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; lean_object* v___y_1803_; 
lean_del_object(v___x_1798_);
lean_dec(v_result_1796_);
lean_del_object(v___x_1780_);
v___x_1801_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_1774_))
{
case 0:
{
lean_object* v_s_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_s_1814_ = lean_ctor_get(v_expectedID_1774_, 0);
lean_inc_ref(v_s_1814_);
lean_dec_ref(v_expectedID_1774_);
v___x_1815_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1816_ = lean_string_append(v___x_1815_, v_s_1814_);
lean_dec_ref(v_s_1814_);
v___x_1817_ = lean_string_append(v___x_1816_, v___x_1815_);
v___y_1803_ = v___x_1817_;
goto v___jp_1802_;
}
case 1:
{
lean_object* v_n_1818_; lean_object* v___x_1819_; 
v_n_1818_ = lean_ctor_get(v_expectedID_1774_, 0);
lean_inc_ref(v_n_1818_);
lean_dec_ref(v_expectedID_1774_);
v___x_1819_ = l_Lean_JsonNumber_toString(v_n_1818_);
v___y_1803_ = v___x_1819_;
goto v___jp_1802_;
}
default: 
{
lean_object* v___x_1820_; 
v___x_1820_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1803_ = v___x_1820_;
goto v___jp_1802_;
}
}
v___jp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_string_append(v___x_1801_, v___y_1803_);
lean_dec_ref(v___y_1803_);
v___x_1805_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_1806_ = lean_string_append(v___x_1804_, v___x_1805_);
switch(lean_obj_tag(v_id_1795_))
{
case 0:
{
lean_object* v_s_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v_s_1807_ = lean_ctor_get(v_id_1795_, 0);
lean_inc_ref(v_s_1807_);
lean_dec_ref(v_id_1795_);
v___x_1808_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_1809_ = lean_string_append(v___x_1808_, v_s_1807_);
lean_dec_ref(v_s_1807_);
v___x_1810_ = lean_string_append(v___x_1809_, v___x_1808_);
v___y_1788_ = v___x_1806_;
v___y_1789_ = v___x_1810_;
goto v___jp_1787_;
}
case 1:
{
lean_object* v_n_1811_; lean_object* v___x_1812_; 
v_n_1811_ = lean_ctor_get(v_id_1795_, 0);
lean_inc_ref(v_n_1811_);
lean_dec_ref(v_id_1795_);
v___x_1812_ = l_Lean_JsonNumber_toString(v_n_1811_);
v___y_1788_ = v___x_1806_;
v___y_1789_ = v___x_1812_;
goto v___jp_1787_;
}
default: 
{
lean_object* v___x_1813_; 
v___x_1813_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_1788_ = v___x_1806_;
v___y_1789_ = v___x_1813_;
goto v___jp_1787_;
}
}
}
}
else
{
lean_object* v___x_1821_; 
lean_dec(v_id_1795_);
lean_del_object(v___x_1785_);
lean_inc(v_result_1796_);
v___x_1821_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__3(v_result_1796_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
lean_del_object(v___x_1798_);
lean_dec(v_expectedID_1774_);
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v___x_1821_);
v___x_1823_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_1824_ = l_Lean_Json_compress(v_result_1796_);
v___x_1825_ = lean_string_append(v___x_1823_, v___x_1824_);
lean_dec_ref(v___x_1824_);
v___x_1826_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_1827_ = lean_string_append(v___x_1825_, v___x_1826_);
v___x_1828_ = lean_string_append(v___x_1827_, v_a_1822_);
lean_dec(v_a_1822_);
v___x_1829_ = lean_mk_io_user_error(v___x_1828_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 1);
lean_ctor_set(v___x_1780_, 0, v___x_1829_);
v___x_1831_ = v___x_1780_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; 
lean_dec(v_result_1796_);
v_a_1833_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1833_);
lean_dec_ref(v___x_1821_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 0);
lean_ctor_set(v___x_1798_, 1, v_a_1833_);
lean_ctor_set(v___x_1798_, 0, v_expectedID_1774_);
v___x_1835_ = v___x_1798_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_expectedID_1774_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_a_1833_);
v___x_1835_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1835_);
v___x_1837_ = v___x_1780_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_1841_; uint8_t v_code_1842_; lean_object* v_message_1843_; lean_object* v_data_x3f_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___x_1876_; lean_object* v___y_1878_; 
lean_del_object(v___x_1785_);
lean_dec(v_expectedID_1774_);
v_id_1841_ = lean_ctor_get(v_a_1783_, 0);
lean_inc(v_id_1841_);
v_code_1842_ = lean_ctor_get_uint8(v_a_1783_, sizeof(void*)*3);
v_message_1843_ = lean_ctor_get(v_a_1783_, 1);
lean_inc_ref(v_message_1843_);
v_data_x3f_1844_ = lean_ctor_get(v_a_1783_, 2);
lean_inc(v_data_x3f_1844_);
lean_dec_ref(v_a_1783_);
v___x_1845_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_1846_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_1876_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_1841_))
{
case 0:
{
lean_object* v_s_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_s_1894_ = lean_ctor_get(v_id_1841_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_id_1841_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v_id_1841_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_s_1894_);
lean_dec(v_id_1841_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 3);
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_s_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
v___y_1878_ = v___x_1899_;
goto v___jp_1877_;
}
}
}
case 1:
{
lean_object* v_n_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
v_n_1902_ = lean_ctor_get(v_id_1841_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_id_1841_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v_id_1841_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_n_1902_);
lean_dec(v_id_1841_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 2);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_n_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v___y_1878_ = v___x_1907_;
goto v___jp_1877_;
}
}
}
default: 
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_box(0);
v___y_1878_ = v___x_1910_;
goto v___jp_1877_;
}
}
v___jp_1847_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_inc(v___y_1851_);
lean_inc_ref(v___y_1848_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___y_1848_);
lean_ctor_set(v___x_1852_, 1, v___y_1851_);
v___x_1853_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_1854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_message_1843_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1852_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_1860_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_1859_, v_data_x3f_1844_);
lean_dec(v_data_x3f_1844_);
v___x_1861_ = l_List_appendTR___redArg(v___x_1858_, v___x_1860_);
v___x_1862_ = l_Lean_Json_mkObj(v___x_1861_);
lean_dec(v___x_1861_);
lean_inc_ref(v___y_1849_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___y_1849_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v___x_1856_);
v___x_1865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___y_1850_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1846_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_Lean_Json_mkObj(v___x_1866_);
lean_dec_ref(v___x_1866_);
v___x_1868_ = l_Lean_Json_compress(v___x_1867_);
v___x_1869_ = lean_string_append(v___x_1845_, v___x_1868_);
lean_dec_ref(v___x_1868_);
v___x_1870_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_1871_ = lean_string_append(v___x_1869_, v___x_1870_);
v___x_1872_ = lean_mk_io_user_error(v___x_1871_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 1);
lean_ctor_set(v___x_1780_, 0, v___x_1872_);
v___x_1874_ = v___x_1780_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
v___jp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1876_);
lean_ctor_set(v___x_1879_, 1, v___y_1878_);
v___x_1880_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_1881_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_1842_)
{
case 0:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1882_;
goto v___jp_1847_;
}
case 1:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1883_;
goto v___jp_1847_;
}
case 2:
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1884_;
goto v___jp_1847_;
}
case 3:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1885_;
goto v___jp_1847_;
}
case 4:
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1886_;
goto v___jp_1847_;
}
case 5:
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1887_;
goto v___jp_1847_;
}
case 6:
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1888_;
goto v___jp_1847_;
}
case 7:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1889_;
goto v___jp_1847_;
}
case 8:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1890_;
goto v___jp_1847_;
}
case 9:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1891_;
goto v___jp_1847_;
}
case 10:
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1892_;
goto v___jp_1847_;
}
default: 
{
lean_object* v___x_1893_; 
v___x_1893_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_1848_ = v___x_1881_;
v___y_1849_ = v___x_1880_;
v___y_1850_ = v___x_1879_;
v___y_1851_ = v___x_1893_;
goto v___jp_1847_;
}
}
}
}
default: 
{
lean_del_object(v___x_1785_);
lean_dec(v_a_1783_);
lean_del_object(v___x_1780_);
goto _start;
}
}
v___jp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1790_ = lean_string_append(v___y_1788_, v___y_1789_);
lean_dec_ref(v___y_1789_);
v___x_1791_ = lean_mk_io_user_error(v___x_1790_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 1);
lean_ctor_set(v___x_1785_, 0, v___x_1791_);
v___x_1793_ = v___x_1785_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
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
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_del_object(v___x_1780_);
lean_dec(v_expectedID_1774_);
v_a_1913_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1782_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1782_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_expectedID_1774_);
v_a_1922_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1777_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1777_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2___boxed(lean_object* v_expectedID_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v_expectedID_1930_, v_a_1931_);
lean_dec_ref(v_a_1931_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(lean_object* v_v_1934_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = l_Lean_Lsp_instToJsonCallHierarchyIncomingCallsParams_toJson(v_v_1934_);
v___x_1936_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(lean_object* v_h_1937_, lean_object* v_r_1938_){
_start:
{
lean_object* v_id_1940_; lean_object* v_method_1941_; lean_object* v_param_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1962_; 
v_id_1940_ = lean_ctor_get(v_r_1938_, 0);
v_method_1941_ = lean_ctor_get(v_r_1938_, 1);
v_param_1942_ = lean_ctor_get(v_r_1938_, 2);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_r_1938_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1944_ = v_r_1938_;
v_isShared_1945_ = v_isSharedCheck_1962_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_param_1942_);
lean_inc(v_method_1941_);
lean_inc(v_id_1940_);
lean_dec(v_r_1938_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1962_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___y_1947_; lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1_spec__2(v_param_1942_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v___x_1953_; 
lean_dec_ref(v___x_1952_);
v___x_1953_ = lean_box(0);
v___y_1947_ = v___x_1953_;
goto v___jp_1946_;
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
v_a_1954_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1952_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1952_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
v___y_1947_ = v___x_1959_;
goto v___jp_1946_;
}
}
}
v___jp_1946_:
{
lean_object* v___x_1949_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 2, v___y_1947_);
v___x_1949_ = v___x_1944_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_id_1940_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_method_1941_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v___y_1947_);
v___x_1949_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_IO_FS_Stream_writeLspMessage(v_h_1937_, v___x_1949_);
return v___x_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1___boxed(lean_object* v_h_1963_, lean_object* v_r_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_h_1963_, v_r_1964_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(lean_object* v_r_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v___x_1970_; lean_object* v_a_1971_; lean_object* v___x_1972_; 
v___x_1970_ = l_Lean_Lsp_Ipc_stdin(v_a_1968_);
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref(v___x_1970_);
v___x_1972_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1_spec__1(v_a_1971_, v_r_1967_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1___boxed(lean_object* v_r_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v_r_1973_, v_a_1974_);
lean_dec_ref(v_a_1974_);
return v_res_1976_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(lean_object* v_k_1977_, lean_object* v_t_1978_){
_start:
{
if (lean_obj_tag(v_t_1978_) == 0)
{
lean_object* v_k_1979_; lean_object* v_l_1980_; lean_object* v_r_1981_; uint8_t v___x_1982_; 
v_k_1979_ = lean_ctor_get(v_t_1978_, 1);
v_l_1980_ = lean_ctor_get(v_t_1978_, 3);
v_r_1981_ = lean_ctor_get(v_t_1978_, 4);
v___x_1982_ = lean_string_dec_lt(v_k_1977_, v_k_1979_);
if (v___x_1982_ == 0)
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_string_dec_eq(v_k_1977_, v_k_1979_);
if (v___x_1983_ == 0)
{
v_t_1978_ = v_r_1981_;
goto _start;
}
else
{
return v___x_1983_;
}
}
else
{
v_t_1978_ = v_l_1980_;
goto _start;
}
}
else
{
uint8_t v___x_1986_; 
v___x_1986_ = 0;
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg___boxed(lean_object* v_k_1987_, lean_object* v_t_1988_){
_start:
{
uint8_t v_res_1989_; lean_object* v_r_1990_; 
v_res_1989_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_1987_, v_t_1988_);
lean_dec(v_t_1988_);
lean_dec_ref(v_k_1987_);
v_r_1990_ = lean_box(v_res_1989_);
return v_r_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(lean_object* v_requestNo_1998_, lean_object* v_item_1999_, lean_object* v_fromRanges_2000_, lean_object* v_visited_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_name_2004_; uint8_t v___x_2005_; 
v_name_2004_ = lean_ctor_get(v_item_1999_, 0);
v___x_2005_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_2004_, v_visited_2001_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_inc(v_requestNo_1998_);
v___x_2006_ = l_Lean_JsonNumber_fromNat(v_requestNo_1998_);
v___x_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
v___x_2008_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_1999_);
lean_inc_ref(v___x_2007_);
v___x_2009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2007_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
lean_ctor_set(v___x_2009_, 2, v_item_1999_);
v___x_2010_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__1(v___x_2009_, v_a_2002_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v___x_2011_; 
lean_dec_ref(v___x_2010_);
v___x_2011_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2(v___x_2007_, v_a_2002_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2049_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref(v___x_2011_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_box(0);
lean_inc_ref(v_name_2004_);
v___x_2056_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_2004_, v___x_2055_, v_visited_2001_);
v___y_2049_ = v___x_2056_;
goto v___jp_2048_;
}
else
{
v___y_2049_ = v_visited_2001_;
goto v___jp_2048_;
}
v___jp_2013_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; size_t v_sz_2019_; size_t v___x_2020_; lean_object* v___x_2021_; 
v___x_2017_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___y_2015_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
v_sz_2019_ = lean_array_size(v___y_2016_);
v___x_2020_ = ((size_t)0ULL);
v___x_2021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___y_2014_, v___y_2016_, v_sz_2019_, v___x_2020_, v___x_2018_, v_a_2002_);
lean_dec_ref(v___y_2016_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2039_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2039_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2039_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v_fst_2026_; lean_object* v_snd_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2038_; 
v_fst_2026_ = lean_ctor_get(v_a_2022_, 0);
v_snd_2027_ = lean_ctor_get(v_a_2022_, 1);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_a_2022_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2029_ = v_a_2022_;
v_isShared_2030_ = v_isSharedCheck_2038_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_snd_2027_);
lean_inc(v_fst_2026_);
lean_dec(v_a_2022_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2038_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2031_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2031_, 0, v_item_1999_);
lean_ctor_set(v___x_2031_, 1, v_fromRanges_2000_);
lean_ctor_set(v___x_2031_, 2, v_snd_2027_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v_fst_2026_);
lean_ctor_set(v___x_2029_, 0, v___x_2031_);
v___x_2033_ = v___x_2029_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_fst_2026_);
v___x_2033_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2035_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2033_);
v___x_2035_ = v___x_2024_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v_fromRanges_2000_);
lean_dec_ref(v_item_1999_);
v_a_2040_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2021_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2021_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
v___jp_2048_:
{
lean_object* v_result_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_result_2050_ = lean_ctor_get(v_a_2012_, 1);
lean_inc(v_result_2050_);
lean_dec(v_a_2012_);
v___x_2051_ = lean_unsigned_to_nat(1u);
v___x_2052_ = lean_nat_add(v_requestNo_1998_, v___x_2051_);
lean_dec(v_requestNo_1998_);
if (lean_obj_tag(v_result_2050_) == 0)
{
lean_object* v___x_2053_; 
v___x_2053_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__2));
v___y_2014_ = v___y_2049_;
v___y_2015_ = v___x_2052_;
v___y_2016_ = v___x_2053_;
goto v___jp_2013_;
}
else
{
lean_object* v_val_2054_; 
v_val_2054_ = lean_ctor_get(v_result_2050_, 0);
lean_inc(v_val_2054_);
lean_dec_ref(v_result_2050_);
v___y_2014_ = v___y_2049_;
v___y_2015_ = v___x_2052_;
v___y_2016_ = v_val_2054_;
goto v___jp_2013_;
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_visited_2001_);
lean_dec_ref(v_fromRanges_2000_);
lean_dec_ref(v_item_1999_);
lean_dec(v_requestNo_1998_);
v_a_2057_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2011_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2011_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v___x_2007_);
lean_dec(v_visited_2001_);
lean_dec_ref(v_fromRanges_2000_);
lean_dec_ref(v_item_1999_);
lean_dec(v_requestNo_1998_);
v_a_2065_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2010_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2010_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec(v_visited_2001_);
lean_dec_ref(v_fromRanges_2000_);
v___x_2073_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2074_, 0, v_item_1999_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
lean_ctor_set(v___x_2074_, 2, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
lean_ctor_set(v___x_2075_, 1, v_requestNo_1998_);
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(lean_object* v___x_2077_, lean_object* v_as_2078_, size_t v_sz_2079_, size_t v_i_2080_, lean_object* v_b_2081_, lean_object* v___y_2082_){
_start:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_usize_dec_lt(v_i_2080_, v_sz_2079_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_dec(v___x_2077_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_b_2081_);
return v___x_2085_;
}
else
{
lean_object* v_fst_2086_; lean_object* v_snd_2087_; lean_object* v_a_2088_; lean_object* v_from_2089_; lean_object* v_fromRanges_2090_; lean_object* v___x_2091_; 
v_fst_2086_ = lean_ctor_get(v_b_2081_, 0);
lean_inc(v_fst_2086_);
v_snd_2087_ = lean_ctor_get(v_b_2081_, 1);
lean_inc(v_snd_2087_);
lean_dec_ref(v_b_2081_);
v_a_2088_ = lean_array_uget_borrowed(v_as_2078_, v_i_2080_);
v_from_2089_ = lean_ctor_get(v_a_2088_, 0);
v_fromRanges_2090_ = lean_ctor_get(v_a_2088_, 1);
lean_inc(v___x_2077_);
lean_inc_ref(v_fromRanges_2090_);
lean_inc_ref(v_from_2089_);
v___x_2091_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2086_, v_from_2089_, v_fromRanges_2090_, v___x_2077_, v___y_2082_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v_fst_2093_; lean_object* v_snd_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2105_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref(v___x_2091_);
v_fst_2093_ = lean_ctor_get(v_a_2092_, 0);
v_snd_2094_ = lean_ctor_get(v_a_2092_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_a_2092_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2096_ = v_a_2092_;
v_isShared_2097_ = v_isSharedCheck_2105_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_snd_2094_);
lean_inc(v_fst_2093_);
lean_dec(v_a_2092_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2105_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2098_ = lean_array_push(v_snd_2087_, v_fst_2093_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v___x_2098_);
lean_ctor_set(v___x_2096_, 0, v_snd_2094_);
v___x_2100_ = v___x_2096_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_snd_2094_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
size_t v___x_2101_; size_t v___x_2102_; 
v___x_2101_ = ((size_t)1ULL);
v___x_2102_ = lean_usize_add(v_i_2080_, v___x_2101_);
v_i_2080_ = v___x_2102_;
v_b_2081_ = v___x_2100_;
goto _start;
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_snd_2087_);
lean_dec(v___x_2077_);
v_a_2106_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2091_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2091_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3___boxed(lean_object* v___x_2114_, lean_object* v_as_2115_, lean_object* v_sz_2116_, lean_object* v_i_2117_, lean_object* v_b_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
size_t v_sz_boxed_2121_; size_t v_i_boxed_2122_; lean_object* v_res_2123_; 
v_sz_boxed_2121_ = lean_unbox_usize(v_sz_2116_);
lean_dec(v_sz_2116_);
v_i_boxed_2122_ = lean_unbox_usize(v_i_2117_);
lean_dec(v_i_2117_);
v_res_2123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__3(v___x_2114_, v_as_2115_, v_sz_boxed_2121_, v_i_boxed_2122_, v_b_2118_, v___y_2119_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_as_2115_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___boxed(lean_object* v_requestNo_2124_, lean_object* v_item_2125_, lean_object* v_fromRanges_2126_, lean_object* v_visited_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_requestNo_2124_, v_item_2125_, v_fromRanges_2126_, v_visited_2127_, v_a_2128_);
lean_dec_ref(v_a_2128_);
return v_res_2130_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(lean_object* v_00_u03b2_2131_, lean_object* v_k_2132_, lean_object* v_t_2133_){
_start:
{
uint8_t v___x_2134_; 
v___x_2134_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_k_2132_, v_t_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___boxed(lean_object* v_00_u03b2_2135_, lean_object* v_k_2136_, lean_object* v_t_2137_){
_start:
{
uint8_t v_res_2138_; lean_object* v_r_2139_; 
v_res_2138_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0(v_00_u03b2_2135_, v_k_2136_, v_t_2137_);
lean_dec(v_t_2137_);
lean_dec_ref(v_k_2136_);
v_r_2139_ = lean_box(v_res_2138_);
return v_r_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4(lean_object* v_00_u03b2_2140_, lean_object* v_k_2141_, lean_object* v_v_2142_, lean_object* v_t_2143_, lean_object* v_hl_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_k_2141_, v_v_2142_, v_t_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2146_, size_t v_i_2147_, lean_object* v_bs_2148_){
_start:
{
uint8_t v___x_2149_; 
v___x_2149_ = lean_usize_dec_lt(v_i_2147_, v_sz_2146_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
v___x_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2150_, 0, v_bs_2148_);
return v___x_2150_;
}
else
{
lean_object* v_v_2151_; lean_object* v___x_2152_; 
v_v_2151_ = lean_array_uget_borrowed(v_bs_2148_, v_i_2147_);
lean_inc(v_v_2151_);
v___x_2152_ = l_Lean_Lsp_instFromJsonCallHierarchyItem_fromJson(v_v_2151_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v_bs_2148_);
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2162_; lean_object* v_bs_x27_2163_; size_t v___x_2164_; size_t v___x_2165_; lean_object* v___x_2166_; 
v_a_2161_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2161_);
lean_dec_ref(v___x_2152_);
v___x_2162_ = lean_unsigned_to_nat(0u);
v_bs_x27_2163_ = lean_array_uset(v_bs_2148_, v_i_2147_, v___x_2162_);
v___x_2164_ = ((size_t)1ULL);
v___x_2165_ = lean_usize_add(v_i_2147_, v___x_2164_);
v___x_2166_ = lean_array_uset(v_bs_x27_2163_, v_i_2147_, v_a_2161_);
v_i_2147_ = v___x_2165_;
v_bs_2148_ = v___x_2166_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2168_, lean_object* v_i_2169_, lean_object* v_bs_2170_){
_start:
{
size_t v_sz_boxed_2171_; size_t v_i_boxed_2172_; lean_object* v_res_2173_; 
v_sz_boxed_2171_ = lean_unbox_usize(v_sz_2168_);
lean_dec(v_sz_2168_);
v_i_boxed_2172_ = lean_unbox_usize(v_i_2169_);
lean_dec(v_i_2169_);
v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2171_, v_i_boxed_2172_, v_bs_2170_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(lean_object* v_x_2174_){
_start:
{
if (lean_obj_tag(v_x_2174_) == 4)
{
lean_object* v_elems_2175_; size_t v_sz_2176_; size_t v___x_2177_; lean_object* v___x_2178_; 
v_elems_2175_ = lean_ctor_get(v_x_2174_, 0);
lean_inc_ref(v_elems_2175_);
lean_dec_ref(v_x_2174_);
v_sz_2176_ = lean_array_size(v_elems_2175_);
v___x_2177_ = ((size_t)0ULL);
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4_spec__6(v_sz_2176_, v___x_2177_, v_elems_2175_);
return v___x_2178_;
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2179_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2180_ = lean_unsigned_to_nat(80u);
v___x_2181_ = l_Lean_Json_pretty(v_x_2174_, v___x_2180_);
v___x_2182_ = lean_string_append(v___x_2179_, v___x_2181_);
lean_dec_ref(v___x_2181_);
v___x_2183_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2184_ = lean_string_append(v___x_2182_, v___x_2183_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
return v___x_2185_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(lean_object* v_x_2188_){
_start:
{
if (lean_obj_tag(v_x_2188_) == 0)
{
lean_object* v___x_2189_; 
v___x_2189_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2___closed__0));
return v___x_2189_;
}
else
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2_spec__4(v_x_2188_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2207_; 
v_a_2199_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2201_ = v___x_2190_;
v_isShared_2202_ = v_isSharedCheck_2207_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2190_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2207_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v_a_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2203_);
v___x_2205_ = v___x_2201_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(lean_object* v_expectedID_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_Lsp_Ipc_stdout(v_a_2209_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2355_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2355_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2355_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_IO_FS_Stream_readLspMessage(v_a_2212_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2346_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2346_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2346_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___y_2222_; lean_object* v___y_2223_; 
switch(lean_obj_tag(v_a_2217_))
{
case 2:
{
lean_object* v_id_2229_; lean_object* v_result_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2274_; 
v_id_2229_ = lean_ctor_get(v_a_2217_, 0);
v_result_2230_ = lean_ctor_get(v_a_2217_, 1);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_a_2217_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2232_ = v_a_2217_;
v_isShared_2233_ = v_isSharedCheck_2274_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_result_2230_);
lean_inc(v_id_2229_);
lean_dec(v_a_2217_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2274_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
uint8_t v___x_2234_; 
v___x_2234_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2229_, v_expectedID_2208_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; lean_object* v___y_2237_; 
lean_del_object(v___x_2232_);
lean_dec(v_result_2230_);
lean_del_object(v___x_2214_);
v___x_2235_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2208_))
{
case 0:
{
lean_object* v_s_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_s_2248_ = lean_ctor_get(v_expectedID_2208_, 0);
lean_inc_ref(v_s_2248_);
lean_dec_ref(v_expectedID_2208_);
v___x_2249_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2250_ = lean_string_append(v___x_2249_, v_s_2248_);
lean_dec_ref(v_s_2248_);
v___x_2251_ = lean_string_append(v___x_2250_, v___x_2249_);
v___y_2237_ = v___x_2251_;
goto v___jp_2236_;
}
case 1:
{
lean_object* v_n_2252_; lean_object* v___x_2253_; 
v_n_2252_ = lean_ctor_get(v_expectedID_2208_, 0);
lean_inc_ref(v_n_2252_);
lean_dec_ref(v_expectedID_2208_);
v___x_2253_ = l_Lean_JsonNumber_toString(v_n_2252_);
v___y_2237_ = v___x_2253_;
goto v___jp_2236_;
}
default: 
{
lean_object* v___x_2254_; 
v___x_2254_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2237_ = v___x_2254_;
goto v___jp_2236_;
}
}
v___jp_2236_:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = lean_string_append(v___x_2235_, v___y_2237_);
lean_dec_ref(v___y_2237_);
v___x_2239_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2240_ = lean_string_append(v___x_2238_, v___x_2239_);
switch(lean_obj_tag(v_id_2229_))
{
case 0:
{
lean_object* v_s_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_s_2241_ = lean_ctor_get(v_id_2229_, 0);
lean_inc_ref(v_s_2241_);
lean_dec_ref(v_id_2229_);
v___x_2242_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2243_ = lean_string_append(v___x_2242_, v_s_2241_);
lean_dec_ref(v_s_2241_);
v___x_2244_ = lean_string_append(v___x_2243_, v___x_2242_);
v___y_2222_ = v___x_2240_;
v___y_2223_ = v___x_2244_;
goto v___jp_2221_;
}
case 1:
{
lean_object* v_n_2245_; lean_object* v___x_2246_; 
v_n_2245_ = lean_ctor_get(v_id_2229_, 0);
lean_inc_ref(v_n_2245_);
lean_dec_ref(v_id_2229_);
v___x_2246_ = l_Lean_JsonNumber_toString(v_n_2245_);
v___y_2222_ = v___x_2240_;
v___y_2223_ = v___x_2246_;
goto v___jp_2221_;
}
default: 
{
lean_object* v___x_2247_; 
v___x_2247_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2222_ = v___x_2240_;
v___y_2223_ = v___x_2247_;
goto v___jp_2221_;
}
}
}
}
else
{
lean_object* v___x_2255_; 
lean_dec(v_id_2229_);
lean_del_object(v___x_2219_);
lean_inc(v_result_2230_);
v___x_2255_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1_spec__2(v_result_2230_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
lean_del_object(v___x_2232_);
lean_dec(v_expectedID_2208_);
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref(v___x_2255_);
v___x_2257_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2258_ = l_Lean_Json_compress(v_result_2230_);
v___x_2259_ = lean_string_append(v___x_2257_, v___x_2258_);
lean_dec_ref(v___x_2258_);
v___x_2260_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2261_ = lean_string_append(v___x_2259_, v___x_2260_);
v___x_2262_ = lean_string_append(v___x_2261_, v_a_2256_);
lean_dec(v_a_2256_);
v___x_2263_ = lean_mk_io_user_error(v___x_2262_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set_tag(v___x_2214_, 1);
lean_ctor_set(v___x_2214_, 0, v___x_2263_);
v___x_2265_ = v___x_2214_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; 
lean_dec(v_result_2230_);
v_a_2267_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2267_);
lean_dec_ref(v___x_2255_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 0);
lean_ctor_set(v___x_2232_, 1, v_a_2267_);
lean_ctor_set(v___x_2232_, 0, v_expectedID_2208_);
v___x_2269_ = v___x_2232_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_expectedID_2208_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_a_2267_);
v___x_2269_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2271_; 
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2269_);
v___x_2271_ = v___x_2214_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2275_; uint8_t v_code_2276_; lean_object* v_message_2277_; lean_object* v_data_x3f_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___x_2310_; lean_object* v___y_2312_; 
lean_del_object(v___x_2219_);
lean_dec(v_expectedID_2208_);
v_id_2275_ = lean_ctor_get(v_a_2217_, 0);
lean_inc(v_id_2275_);
v_code_2276_ = lean_ctor_get_uint8(v_a_2217_, sizeof(void*)*3);
v_message_2277_ = lean_ctor_get(v_a_2217_, 1);
lean_inc_ref(v_message_2277_);
v_data_x3f_2278_ = lean_ctor_get(v_a_2217_, 2);
lean_inc(v_data_x3f_2278_);
lean_dec_ref(v_a_2217_);
v___x_2279_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2280_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2310_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2275_))
{
case 0:
{
lean_object* v_s_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
v_s_2328_ = lean_ctor_get(v_id_2275_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_id_2275_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v_id_2275_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_s_2328_);
lean_dec(v_id_2275_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
lean_ctor_set_tag(v___x_2330_, 3);
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_s_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
v___y_2312_ = v___x_2333_;
goto v___jp_2311_;
}
}
}
case 1:
{
lean_object* v_n_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
v_n_2336_ = lean_ctor_get(v_id_2275_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_id_2275_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v_id_2275_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_n_2336_);
lean_dec(v_id_2275_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set_tag(v___x_2338_, 2);
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_n_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
v___y_2312_ = v___x_2341_;
goto v___jp_2311_;
}
}
}
default: 
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_box(0);
v___y_2312_ = v___x_2344_;
goto v___jp_2311_;
}
}
v___jp_2281_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
lean_inc(v___y_2285_);
lean_inc_ref(v___y_2283_);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___y_2283_);
lean_ctor_set(v___x_2286_, 1, v___y_2285_);
v___x_2287_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2288_, 0, v_message_2277_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = lean_box(0);
v___x_2291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2286_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2294_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2293_, v_data_x3f_2278_);
lean_dec(v_data_x3f_2278_);
v___x_2295_ = l_List_appendTR___redArg(v___x_2292_, v___x_2294_);
v___x_2296_ = l_Lean_Json_mkObj(v___x_2295_);
lean_dec(v___x_2295_);
lean_inc_ref(v___y_2284_);
v___x_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___y_2284_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___x_2290_);
v___x_2299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___y_2282_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2280_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = l_Lean_Json_mkObj(v___x_2300_);
lean_dec_ref(v___x_2300_);
v___x_2302_ = l_Lean_Json_compress(v___x_2301_);
v___x_2303_ = lean_string_append(v___x_2279_, v___x_2302_);
lean_dec_ref(v___x_2302_);
v___x_2304_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2305_ = lean_string_append(v___x_2303_, v___x_2304_);
v___x_2306_ = lean_mk_io_user_error(v___x_2305_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set_tag(v___x_2214_, 1);
lean_ctor_set(v___x_2214_, 0, v___x_2306_);
v___x_2308_ = v___x_2214_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
v___jp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2310_);
lean_ctor_set(v___x_2313_, 1, v___y_2312_);
v___x_2314_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2315_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2276_)
{
case 0:
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2316_;
goto v___jp_2281_;
}
case 1:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2317_;
goto v___jp_2281_;
}
case 2:
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2318_;
goto v___jp_2281_;
}
case 3:
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2319_;
goto v___jp_2281_;
}
case 4:
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2320_;
goto v___jp_2281_;
}
case 5:
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2321_;
goto v___jp_2281_;
}
case 6:
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2322_;
goto v___jp_2281_;
}
case 7:
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2323_;
goto v___jp_2281_;
}
case 8:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2324_;
goto v___jp_2281_;
}
case 9:
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2325_;
goto v___jp_2281_;
}
case 10:
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2326_;
goto v___jp_2281_;
}
default: 
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2282_ = v___x_2313_;
v___y_2283_ = v___x_2315_;
v___y_2284_ = v___x_2314_;
v___y_2285_ = v___x_2327_;
goto v___jp_2281_;
}
}
}
}
default: 
{
lean_del_object(v___x_2219_);
lean_dec(v_a_2217_);
lean_del_object(v___x_2214_);
goto _start;
}
}
v___jp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2224_ = lean_string_append(v___y_2222_, v___y_2223_);
lean_dec_ref(v___y_2223_);
v___x_2225_ = lean_mk_io_user_error(v___x_2224_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set_tag(v___x_2219_, 1);
lean_ctor_set(v___x_2219_, 0, v___x_2225_);
v___x_2227_ = v___x_2219_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
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
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_del_object(v___x_2214_);
lean_dec(v_expectedID_2208_);
v_a_2347_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2216_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2216_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec(v_expectedID_2208_);
v_a_2356_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2211_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2211_);
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
return v___x_2361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1___boxed(lean_object* v_expectedID_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v_expectedID_2364_, v_a_2365_);
lean_dec_ref(v_a_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(lean_object* v_as_2368_, size_t v_sz_2369_, size_t v_i_2370_, lean_object* v_b_2371_, lean_object* v___y_2372_){
_start:
{
uint8_t v___x_2374_; 
v___x_2374_ = lean_usize_dec_lt(v_i_2370_, v_sz_2369_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2375_, 0, v_b_2371_);
return v___x_2375_;
}
else
{
lean_object* v_fst_2376_; lean_object* v_snd_2377_; lean_object* v_a_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v_fst_2376_ = lean_ctor_get(v_b_2371_, 0);
lean_inc(v_fst_2376_);
v_snd_2377_ = lean_ctor_get(v_b_2371_, 1);
lean_inc(v_snd_2377_);
lean_dec_ref(v_b_2371_);
v_a_2378_ = lean_array_uget_borrowed(v_as_2368_, v_i_2370_);
v___x_2379_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2380_ = lean_box(1);
lean_inc(v_a_2378_);
v___x_2381_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go(v_fst_2376_, v_a_2378_, v___x_2379_, v___x_2380_, v___y_2372_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v_fst_2383_; lean_object* v_snd_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2395_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref(v___x_2381_);
v_fst_2383_ = lean_ctor_get(v_a_2382_, 0);
v_snd_2384_ = lean_ctor_get(v_a_2382_, 1);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_a_2382_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2386_ = v_a_2382_;
v_isShared_2387_ = v_isSharedCheck_2395_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_snd_2384_);
lean_inc(v_fst_2383_);
lean_dec(v_a_2382_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2395_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; lean_object* v___x_2390_; 
v___x_2388_ = lean_array_push(v_snd_2377_, v_fst_2383_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 1, v___x_2388_);
lean_ctor_set(v___x_2386_, 0, v_snd_2384_);
v___x_2390_ = v___x_2386_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_snd_2384_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
size_t v___x_2391_; size_t v___x_2392_; 
v___x_2391_ = ((size_t)1ULL);
v___x_2392_ = lean_usize_add(v_i_2370_, v___x_2391_);
v_i_2370_ = v___x_2392_;
v_b_2371_ = v___x_2390_;
goto _start;
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_snd_2377_);
v_a_2396_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2381_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2381_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2___boxed(lean_object* v_as_2404_, lean_object* v_sz_2405_, lean_object* v_i_2406_, lean_object* v_b_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
size_t v_sz_boxed_2410_; size_t v_i_boxed_2411_; lean_object* v_res_2412_; 
v_sz_boxed_2410_ = lean_unbox_usize(v_sz_2405_);
lean_dec(v_sz_2405_);
v_i_boxed_2411_ = lean_unbox_usize(v_i_2406_);
lean_dec(v_i_2406_);
v_res_2412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v_as_2404_, v_sz_boxed_2410_, v_i_boxed_2411_, v_b_2407_, v___y_2408_);
lean_dec_ref(v___y_2408_);
lean_dec_ref(v_as_2404_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(lean_object* v_v_2413_){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = l_Lean_Lsp_instToJsonCallHierarchyPrepareParams_toJson(v_v_2413_);
v___x_2415_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(lean_object* v_h_2416_, lean_object* v_r_2417_){
_start:
{
lean_object* v_id_2419_; lean_object* v_method_2420_; lean_object* v_param_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2441_; 
v_id_2419_ = lean_ctor_get(v_r_2417_, 0);
v_method_2420_ = lean_ctor_get(v_r_2417_, 1);
v_param_2421_ = lean_ctor_get(v_r_2417_, 2);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_r_2417_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2423_ = v_r_2417_;
v_isShared_2424_ = v_isSharedCheck_2441_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_param_2421_);
lean_inc(v_method_2420_);
lean_inc(v_id_2419_);
lean_dec(v_r_2417_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2441_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___y_2426_; lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0_spec__1(v_param_2421_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v___x_2432_; 
lean_dec_ref(v___x_2431_);
v___x_2432_ = lean_box(0);
v___y_2426_ = v___x_2432_;
goto v___jp_2425_;
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
v_a_2433_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2431_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2431_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
v___y_2426_ = v___x_2438_;
goto v___jp_2425_;
}
}
}
v___jp_2425_:
{
lean_object* v___x_2428_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 2, v___y_2426_);
v___x_2428_ = v___x_2423_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_id_2419_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_method_2420_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v___y_2426_);
v___x_2428_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_IO_FS_Stream_writeLspMessage(v_h_2416_, v___x_2428_);
return v___x_2429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0___boxed(lean_object* v_h_2442_, lean_object* v_r_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_h_2442_, v_r_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(lean_object* v_r_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v___x_2449_; lean_object* v_a_2450_; lean_object* v___x_2451_; 
v___x_2449_ = l_Lean_Lsp_Ipc_stdin(v_a_2447_);
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref(v___x_2449_);
v___x_2451_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0_spec__0(v_a_2450_, v_r_2446_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0___boxed(lean_object* v_r_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v_r_2452_, v_a_2453_);
lean_dec_ref(v_a_2453_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(lean_object* v_requestNo_2459_, lean_object* v_uri_2460_, lean_object* v_pos_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_inc(v_requestNo_2459_);
v___x_2464_ = l_Lean_JsonNumber_fromNat(v_requestNo_2459_);
v___x_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
v___x_2466_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v_uri_2460_);
lean_ctor_set(v___x_2467_, 1, v_pos_2461_);
lean_inc_ref(v___x_2465_);
v___x_2468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2465_);
lean_ctor_set(v___x_2468_, 1, v___x_2466_);
lean_ctor_set(v___x_2468_, 2, v___x_2467_);
v___x_2469_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2468_, v_a_2462_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v___x_2470_; 
lean_dec_ref(v___x_2469_);
v___x_2470_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2465_, v_a_2462_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v_result_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2514_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref(v___x_2470_);
v_result_2472_ = lean_ctor_get(v_a_2471_, 1);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_a_2471_);
if (v_isSharedCheck_2514_ == 0)
{
lean_object* v_unused_2515_; 
v_unused_2515_ = lean_ctor_get(v_a_2471_, 0);
lean_dec(v_unused_2515_);
v___x_2474_ = v_a_2471_;
v_isShared_2475_ = v_isSharedCheck_2514_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_result_2472_);
lean_dec(v_a_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2514_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___y_2479_; 
v___x_2476_ = lean_unsigned_to_nat(1u);
v___x_2477_ = lean_nat_add(v_requestNo_2459_, v___x_2476_);
lean_dec(v_requestNo_2459_);
if (lean_obj_tag(v_result_2472_) == 0)
{
lean_object* v___x_2512_; 
v___x_2512_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_2479_ = v___x_2512_;
goto v___jp_2478_;
}
else
{
lean_object* v_val_2513_; 
v_val_2513_ = lean_ctor_get(v_result_2472_, 0);
lean_inc(v_val_2513_);
lean_dec_ref(v_result_2472_);
v___y_2479_ = v_val_2513_;
goto v___jp_2478_;
}
v___jp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
v___x_2480_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 1, v___x_2480_);
lean_ctor_set(v___x_2474_, 0, v___x_2477_);
v___x_2482_ = v___x_2474_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2480_);
v___x_2482_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
size_t v_sz_2483_; size_t v___x_2484_; lean_object* v___x_2485_; 
v_sz_2483_ = lean_array_size(v___y_2479_);
v___x_2484_ = ((size_t)0ULL);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__2(v___y_2479_, v_sz_2483_, v___x_2484_, v___x_2482_, v_a_2462_);
lean_dec_ref(v___y_2479_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2502_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2502_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2502_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v_fst_2490_; lean_object* v_snd_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2501_; 
v_fst_2490_ = lean_ctor_get(v_a_2486_, 0);
v_snd_2491_ = lean_ctor_get(v_a_2486_, 1);
v_isSharedCheck_2501_ = !lean_is_exclusive(v_a_2486_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2493_ = v_a_2486_;
v_isShared_2494_ = v_isSharedCheck_2501_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_snd_2491_);
lean_inc(v_fst_2490_);
lean_dec(v_a_2486_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2501_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 1, v_fst_2490_);
lean_ctor_set(v___x_2493_, 0, v_snd_2491_);
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_snd_2491_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_fst_2490_);
v___x_2496_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2498_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v___x_2496_);
v___x_2498_ = v___x_2488_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
v_a_2503_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2485_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2485_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_requestNo_2459_);
v_a_2516_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2470_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2470_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v___x_2465_);
lean_dec(v_requestNo_2459_);
v_a_2524_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2469_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2469_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___boxed(lean_object* v_requestNo_2532_, lean_object* v_uri_2533_, lean_object* v_pos_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Lsp_Ipc_expandIncomingCallHierarchy(v_requestNo_2532_, v_uri_2533_, v_pos_2534_, v_a_2535_);
lean_dec_ref(v_a_2535_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(size_t v_sz_2538_, size_t v_i_2539_, lean_object* v_bs_2540_){
_start:
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_usize_dec_lt(v_i_2539_, v_sz_2538_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2542_, 0, v_bs_2540_);
return v___x_2542_;
}
else
{
lean_object* v_v_2543_; lean_object* v___x_2544_; 
v_v_2543_ = lean_array_uget_borrowed(v_bs_2540_, v_i_2539_);
lean_inc(v_v_2543_);
v___x_2544_ = l_Lean_Lsp_instFromJsonCallHierarchyOutgoingCall_fromJson(v_v_2543_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v_bs_2540_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2554_; lean_object* v_bs_x27_2555_; size_t v___x_2556_; size_t v___x_2557_; lean_object* v___x_2558_; 
v_a_2553_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2544_);
v___x_2554_ = lean_unsigned_to_nat(0u);
v_bs_x27_2555_ = lean_array_uset(v_bs_2540_, v_i_2539_, v___x_2554_);
v___x_2556_ = ((size_t)1ULL);
v___x_2557_ = lean_usize_add(v_i_2539_, v___x_2556_);
v___x_2558_ = lean_array_uset(v_bs_x27_2555_, v_i_2539_, v_a_2553_);
v_i_2539_ = v___x_2557_;
v_bs_2540_ = v___x_2558_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2560_, lean_object* v_i_2561_, lean_object* v_bs_2562_){
_start:
{
size_t v_sz_boxed_2563_; size_t v_i_boxed_2564_; lean_object* v_res_2565_; 
v_sz_boxed_2563_ = lean_unbox_usize(v_sz_2560_);
lean_dec(v_sz_2560_);
v_i_boxed_2564_ = lean_unbox_usize(v_i_2561_);
lean_dec(v_i_2561_);
v_res_2565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_boxed_2563_, v_i_boxed_2564_, v_bs_2562_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(lean_object* v_x_2566_){
_start:
{
if (lean_obj_tag(v_x_2566_) == 4)
{
lean_object* v_elems_2567_; size_t v_sz_2568_; size_t v___x_2569_; lean_object* v___x_2570_; 
v_elems_2567_ = lean_ctor_get(v_x_2566_, 0);
lean_inc_ref(v_elems_2567_);
lean_dec_ref(v_x_2566_);
v_sz_2568_ = lean_array_size(v_elems_2567_);
v___x_2569_ = ((size_t)0ULL);
v___x_2570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4_spec__6(v_sz_2568_, v___x_2569_, v_elems_2567_);
return v___x_2570_;
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2571_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_2572_ = lean_unsigned_to_nat(80u);
v___x_2573_ = l_Lean_Json_pretty(v_x_2566_, v___x_2572_);
v___x_2574_ = lean_string_append(v___x_2571_, v___x_2573_);
lean_dec_ref(v___x_2573_);
v___x_2575_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2576_ = lean_string_append(v___x_2574_, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
return v___x_2577_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(lean_object* v_x_2580_){
_start:
{
if (lean_obj_tag(v_x_2580_) == 0)
{
lean_object* v___x_2581_; 
v___x_2581_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2___closed__0));
return v___x_2581_;
}
else
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2_spec__4(v_x_2580_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2599_; 
v_a_2591_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2593_ = v___x_2582_;
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2582_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2595_, 0, v_a_2591_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2595_);
v___x_2597_ = v___x_2593_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(lean_object* v_expectedID_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_Lsp_Ipc_stdout(v_a_2601_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2747_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2747_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2747_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_IO_FS_Stream_readLspMessage(v_a_2604_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2738_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2738_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2738_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___y_2614_; lean_object* v___y_2615_; 
switch(lean_obj_tag(v_a_2609_))
{
case 2:
{
lean_object* v_id_2621_; lean_object* v_result_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2666_; 
v_id_2621_ = lean_ctor_get(v_a_2609_, 0);
v_result_2622_ = lean_ctor_get(v_a_2609_, 1);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_a_2609_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2624_ = v_a_2609_;
v_isShared_2625_ = v_isSharedCheck_2666_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_result_2622_);
lean_inc(v_id_2621_);
lean_dec(v_a_2609_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2666_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
uint8_t v___x_2626_; 
v___x_2626_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_2621_, v_expectedID_2600_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; lean_object* v___y_2629_; 
lean_del_object(v___x_2624_);
lean_dec(v_result_2622_);
lean_del_object(v___x_2606_);
v___x_2627_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_2600_))
{
case 0:
{
lean_object* v_s_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_s_2640_ = lean_ctor_get(v_expectedID_2600_, 0);
lean_inc_ref(v_s_2640_);
lean_dec_ref(v_expectedID_2600_);
v___x_2641_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2642_ = lean_string_append(v___x_2641_, v_s_2640_);
lean_dec_ref(v_s_2640_);
v___x_2643_ = lean_string_append(v___x_2642_, v___x_2641_);
v___y_2629_ = v___x_2643_;
goto v___jp_2628_;
}
case 1:
{
lean_object* v_n_2644_; lean_object* v___x_2645_; 
v_n_2644_ = lean_ctor_get(v_expectedID_2600_, 0);
lean_inc_ref(v_n_2644_);
lean_dec_ref(v_expectedID_2600_);
v___x_2645_ = l_Lean_JsonNumber_toString(v_n_2644_);
v___y_2629_ = v___x_2645_;
goto v___jp_2628_;
}
default: 
{
lean_object* v___x_2646_; 
v___x_2646_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2629_ = v___x_2646_;
goto v___jp_2628_;
}
}
v___jp_2628_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2630_ = lean_string_append(v___x_2627_, v___y_2629_);
lean_dec_ref(v___y_2629_);
v___x_2631_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_2632_ = lean_string_append(v___x_2630_, v___x_2631_);
switch(lean_obj_tag(v_id_2621_))
{
case 0:
{
lean_object* v_s_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v_s_2633_ = lean_ctor_get(v_id_2621_, 0);
lean_inc_ref(v_s_2633_);
lean_dec_ref(v_id_2621_);
v___x_2634_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_2635_ = lean_string_append(v___x_2634_, v_s_2633_);
lean_dec_ref(v_s_2633_);
v___x_2636_ = lean_string_append(v___x_2635_, v___x_2634_);
v___y_2614_ = v___x_2632_;
v___y_2615_ = v___x_2636_;
goto v___jp_2613_;
}
case 1:
{
lean_object* v_n_2637_; lean_object* v___x_2638_; 
v_n_2637_ = lean_ctor_get(v_id_2621_, 0);
lean_inc_ref(v_n_2637_);
lean_dec_ref(v_id_2621_);
v___x_2638_ = l_Lean_JsonNumber_toString(v_n_2637_);
v___y_2614_ = v___x_2632_;
v___y_2615_ = v___x_2638_;
goto v___jp_2613_;
}
default: 
{
lean_object* v___x_2639_; 
v___x_2639_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_2614_ = v___x_2632_;
v___y_2615_ = v___x_2639_;
goto v___jp_2613_;
}
}
}
}
else
{
lean_object* v___x_2647_; 
lean_dec(v_id_2621_);
lean_del_object(v___x_2611_);
lean_inc(v_result_2622_);
v___x_2647_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1_spec__2(v_result_2622_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2657_; 
lean_del_object(v___x_2624_);
lean_dec(v_expectedID_2600_);
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2647_);
v___x_2649_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_2650_ = l_Lean_Json_compress(v_result_2622_);
v___x_2651_ = lean_string_append(v___x_2649_, v___x_2650_);
lean_dec_ref(v___x_2650_);
v___x_2652_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_2653_ = lean_string_append(v___x_2651_, v___x_2652_);
v___x_2654_ = lean_string_append(v___x_2653_, v_a_2648_);
lean_dec(v_a_2648_);
v___x_2655_ = lean_mk_io_user_error(v___x_2654_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set_tag(v___x_2606_, 1);
lean_ctor_set(v___x_2606_, 0, v___x_2655_);
v___x_2657_ = v___x_2606_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2655_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; 
lean_dec(v_result_2622_);
v_a_2659_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2647_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 0);
lean_ctor_set(v___x_2624_, 1, v_a_2659_);
lean_ctor_set(v___x_2624_, 0, v_expectedID_2600_);
v___x_2661_ = v___x_2624_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_expectedID_2600_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_a_2659_);
v___x_2661_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2663_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2661_);
v___x_2663_ = v___x_2606_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_2667_; uint8_t v_code_2668_; lean_object* v_message_2669_; lean_object* v_data_x3f_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___x_2702_; lean_object* v___y_2704_; 
lean_del_object(v___x_2611_);
lean_dec(v_expectedID_2600_);
v_id_2667_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_id_2667_);
v_code_2668_ = lean_ctor_get_uint8(v_a_2609_, sizeof(void*)*3);
v_message_2669_ = lean_ctor_get(v_a_2609_, 1);
lean_inc_ref(v_message_2669_);
v_data_x3f_2670_ = lean_ctor_get(v_a_2609_, 2);
lean_inc(v_data_x3f_2670_);
lean_dec_ref(v_a_2609_);
v___x_2671_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_2672_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_2702_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_2667_))
{
case 0:
{
lean_object* v_s_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
v_s_2720_ = lean_ctor_get(v_id_2667_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_id_2667_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v_id_2667_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_s_2720_);
lean_dec(v_id_2667_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set_tag(v___x_2722_, 3);
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_s_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
v___y_2704_ = v___x_2725_;
goto v___jp_2703_;
}
}
}
case 1:
{
lean_object* v_n_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
v_n_2728_ = lean_ctor_get(v_id_2667_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_id_2667_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v_id_2667_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_n_2728_);
lean_dec(v_id_2667_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set_tag(v___x_2730_, 2);
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_n_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
v___y_2704_ = v___x_2733_;
goto v___jp_2703_;
}
}
}
default: 
{
lean_object* v___x_2736_; 
v___x_2736_ = lean_box(0);
v___y_2704_ = v___x_2736_;
goto v___jp_2703_;
}
}
v___jp_2673_:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
lean_inc(v___y_2677_);
lean_inc_ref(v___y_2675_);
v___x_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___y_2675_);
lean_ctor_set(v___x_2678_, 1, v___y_2677_);
v___x_2679_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_2680_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2680_, 0, v_message_2669_);
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
v___x_2682_ = lean_box(0);
v___x_2683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2681_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2678_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_2686_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_2685_, v_data_x3f_2670_);
lean_dec(v_data_x3f_2670_);
v___x_2687_ = l_List_appendTR___redArg(v___x_2684_, v___x_2686_);
v___x_2688_ = l_Lean_Json_mkObj(v___x_2687_);
lean_dec(v___x_2687_);
lean_inc_ref(v___y_2676_);
v___x_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___y_2676_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v___x_2682_);
v___x_2691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___y_2674_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2672_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = l_Lean_Json_mkObj(v___x_2692_);
lean_dec_ref(v___x_2692_);
v___x_2694_ = l_Lean_Json_compress(v___x_2693_);
v___x_2695_ = lean_string_append(v___x_2671_, v___x_2694_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_2697_ = lean_string_append(v___x_2695_, v___x_2696_);
v___x_2698_ = lean_mk_io_user_error(v___x_2697_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set_tag(v___x_2606_, 1);
lean_ctor_set(v___x_2606_, 0, v___x_2698_);
v___x_2700_ = v___x_2606_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
v___jp_2703_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2702_);
lean_ctor_set(v___x_2705_, 1, v___y_2704_);
v___x_2706_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_2707_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_2668_)
{
case 0:
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2708_;
goto v___jp_2673_;
}
case 1:
{
lean_object* v___x_2709_; 
v___x_2709_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2709_;
goto v___jp_2673_;
}
case 2:
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2710_;
goto v___jp_2673_;
}
case 3:
{
lean_object* v___x_2711_; 
v___x_2711_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2711_;
goto v___jp_2673_;
}
case 4:
{
lean_object* v___x_2712_; 
v___x_2712_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2712_;
goto v___jp_2673_;
}
case 5:
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2713_;
goto v___jp_2673_;
}
case 6:
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2714_;
goto v___jp_2673_;
}
case 7:
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2715_;
goto v___jp_2673_;
}
case 8:
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2716_;
goto v___jp_2673_;
}
case 9:
{
lean_object* v___x_2717_; 
v___x_2717_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2717_;
goto v___jp_2673_;
}
case 10:
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2718_;
goto v___jp_2673_;
}
default: 
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_2674_ = v___x_2705_;
v___y_2675_ = v___x_2707_;
v___y_2676_ = v___x_2706_;
v___y_2677_ = v___x_2719_;
goto v___jp_2673_;
}
}
}
}
default: 
{
lean_del_object(v___x_2611_);
lean_dec(v_a_2609_);
lean_del_object(v___x_2606_);
goto _start;
}
}
v___jp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
v___x_2616_ = lean_string_append(v___y_2614_, v___y_2615_);
lean_dec_ref(v___y_2615_);
v___x_2617_ = lean_mk_io_user_error(v___x_2616_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 1);
lean_ctor_set(v___x_2611_, 0, v___x_2617_);
v___x_2619_ = v___x_2611_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_del_object(v___x_2606_);
lean_dec(v_expectedID_2600_);
v_a_2739_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2608_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2608_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v_expectedID_2600_);
v_a_2748_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2603_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2603_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1___boxed(lean_object* v_expectedID_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v_expectedID_2756_, v_a_2757_);
lean_dec_ref(v_a_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(lean_object* v_v_2760_){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = l_Lean_Lsp_instToJsonCallHierarchyOutgoingCallsParams_toJson(v_v_2760_);
v___x_2762_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(lean_object* v_h_2763_, lean_object* v_r_2764_){
_start:
{
lean_object* v_id_2766_; lean_object* v_method_2767_; lean_object* v_param_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2788_; 
v_id_2766_ = lean_ctor_get(v_r_2764_, 0);
v_method_2767_ = lean_ctor_get(v_r_2764_, 1);
v_param_2768_ = lean_ctor_get(v_r_2764_, 2);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_r_2764_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2770_ = v_r_2764_;
v_isShared_2771_ = v_isSharedCheck_2788_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_param_2768_);
lean_inc(v_method_2767_);
lean_inc(v_id_2766_);
lean_dec(v_r_2764_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2788_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___y_2773_; lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0_spec__1(v_param_2768_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v___x_2779_; 
lean_dec_ref(v___x_2778_);
v___x_2779_ = lean_box(0);
v___y_2773_ = v___x_2779_;
goto v___jp_2772_;
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
v_a_2780_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2778_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2778_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
v___y_2773_ = v___x_2785_;
goto v___jp_2772_;
}
}
}
v___jp_2772_:
{
lean_object* v___x_2775_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 2, v___y_2773_);
v___x_2775_ = v___x_2770_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_id_2766_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_method_2767_);
lean_ctor_set(v_reuseFailAlloc_2777_, 2, v___y_2773_);
v___x_2775_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_IO_FS_Stream_writeLspMessage(v_h_2763_, v___x_2775_);
return v___x_2776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0___boxed(lean_object* v_h_2789_, lean_object* v_r_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_h_2789_, v_r_2790_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(lean_object* v_r_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v___x_2796_; lean_object* v_a_2797_; lean_object* v___x_2798_; 
v___x_2796_ = l_Lean_Lsp_Ipc_stdin(v_a_2794_);
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2796_);
v___x_2798_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0_spec__0(v_a_2797_, v_r_2793_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0___boxed(lean_object* v_r_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v_r_2799_, v_a_2800_);
lean_dec_ref(v_a_2800_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(lean_object* v_requestNo_2806_, lean_object* v_item_2807_, lean_object* v_fromRanges_2808_, lean_object* v_visited_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_name_2812_; uint8_t v___x_2813_; 
v_name_2812_ = lean_ctor_get(v_item_2807_, 0);
v___x_2813_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_2812_, v_visited_2809_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_inc(v_requestNo_2806_);
v___x_2814_ = l_Lean_JsonNumber_fromNat(v_requestNo_2806_);
v___x_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
v___x_2816_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__0));
lean_inc_ref(v_item_2807_);
lean_inc_ref(v___x_2815_);
v___x_2817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
lean_ctor_set(v___x_2817_, 2, v_item_2807_);
v___x_2818_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__0(v___x_2817_, v_a_2810_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v___x_2819_; 
lean_dec_ref(v___x_2818_);
v___x_2819_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__1(v___x_2815_, v_a_2810_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2857_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref(v___x_2819_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_box(0);
lean_inc_ref(v_name_2812_);
v___x_2864_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_2812_, v___x_2863_, v_visited_2809_);
v___y_2857_ = v___x_2864_;
goto v___jp_2856_;
}
else
{
v___y_2857_ = v_visited_2809_;
goto v___jp_2856_;
}
v___jp_2821_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; size_t v_sz_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2825_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___y_2823_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v_sz_2827_ = lean_array_size(v___y_2824_);
v___x_2828_ = ((size_t)0ULL);
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___y_2822_, v___y_2824_, v_sz_2827_, v___x_2828_, v___x_2826_, v_a_2810_);
lean_dec_ref(v___y_2824_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2847_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2847_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2847_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v_fst_2834_; lean_object* v_snd_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2846_; 
v_fst_2834_ = lean_ctor_get(v_a_2830_, 0);
v_snd_2835_ = lean_ctor_get(v_a_2830_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_a_2830_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2837_ = v_a_2830_;
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_snd_2835_);
lean_inc(v_fst_2834_);
lean_dec(v_a_2830_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2839_, 0, v_item_2807_);
lean_ctor_set(v___x_2839_, 1, v_fromRanges_2808_);
lean_ctor_set(v___x_2839_, 2, v_snd_2835_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v_fst_2834_);
lean_ctor_set(v___x_2837_, 0, v___x_2839_);
v___x_2841_ = v___x_2837_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_fst_2834_);
v___x_2841_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2843_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v___x_2841_);
v___x_2843_ = v___x_2832_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v_fromRanges_2808_);
lean_dec_ref(v_item_2807_);
v_a_2848_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2829_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2829_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
v___jp_2856_:
{
lean_object* v_result_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_result_2858_ = lean_ctor_get(v_a_2820_, 1);
lean_inc(v_result_2858_);
lean_dec(v_a_2820_);
v___x_2859_ = lean_unsigned_to_nat(1u);
v___x_2860_ = lean_nat_add(v_requestNo_2806_, v___x_2859_);
lean_dec(v_requestNo_2806_);
if (lean_obj_tag(v_result_2858_) == 0)
{
lean_object* v___x_2861_; 
v___x_2861_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___closed__1));
v___y_2822_ = v___y_2857_;
v___y_2823_ = v___x_2860_;
v___y_2824_ = v___x_2861_;
goto v___jp_2821_;
}
else
{
lean_object* v_val_2862_; 
v_val_2862_ = lean_ctor_get(v_result_2858_, 0);
lean_inc(v_val_2862_);
lean_dec_ref(v_result_2858_);
v___y_2822_ = v___y_2857_;
v___y_2823_ = v___x_2860_;
v___y_2824_ = v_val_2862_;
goto v___jp_2821_;
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_visited_2809_);
lean_dec_ref(v_fromRanges_2808_);
lean_dec_ref(v_item_2807_);
lean_dec(v_requestNo_2806_);
v_a_2865_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2819_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2819_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec_ref(v___x_2815_);
lean_dec(v_visited_2809_);
lean_dec_ref(v_fromRanges_2808_);
lean_dec_ref(v_item_2807_);
lean_dec(v_requestNo_2806_);
v_a_2873_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2818_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2818_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec(v_visited_2809_);
lean_dec_ref(v_fromRanges_2808_);
v___x_2881_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2882_, 0, v_item_2807_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
lean_ctor_set(v___x_2882_, 2, v___x_2881_);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
lean_ctor_set(v___x_2883_, 1, v_requestNo_2806_);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(lean_object* v___x_2885_, lean_object* v_as_2886_, size_t v_sz_2887_, size_t v_i_2888_, lean_object* v_b_2889_, lean_object* v___y_2890_){
_start:
{
uint8_t v___x_2892_; 
v___x_2892_ = lean_usize_dec_lt(v_i_2888_, v_sz_2887_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; 
lean_dec(v___x_2885_);
v___x_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2893_, 0, v_b_2889_);
return v___x_2893_;
}
else
{
lean_object* v_fst_2894_; lean_object* v_snd_2895_; lean_object* v_a_2896_; lean_object* v_to_2897_; lean_object* v_fromRanges_2898_; lean_object* v___x_2899_; 
v_fst_2894_ = lean_ctor_get(v_b_2889_, 0);
lean_inc(v_fst_2894_);
v_snd_2895_ = lean_ctor_get(v_b_2889_, 1);
lean_inc(v_snd_2895_);
lean_dec_ref(v_b_2889_);
v_a_2896_ = lean_array_uget_borrowed(v_as_2886_, v_i_2888_);
v_to_2897_ = lean_ctor_get(v_a_2896_, 0);
v_fromRanges_2898_ = lean_ctor_get(v_a_2896_, 1);
lean_inc(v___x_2885_);
lean_inc_ref(v_fromRanges_2898_);
lean_inc_ref(v_to_2897_);
v___x_2899_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2894_, v_to_2897_, v_fromRanges_2898_, v___x_2885_, v___y_2890_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v_fst_2901_; lean_object* v_snd_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2913_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref(v___x_2899_);
v_fst_2901_ = lean_ctor_get(v_a_2900_, 0);
v_snd_2902_ = lean_ctor_get(v_a_2900_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_a_2900_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2904_ = v_a_2900_;
v_isShared_2905_ = v_isSharedCheck_2913_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_snd_2902_);
lean_inc(v_fst_2901_);
lean_dec(v_a_2900_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2913_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2906_ = lean_array_push(v_snd_2895_, v_fst_2901_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 1, v___x_2906_);
lean_ctor_set(v___x_2904_, 0, v_snd_2902_);
v___x_2908_ = v___x_2904_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_snd_2902_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
size_t v___x_2909_; size_t v___x_2910_; 
v___x_2909_ = ((size_t)1ULL);
v___x_2910_ = lean_usize_add(v_i_2888_, v___x_2909_);
v_i_2888_ = v___x_2910_;
v_b_2889_ = v___x_2908_;
goto _start;
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v_snd_2895_);
lean_dec(v___x_2885_);
v_a_2914_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2899_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2899_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2___boxed(lean_object* v___x_2922_, lean_object* v_as_2923_, lean_object* v_sz_2924_, lean_object* v_i_2925_, lean_object* v_b_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
size_t v_sz_boxed_2929_; size_t v_i_boxed_2930_; lean_object* v_res_2931_; 
v_sz_boxed_2929_ = lean_unbox_usize(v_sz_2924_);
lean_dec(v_sz_2924_);
v_i_boxed_2930_ = lean_unbox_usize(v_i_2925_);
lean_dec(v_i_2925_);
v_res_2931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go_spec__2(v___x_2922_, v_as_2923_, v_sz_boxed_2929_, v_i_boxed_2930_, v_b_2926_, v___y_2927_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v_as_2923_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go___boxed(lean_object* v_requestNo_2932_, lean_object* v_item_2933_, lean_object* v_fromRanges_2934_, lean_object* v_visited_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_requestNo_2932_, v_item_2933_, v_fromRanges_2934_, v_visited_2935_, v_a_2936_);
lean_dec_ref(v_a_2936_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(lean_object* v_as_2939_, size_t v_sz_2940_, size_t v_i_2941_, lean_object* v_b_2942_, lean_object* v___y_2943_){
_start:
{
uint8_t v___x_2945_; 
v___x_2945_ = lean_usize_dec_lt(v_i_2941_, v_sz_2940_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v_b_2942_);
return v___x_2946_;
}
else
{
lean_object* v_fst_2947_; lean_object* v_snd_2948_; lean_object* v_a_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_fst_2947_ = lean_ctor_get(v_b_2942_, 0);
lean_inc(v_fst_2947_);
v_snd_2948_ = lean_ctor_get(v_b_2942_, 1);
lean_inc(v_snd_2948_);
lean_dec_ref(v_b_2942_);
v_a_2949_ = lean_array_uget_borrowed(v_as_2939_, v_i_2941_);
v___x_2950_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__3));
v___x_2951_ = lean_box(1);
lean_inc(v_a_2949_);
v___x_2952_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandOutgoingCallHierarchy_go(v_fst_2947_, v_a_2949_, v___x_2950_, v___x_2951_, v___y_2943_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v_fst_2954_; lean_object* v_snd_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2966_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref(v___x_2952_);
v_fst_2954_ = lean_ctor_get(v_a_2953_, 0);
v_snd_2955_ = lean_ctor_get(v_a_2953_, 1);
v_isSharedCheck_2966_ = !lean_is_exclusive(v_a_2953_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2957_ = v_a_2953_;
v_isShared_2958_ = v_isSharedCheck_2966_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_snd_2955_);
lean_inc(v_fst_2954_);
lean_dec(v_a_2953_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2966_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2959_ = lean_array_push(v_snd_2948_, v_fst_2954_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v___x_2959_);
lean_ctor_set(v___x_2957_, 0, v_snd_2955_);
v___x_2961_ = v___x_2957_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_snd_2955_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
size_t v___x_2962_; size_t v___x_2963_; 
v___x_2962_ = ((size_t)1ULL);
v___x_2963_ = lean_usize_add(v_i_2941_, v___x_2962_);
v_i_2941_ = v___x_2963_;
v_b_2942_ = v___x_2961_;
goto _start;
}
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_snd_2948_);
v_a_2967_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2952_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2952_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0___boxed(lean_object* v_as_2975_, lean_object* v_sz_2976_, lean_object* v_i_2977_, lean_object* v_b_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
size_t v_sz_boxed_2981_; size_t v_i_boxed_2982_; lean_object* v_res_2983_; 
v_sz_boxed_2981_ = lean_unbox_usize(v_sz_2976_);
lean_dec(v_sz_2976_);
v_i_boxed_2982_ = lean_unbox_usize(v_i_2977_);
lean_dec(v_i_2977_);
v_res_2983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v_as_2975_, v_sz_boxed_2981_, v_i_boxed_2982_, v_b_2978_, v___y_2979_);
lean_dec_ref(v___y_2979_);
lean_dec_ref(v_as_2975_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(lean_object* v_requestNo_2984_, lean_object* v_uri_2985_, lean_object* v_pos_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
lean_inc(v_requestNo_2984_);
v___x_2989_ = l_Lean_JsonNumber_fromNat(v_requestNo_2984_);
v___x_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
v___x_2991_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__0));
v___x_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2992_, 0, v_uri_2985_);
lean_ctor_set(v___x_2992_, 1, v_pos_2986_);
lean_inc_ref(v___x_2990_);
v___x_2993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2990_);
lean_ctor_set(v___x_2993_, 1, v___x_2991_);
lean_ctor_set(v___x_2993_, 2, v___x_2992_);
v___x_2994_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__0(v___x_2993_, v_a_2987_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v___x_2995_; 
lean_dec_ref(v___x_2994_);
v___x_2995_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandIncomingCallHierarchy_spec__1(v___x_2990_, v_a_2987_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v_result_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3039_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref(v___x_2995_);
v_result_2997_ = lean_ctor_get(v_a_2996_, 1);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_a_2996_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; 
v_unused_3040_ = lean_ctor_get(v_a_2996_, 0);
lean_dec(v_unused_3040_);
v___x_2999_ = v_a_2996_;
v_isShared_3000_ = v_isSharedCheck_3039_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_result_2997_);
lean_dec(v_a_2996_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3039_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___y_3004_; 
v___x_3001_ = lean_unsigned_to_nat(1u);
v___x_3002_ = lean_nat_add(v_requestNo_2984_, v___x_3001_);
lean_dec(v_requestNo_2984_);
if (lean_obj_tag(v_result_2997_) == 0)
{
lean_object* v___x_3037_; 
v___x_3037_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandIncomingCallHierarchy___closed__1));
v___y_3004_ = v___x_3037_;
goto v___jp_3003_;
}
else
{
lean_object* v_val_3038_; 
v_val_3038_ = lean_ctor_get(v_result_2997_, 0);
lean_inc(v_val_3038_);
lean_dec_ref(v_result_2997_);
v___y_3004_ = v_val_3038_;
goto v___jp_3003_;
}
v___jp_3003_:
{
lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3005_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go___closed__1));
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 1, v___x_3005_);
lean_ctor_set(v___x_2999_, 0, v___x_3002_);
v___x_3007_ = v___x_2999_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
size_t v_sz_3008_; size_t v___x_3009_; lean_object* v___x_3010_; 
v_sz_3008_ = lean_array_size(v___y_3004_);
v___x_3009_ = ((size_t)0ULL);
v___x_3010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Lsp_Ipc_expandOutgoingCallHierarchy_spec__0(v___y_3004_, v_sz_3008_, v___x_3009_, v___x_3007_, v_a_2987_);
lean_dec_ref(v___y_3004_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3027_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3013_ = v___x_3010_;
v_isShared_3014_ = v_isSharedCheck_3027_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3027_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v_fst_3015_; lean_object* v_snd_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3026_; 
v_fst_3015_ = lean_ctor_get(v_a_3011_, 0);
v_snd_3016_ = lean_ctor_get(v_a_3011_, 1);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_a_3011_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3018_ = v_a_3011_;
v_isShared_3019_ = v_isSharedCheck_3026_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_snd_3016_);
lean_inc(v_fst_3015_);
lean_dec(v_a_3011_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3026_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 1, v_fst_3015_);
lean_ctor_set(v___x_3018_, 0, v_snd_3016_);
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_snd_3016_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_fst_3015_);
v___x_3021_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3023_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___x_3021_);
v___x_3023_ = v___x_3013_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
v_a_3028_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3010_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3010_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec(v_requestNo_2984_);
v_a_3041_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_2995_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_2995_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec_ref(v___x_2990_);
lean_dec(v_requestNo_2984_);
v_a_3049_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_2994_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_2994_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy___boxed(lean_object* v_requestNo_3057_, lean_object* v_uri_3058_, lean_object* v_pos_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lean_Lsp_Ipc_expandOutgoingCallHierarchy(v_requestNo_3057_, v_uri_3058_, v_pos_3059_, v_a_3060_);
lean_dec_ref(v_a_3060_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(lean_object* v_j_3063_, lean_object* v_k_3064_){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = l_Lean_Json_getObjValD(v_j_3063_, v_k_3064_);
v___x_3066_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0___boxed(lean_object* v_j_3067_, lean_object* v_k_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_j_3067_, v_k_3068_);
lean_dec_ref(v_k_3068_);
return v_res_3069_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2(void){
_start:
{
uint8_t v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = 1;
v___x_3077_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__1));
v___x_3078_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3077_, v___x_3076_);
return v___x_3078_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__7));
v___x_3080_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__2);
v___x_3081_ = lean_string_append(v___x_3080_, v___x_3079_);
return v___x_3081_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3082_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__10);
v___x_3083_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3084_ = lean_string_append(v___x_3083_, v___x_3082_);
return v___x_3084_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5(void){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3086_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__4);
v___x_3087_ = lean_string_append(v___x_3086_, v___x_3085_);
return v___x_3087_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6(void){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21, &l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21_once, _init_l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__21);
v___x_3089_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__3);
v___x_3090_ = lean_string_append(v___x_3089_, v___x_3088_);
return v___x_3090_;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7(void){
_start:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__12));
v___x_3092_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__6);
v___x_3093_ = lean_string_append(v___x_3092_, v___x_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(lean_object* v_json_3094_){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
lean_inc(v_json_3094_);
v___x_3096_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__0(v_json_3094_, v___x_3095_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3106_; 
lean_dec(v_json_3094_);
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3106_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3106_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3101_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__5);
v___x_3102_ = lean_string_append(v___x_3101_, v_a_3097_);
lean_dec(v_a_3097_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3102_);
v___x_3104_ = v___x_3099_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
else
{
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec(v_json_3094_);
v_a_3107_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3096_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3096_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set_tag(v___x_3109_, 0);
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v_a_3115_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3115_);
lean_dec_ref(v___x_3096_);
v___x_3116_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3117_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_json_3094_, v___x_3116_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v_a_3115_);
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3120_ = v___x_3117_;
v_isShared_3121_ = v_isSharedCheck_3127_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3127_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3125_; 
v___x_3122_ = lean_obj_once(&l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7, &l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7_once, _init_l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson___closed__7);
v___x_3123_ = lean_string_append(v___x_3122_, v_a_3118_);
lean_dec(v_a_3118_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v___x_3123_);
v___x_3125_ = v___x_3120_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3123_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
else
{
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec(v_a_3115_);
v_a_3128_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3117_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3117_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set_tag(v___x_3130_, 0);
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
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3144_; 
v_a_3136_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3138_ = v___x_3117_;
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3117_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v_a_3115_);
lean_ctor_set(v___x_3140_, 1, v_a_3136_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3140_);
v___x_3142_ = v___x_3138_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(size_t v_sz_3145_, size_t v_i_3146_, lean_object* v_bs_3147_){
_start:
{
uint8_t v___x_3148_; 
v___x_3148_ = lean_usize_dec_lt(v_i_3146_, v_sz_3145_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; 
v___x_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3149_, 0, v_bs_3147_);
return v___x_3149_;
}
else
{
lean_object* v_v_3150_; lean_object* v___x_3151_; 
v_v_3150_ = lean_array_uget_borrowed(v_bs_3147_, v_i_3146_);
lean_inc(v_v_3150_);
v___x_3151_ = l_Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson(v_v_3150_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref(v_bs_3147_);
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3161_; lean_object* v_bs_x27_3162_; size_t v___x_3163_; size_t v___x_3164_; lean_object* v___x_3165_; 
v_a_3160_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___x_3151_);
v___x_3161_ = lean_unsigned_to_nat(0u);
v_bs_x27_3162_ = lean_array_uset(v_bs_3147_, v_i_3146_, v___x_3161_);
v___x_3163_ = ((size_t)1ULL);
v___x_3164_ = lean_usize_add(v_i_3146_, v___x_3163_);
v___x_3165_ = lean_array_uset(v_bs_x27_3162_, v_i_3146_, v_a_3160_);
v_i_3146_ = v___x_3164_;
v_bs_3147_ = v___x_3165_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(lean_object* v_x_3167_){
_start:
{
if (lean_obj_tag(v_x_3167_) == 4)
{
lean_object* v_elems_3168_; size_t v_sz_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v_elems_3168_ = lean_ctor_get(v_x_3167_, 0);
lean_inc_ref(v_elems_3168_);
lean_dec_ref(v_x_3167_);
v_sz_3169_ = lean_array_size(v_elems_3168_);
v___x_3170_ = ((size_t)0ULL);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_3169_, v___x_3170_, v_elems_3168_);
return v___x_3171_;
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3172_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3173_ = lean_unsigned_to_nat(80u);
v___x_3174_ = l_Lean_Json_pretty(v_x_3167_, v___x_3173_);
v___x_3175_ = lean_string_append(v___x_3172_, v___x_3174_);
lean_dec_ref(v___x_3174_);
v___x_3176_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3177_ = lean_string_append(v___x_3175_, v___x_3176_);
v___x_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
return v___x_3178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(lean_object* v_j_3179_, lean_object* v_k_3180_){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = l_Lean_Json_getObjValD(v_j_3179_, v_k_3180_);
v___x_3182_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1(v___x_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1___boxed(lean_object* v_j_3183_, lean_object* v_k_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1(v_j_3183_, v_k_3184_);
lean_dec_ref(v_k_3184_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_3186_, lean_object* v_i_3187_, lean_object* v_bs_3188_){
_start:
{
size_t v_sz_boxed_3189_; size_t v_i_boxed_3190_; lean_object* v_res_3191_; 
v_sz_boxed_3189_ = lean_unbox_usize(v_sz_3186_);
lean_dec(v_sz_3186_);
v_i_boxed_3190_ = lean_unbox_usize(v_i_3187_);
lean_dec(v_i_3187_);
v_res_3191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonModuleHierarchy_fromJson_spec__1_spec__1_spec__2(v_sz_boxed_3189_, v_i_boxed_3190_, v_bs_3188_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(lean_object* v_x_3194_){
_start:
{
lean_object* v_item_3195_; lean_object* v_children_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3216_; 
v_item_3195_ = lean_ctor_get(v_x_3194_, 0);
v_children_3196_ = lean_ctor_get(v_x_3194_, 1);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_x_3194_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3198_ = v_x_3194_;
v_isShared_3199_ = v_isSharedCheck_3216_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_children_3196_);
lean_inc(v_item_3195_);
lean_dec(v_x_3194_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3216_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3203_; 
v___x_3200_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__0));
v___x_3201_ = l_Lean_Lsp_instToJsonLeanImport_toJson(v_item_3195_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 1, v___x_3201_);
lean_ctor_set(v___x_3198_, 0, v___x_3200_);
v___x_3203_ = v___x_3198_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3204_ = lean_box(0);
v___x_3205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3203_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = ((lean_object*)(l_Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson___closed__19));
v___x_3207_ = l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(v_children_3196_);
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3206_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v___x_3204_);
v___x_3210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v___x_3204_);
v___x_3211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3205_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = ((lean_object*)(l_Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson___closed__0));
v___x_3213_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_Ipc_instToJsonCallHierarchy_toJson_spec__2(v___x_3211_, v___x_3212_);
v___x_3214_ = l_Lean_Json_mkObj(v___x_3213_);
lean_dec(v___x_3213_);
return v___x_3214_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(size_t v_sz_3217_, size_t v_i_3218_, lean_object* v_bs_3219_){
_start:
{
uint8_t v___x_3220_; 
v___x_3220_ = lean_usize_dec_lt(v_i_3218_, v_sz_3217_);
if (v___x_3220_ == 0)
{
return v_bs_3219_;
}
else
{
lean_object* v_v_3221_; lean_object* v___x_3222_; lean_object* v_bs_x27_3223_; lean_object* v___x_3224_; size_t v___x_3225_; size_t v___x_3226_; lean_object* v___x_3227_; 
v_v_3221_ = lean_array_uget(v_bs_3219_, v_i_3218_);
v___x_3222_ = lean_unsigned_to_nat(0u);
v_bs_x27_3223_ = lean_array_uset(v_bs_3219_, v_i_3218_, v___x_3222_);
v___x_3224_ = l_Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson(v_v_3221_);
v___x_3225_ = ((size_t)1ULL);
v___x_3226_ = lean_usize_add(v_i_3218_, v___x_3225_);
v___x_3227_ = lean_array_uset(v_bs_x27_3223_, v_i_3218_, v___x_3224_);
v_i_3218_ = v___x_3226_;
v_bs_3219_ = v___x_3227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0(lean_object* v_a_3229_){
_start:
{
size_t v_sz_3230_; size_t v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_sz_3230_ = lean_array_size(v_a_3229_);
v___x_3231_ = ((size_t)0ULL);
v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_3230_, v___x_3231_, v_a_3229_);
v___x_3233_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0___boxed(lean_object* v_sz_3234_, lean_object* v_i_3235_, lean_object* v_bs_3236_){
_start:
{
size_t v_sz_boxed_3237_; size_t v_i_boxed_3238_; lean_object* v_res_3239_; 
v_sz_boxed_3237_ = lean_unbox_usize(v_sz_3234_);
lean_dec(v_sz_3234_);
v_i_boxed_3238_ = lean_unbox_usize(v_i_3235_);
lean_dec(v_i_3235_);
v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_Ipc_instToJsonModuleHierarchy_toJson_spec__0_spec__0(v_sz_boxed_3237_, v_i_boxed_3238_, v_bs_3236_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(size_t v_sz_3242_, size_t v_i_3243_, lean_object* v_bs_3244_){
_start:
{
uint8_t v___x_3245_; 
v___x_3245_ = lean_usize_dec_lt(v_i_3243_, v_sz_3242_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3246_, 0, v_bs_3244_);
return v___x_3246_;
}
else
{
lean_object* v_v_3247_; lean_object* v___x_3248_; 
v_v_3247_ = lean_array_uget_borrowed(v_bs_3244_, v_i_3243_);
lean_inc(v_v_3247_);
v___x_3248_ = l_Lean_Lsp_instFromJsonLeanImport_fromJson(v_v_3247_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec_ref(v_bs_3244_);
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3248_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3258_; lean_object* v_bs_x27_3259_; size_t v___x_3260_; size_t v___x_3261_; lean_object* v___x_3262_; 
v_a_3257_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3257_);
lean_dec_ref(v___x_3248_);
v___x_3258_ = lean_unsigned_to_nat(0u);
v_bs_x27_3259_ = lean_array_uset(v_bs_3244_, v_i_3243_, v___x_3258_);
v___x_3260_ = ((size_t)1ULL);
v___x_3261_ = lean_usize_add(v_i_3243_, v___x_3260_);
v___x_3262_ = lean_array_uset(v_bs_x27_3259_, v_i_3243_, v_a_3257_);
v_i_3243_ = v___x_3261_;
v_bs_3244_ = v___x_3262_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4___boxed(lean_object* v_sz_3264_, lean_object* v_i_3265_, lean_object* v_bs_3266_){
_start:
{
size_t v_sz_boxed_3267_; size_t v_i_boxed_3268_; lean_object* v_res_3269_; 
v_sz_boxed_3267_ = lean_unbox_usize(v_sz_3264_);
lean_dec(v_sz_3264_);
v_i_boxed_3268_ = lean_unbox_usize(v_i_3265_);
lean_dec(v_i_3265_);
v_res_3269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_boxed_3267_, v_i_boxed_3268_, v_bs_3266_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(lean_object* v_x_3270_){
_start:
{
if (lean_obj_tag(v_x_3270_) == 4)
{
lean_object* v_elems_3271_; size_t v_sz_3272_; size_t v___x_3273_; lean_object* v___x_3274_; 
v_elems_3271_ = lean_ctor_get(v_x_3270_, 0);
lean_inc_ref(v_elems_3271_);
lean_dec_ref(v_x_3270_);
v_sz_3272_ = lean_array_size(v_elems_3271_);
v___x_3273_ = ((size_t)0ULL);
v___x_3274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2_spec__4(v_sz_3272_, v___x_3273_, v_elems_3271_);
return v___x_3274_;
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3275_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_Ipc_instFromJsonCallHierarchy_fromJson_spec__1_spec__1___closed__0));
v___x_3276_ = lean_unsigned_to_nat(80u);
v___x_3277_ = l_Lean_Json_pretty(v_x_3270_, v___x_3276_);
v___x_3278_ = lean_string_append(v___x_3275_, v___x_3277_);
lean_dec_ref(v___x_3277_);
v___x_3279_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3280_ = lean_string_append(v___x_3278_, v___x_3279_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(lean_object* v_expectedID_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Lean_Lsp_Ipc_stdout(v_a_3283_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3429_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3429_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3429_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_IO_FS_Stream_readLspMessage(v_a_3286_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3420_; 
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3293_ = v___x_3290_;
v_isShared_3294_ = v_isSharedCheck_3420_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3290_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3420_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___y_3296_; lean_object* v___y_3297_; 
switch(lean_obj_tag(v_a_3291_))
{
case 2:
{
lean_object* v_id_3303_; lean_object* v_result_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3348_; 
v_id_3303_ = lean_ctor_get(v_a_3291_, 0);
v_result_3304_ = lean_ctor_get(v_a_3291_, 1);
v_isSharedCheck_3348_ = !lean_is_exclusive(v_a_3291_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3306_ = v_a_3291_;
v_isShared_3307_ = v_isSharedCheck_3348_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_result_3304_);
lean_inc(v_id_3303_);
lean_dec(v_a_3291_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3348_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
uint8_t v___x_3308_; 
v___x_3308_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3303_, v_expectedID_3282_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; lean_object* v___y_3311_; 
lean_del_object(v___x_3306_);
lean_dec(v_result_3304_);
lean_del_object(v___x_3288_);
v___x_3309_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3282_))
{
case 0:
{
lean_object* v_s_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v_s_3322_ = lean_ctor_get(v_expectedID_3282_, 0);
lean_inc_ref(v_s_3322_);
lean_dec_ref(v_expectedID_3282_);
v___x_3323_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3324_ = lean_string_append(v___x_3323_, v_s_3322_);
lean_dec_ref(v_s_3322_);
v___x_3325_ = lean_string_append(v___x_3324_, v___x_3323_);
v___y_3311_ = v___x_3325_;
goto v___jp_3310_;
}
case 1:
{
lean_object* v_n_3326_; lean_object* v___x_3327_; 
v_n_3326_ = lean_ctor_get(v_expectedID_3282_, 0);
lean_inc_ref(v_n_3326_);
lean_dec_ref(v_expectedID_3282_);
v___x_3327_ = l_Lean_JsonNumber_toString(v_n_3326_);
v___y_3311_ = v___x_3327_;
goto v___jp_3310_;
}
default: 
{
lean_object* v___x_3328_; 
v___x_3328_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3311_ = v___x_3328_;
goto v___jp_3310_;
}
}
v___jp_3310_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3312_ = lean_string_append(v___x_3309_, v___y_3311_);
lean_dec_ref(v___y_3311_);
v___x_3313_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3314_ = lean_string_append(v___x_3312_, v___x_3313_);
switch(lean_obj_tag(v_id_3303_))
{
case 0:
{
lean_object* v_s_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v_s_3315_ = lean_ctor_get(v_id_3303_, 0);
lean_inc_ref(v_s_3315_);
lean_dec_ref(v_id_3303_);
v___x_3316_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3317_ = lean_string_append(v___x_3316_, v_s_3315_);
lean_dec_ref(v_s_3315_);
v___x_3318_ = lean_string_append(v___x_3317_, v___x_3316_);
v___y_3296_ = v___x_3314_;
v___y_3297_ = v___x_3318_;
goto v___jp_3295_;
}
case 1:
{
lean_object* v_n_3319_; lean_object* v___x_3320_; 
v_n_3319_ = lean_ctor_get(v_id_3303_, 0);
lean_inc_ref(v_n_3319_);
lean_dec_ref(v_id_3303_);
v___x_3320_ = l_Lean_JsonNumber_toString(v_n_3319_);
v___y_3296_ = v___x_3314_;
v___y_3297_ = v___x_3320_;
goto v___jp_3295_;
}
default: 
{
lean_object* v___x_3321_; 
v___x_3321_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3296_ = v___x_3314_;
v___y_3297_ = v___x_3321_;
goto v___jp_3295_;
}
}
}
}
else
{
lean_object* v___x_3329_; 
lean_dec(v_id_3303_);
lean_del_object(v___x_3293_);
lean_inc(v_result_3304_);
v___x_3329_ = l_Array_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1_spec__2(v_result_3304_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
lean_del_object(v___x_3306_);
lean_dec(v_expectedID_3282_);
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref(v___x_3329_);
v___x_3331_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3332_ = l_Lean_Json_compress(v_result_3304_);
v___x_3333_ = lean_string_append(v___x_3331_, v___x_3332_);
lean_dec_ref(v___x_3332_);
v___x_3334_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3335_ = lean_string_append(v___x_3333_, v___x_3334_);
v___x_3336_ = lean_string_append(v___x_3335_, v_a_3330_);
lean_dec(v_a_3330_);
v___x_3337_ = lean_mk_io_user_error(v___x_3336_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set_tag(v___x_3288_, 1);
lean_ctor_set(v___x_3288_, 0, v___x_3337_);
v___x_3339_ = v___x_3288_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; 
lean_dec(v_result_3304_);
v_a_3341_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3341_);
lean_dec_ref(v___x_3329_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set_tag(v___x_3306_, 0);
lean_ctor_set(v___x_3306_, 1, v_a_3341_);
lean_ctor_set(v___x_3306_, 0, v_expectedID_3282_);
v___x_3343_ = v___x_3306_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_expectedID_3282_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v_a_3341_);
v___x_3343_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3345_; 
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v___x_3343_);
v___x_3345_ = v___x_3288_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3349_; uint8_t v_code_3350_; lean_object* v_message_3351_; lean_object* v_data_x3f_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___x_3384_; lean_object* v___y_3386_; 
lean_del_object(v___x_3293_);
lean_dec(v_expectedID_3282_);
v_id_3349_ = lean_ctor_get(v_a_3291_, 0);
lean_inc(v_id_3349_);
v_code_3350_ = lean_ctor_get_uint8(v_a_3291_, sizeof(void*)*3);
v_message_3351_ = lean_ctor_get(v_a_3291_, 1);
lean_inc_ref(v_message_3351_);
v_data_x3f_3352_ = lean_ctor_get(v_a_3291_, 2);
lean_inc(v_data_x3f_3352_);
lean_dec_ref(v_a_3291_);
v___x_3353_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3354_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3384_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3349_))
{
case 0:
{
lean_object* v_s_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
v_s_3402_ = lean_ctor_get(v_id_3349_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_id_3349_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v_id_3349_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_s_3402_);
lean_dec(v_id_3349_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set_tag(v___x_3404_, 3);
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_s_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
v___y_3386_ = v___x_3407_;
goto v___jp_3385_;
}
}
}
case 1:
{
lean_object* v_n_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
v_n_3410_ = lean_ctor_get(v_id_3349_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_id_3349_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v_id_3349_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_n_3410_);
lean_dec(v_id_3349_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
lean_ctor_set_tag(v___x_3412_, 2);
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_n_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
v___y_3386_ = v___x_3415_;
goto v___jp_3385_;
}
}
}
default: 
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_box(0);
v___y_3386_ = v___x_3418_;
goto v___jp_3385_;
}
}
v___jp_3355_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3382_; 
lean_inc(v___y_3359_);
lean_inc_ref(v___y_3357_);
v___x_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___y_3357_);
lean_ctor_set(v___x_3360_, 1, v___y_3359_);
v___x_3361_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3362_, 0, v_message_3351_);
v___x_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3361_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
v___x_3364_ = lean_box(0);
v___x_3365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3360_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3368_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3367_, v_data_x3f_3352_);
lean_dec(v_data_x3f_3352_);
v___x_3369_ = l_List_appendTR___redArg(v___x_3366_, v___x_3368_);
v___x_3370_ = l_Lean_Json_mkObj(v___x_3369_);
lean_dec(v___x_3369_);
lean_inc_ref(v___y_3358_);
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___y_3358_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
lean_ctor_set(v___x_3372_, 1, v___x_3364_);
v___x_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___y_3356_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
v___x_3374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3354_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = l_Lean_Json_mkObj(v___x_3374_);
lean_dec_ref(v___x_3374_);
v___x_3376_ = l_Lean_Json_compress(v___x_3375_);
v___x_3377_ = lean_string_append(v___x_3353_, v___x_3376_);
lean_dec_ref(v___x_3376_);
v___x_3378_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3379_ = lean_string_append(v___x_3377_, v___x_3378_);
v___x_3380_ = lean_mk_io_user_error(v___x_3379_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set_tag(v___x_3288_, 1);
lean_ctor_set(v___x_3288_, 0, v___x_3380_);
v___x_3382_ = v___x_3288_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
v___jp_3385_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3384_);
lean_ctor_set(v___x_3387_, 1, v___y_3386_);
v___x_3388_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3389_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3350_)
{
case 0:
{
lean_object* v___x_3390_; 
v___x_3390_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3390_;
goto v___jp_3355_;
}
case 1:
{
lean_object* v___x_3391_; 
v___x_3391_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3391_;
goto v___jp_3355_;
}
case 2:
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3392_;
goto v___jp_3355_;
}
case 3:
{
lean_object* v___x_3393_; 
v___x_3393_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3393_;
goto v___jp_3355_;
}
case 4:
{
lean_object* v___x_3394_; 
v___x_3394_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3394_;
goto v___jp_3355_;
}
case 5:
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3395_;
goto v___jp_3355_;
}
case 6:
{
lean_object* v___x_3396_; 
v___x_3396_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3396_;
goto v___jp_3355_;
}
case 7:
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3397_;
goto v___jp_3355_;
}
case 8:
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3398_;
goto v___jp_3355_;
}
case 9:
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3399_;
goto v___jp_3355_;
}
case 10:
{
lean_object* v___x_3400_; 
v___x_3400_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3400_;
goto v___jp_3355_;
}
default: 
{
lean_object* v___x_3401_; 
v___x_3401_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3356_ = v___x_3387_;
v___y_3357_ = v___x_3389_;
v___y_3358_ = v___x_3388_;
v___y_3359_ = v___x_3401_;
goto v___jp_3355_;
}
}
}
}
default: 
{
lean_del_object(v___x_3293_);
lean_dec(v_a_3291_);
lean_del_object(v___x_3288_);
goto _start;
}
}
v___jp_3295_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3301_; 
v___x_3298_ = lean_string_append(v___y_3296_, v___y_3297_);
lean_dec_ref(v___y_3297_);
v___x_3299_ = lean_mk_io_user_error(v___x_3298_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set_tag(v___x_3293_, 1);
lean_ctor_set(v___x_3293_, 0, v___x_3299_);
v___x_3301_ = v___x_3293_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3299_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_del_object(v___x_3288_);
lean_dec(v_expectedID_3282_);
v_a_3421_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3290_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3290_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v_expectedID_3282_);
v_a_3430_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3285_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3285_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1___boxed(lean_object* v_expectedID_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v_expectedID_3438_, v_a_3439_);
lean_dec_ref(v_a_3439_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(lean_object* v_v_3442_){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportsParams_toJson(v_v_3442_);
v___x_3444_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_v_3445_);
lean_dec_ref(v_v_3445_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(lean_object* v_h_3447_, lean_object* v_r_3448_){
_start:
{
lean_object* v_id_3450_; lean_object* v_method_3451_; lean_object* v_param_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3472_; 
v_id_3450_ = lean_ctor_get(v_r_3448_, 0);
v_method_3451_ = lean_ctor_get(v_r_3448_, 1);
v_param_3452_ = lean_ctor_get(v_r_3448_, 2);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_r_3448_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3454_ = v_r_3448_;
v_isShared_3455_ = v_isSharedCheck_3472_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_param_3452_);
lean_inc(v_method_3451_);
lean_inc(v_id_3450_);
lean_dec(v_r_3448_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3472_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___y_3457_; lean_object* v___x_3462_; 
v___x_3462_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0_spec__1(v_param_3452_);
lean_dec(v_param_3452_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v___x_3463_; 
lean_dec_ref(v___x_3462_);
v___x_3463_ = lean_box(0);
v___y_3457_ = v___x_3463_;
goto v___jp_3456_;
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
v_a_3464_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3462_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3462_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
v___y_3457_ = v___x_3469_;
goto v___jp_3456_;
}
}
}
v___jp_3456_:
{
lean_object* v___x_3459_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 2, v___y_3457_);
v___x_3459_ = v___x_3454_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_id_3450_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_method_3451_);
lean_ctor_set(v_reuseFailAlloc_3461_, 2, v___y_3457_);
v___x_3459_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_IO_FS_Stream_writeLspMessage(v_h_3447_, v___x_3459_);
return v___x_3460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0___boxed(lean_object* v_h_3473_, lean_object* v_r_3474_, lean_object* v_a_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_h_3473_, v_r_3474_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(lean_object* v_r_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v___x_3480_; lean_object* v_a_3481_; lean_object* v___x_3482_; 
v___x_3480_ = l_Lean_Lsp_Ipc_stdin(v_a_3478_);
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref(v___x_3480_);
v___x_3482_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0_spec__0(v_a_3481_, v_r_3477_);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0___boxed(lean_object* v_r_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v_r_3483_, v_a_3484_);
lean_dec_ref(v_a_3484_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(lean_object* v_requestNo_3490_, lean_object* v_item_3491_, lean_object* v_visited_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v_module_3495_; lean_object* v_name_3496_; uint8_t v___x_3497_; 
v_module_3495_ = lean_ctor_get(v_item_3491_, 0);
v_name_3496_ = lean_ctor_get(v_module_3495_, 0);
v___x_3497_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3496_, v_visited_3492_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_inc(v_requestNo_3490_);
v___x_3498_ = l_Lean_JsonNumber_fromNat(v_requestNo_3490_);
v___x_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
v___x_3500_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__0));
lean_inc_ref(v_module_3495_);
lean_inc_ref(v___x_3499_);
v___x_3501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3499_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
lean_ctor_set(v___x_3501_, 2, v_module_3495_);
v___x_3502_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__0(v___x_3501_, v_a_3493_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v___x_3503_; 
lean_dec_ref(v___x_3502_);
v___x_3503_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3499_, v_a_3493_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___y_3506_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___x_3503_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = lean_box(0);
lean_inc_ref(v_name_3496_);
v___x_3549_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3496_, v___x_3548_, v_visited_3492_);
v___y_3506_ = v___x_3549_;
goto v___jp_3505_;
}
else
{
v___y_3506_ = v_visited_3492_;
goto v___jp_3505_;
}
v___jp_3505_:
{
lean_object* v_result_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3546_; 
v_result_3507_ = lean_ctor_get(v_a_3504_, 1);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_a_3504_);
if (v_isSharedCheck_3546_ == 0)
{
lean_object* v_unused_3547_; 
v_unused_3547_ = lean_ctor_get(v_a_3504_, 0);
lean_dec(v_unused_3547_);
v___x_3509_ = v_a_3504_;
v_isShared_3510_ = v_isSharedCheck_3546_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_result_3507_);
lean_dec(v_a_3504_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3546_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3511_ = lean_unsigned_to_nat(1u);
v___x_3512_ = lean_nat_add(v_requestNo_3490_, v___x_3511_);
lean_dec(v_requestNo_3490_);
v___x_3513_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 1, v___x_3513_);
lean_ctor_set(v___x_3509_, 0, v___x_3512_);
v___x_3515_ = v___x_3509_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
size_t v_sz_3516_; size_t v___x_3517_; lean_object* v___x_3518_; 
v_sz_3516_ = lean_array_size(v_result_3507_);
v___x_3517_ = ((size_t)0ULL);
v___x_3518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___y_3506_, v_result_3507_, v_sz_3516_, v___x_3517_, v___x_3515_, v_a_3493_);
lean_dec(v_result_3507_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3536_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3536_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3536_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v_fst_3523_; lean_object* v_snd_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3535_; 
v_fst_3523_ = lean_ctor_get(v_a_3519_, 0);
v_snd_3524_ = lean_ctor_get(v_a_3519_, 1);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_a_3519_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3526_ = v_a_3519_;
v_isShared_3527_ = v_isSharedCheck_3535_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_snd_3524_);
lean_inc(v_fst_3523_);
lean_dec(v_a_3519_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3535_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; lean_object* v___x_3530_; 
v___x_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3528_, 0, v_item_3491_);
lean_ctor_set(v___x_3528_, 1, v_snd_3524_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 1, v_fst_3523_);
lean_ctor_set(v___x_3526_, 0, v___x_3528_);
v___x_3530_ = v___x_3526_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_fst_3523_);
v___x_3530_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3532_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3530_);
v___x_3532_ = v___x_3521_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v_item_3491_);
v_a_3537_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3518_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3518_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
lean_dec(v_visited_3492_);
lean_dec_ref(v_item_3491_);
lean_dec(v_requestNo_3490_);
v_a_3550_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3503_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3503_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec_ref(v___x_3499_);
lean_dec(v_visited_3492_);
lean_dec_ref(v_item_3491_);
lean_dec(v_requestNo_3490_);
v_a_3558_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3502_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3502_);
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
else
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
lean_dec(v_visited_3492_);
v___x_3566_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3567_, 0, v_item_3491_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
lean_ctor_set(v___x_3568_, 1, v_requestNo_3490_);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(lean_object* v___x_3570_, lean_object* v_as_3571_, size_t v_sz_3572_, size_t v_i_3573_, lean_object* v_b_3574_, lean_object* v___y_3575_){
_start:
{
uint8_t v___x_3577_; 
v___x_3577_ = lean_usize_dec_lt(v_i_3573_, v_sz_3572_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; 
lean_dec(v___x_3570_);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v_b_3574_);
return v___x_3578_;
}
else
{
lean_object* v_fst_3579_; lean_object* v_snd_3580_; lean_object* v_a_3581_; lean_object* v___x_3582_; 
v_fst_3579_ = lean_ctor_get(v_b_3574_, 0);
lean_inc(v_fst_3579_);
v_snd_3580_ = lean_ctor_get(v_b_3574_, 1);
lean_inc(v_snd_3580_);
lean_dec_ref(v_b_3574_);
v_a_3581_ = lean_array_uget_borrowed(v_as_3571_, v_i_3573_);
lean_inc(v___x_3570_);
lean_inc(v_a_3581_);
v___x_3582_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_fst_3579_, v_a_3581_, v___x_3570_, v___y_3575_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; lean_object* v_fst_3584_; lean_object* v_snd_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3596_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref(v___x_3582_);
v_fst_3584_ = lean_ctor_get(v_a_3583_, 0);
v_snd_3585_ = lean_ctor_get(v_a_3583_, 1);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_a_3583_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3587_ = v_a_3583_;
v_isShared_3588_ = v_isSharedCheck_3596_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_snd_3585_);
lean_inc(v_fst_3584_);
lean_dec(v_a_3583_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3596_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; lean_object* v___x_3591_; 
v___x_3589_ = lean_array_push(v_snd_3580_, v_fst_3584_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 1, v___x_3589_);
lean_ctor_set(v___x_3587_, 0, v_snd_3585_);
v___x_3591_ = v___x_3587_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_snd_3585_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
size_t v___x_3592_; size_t v___x_3593_; 
v___x_3592_ = ((size_t)1ULL);
v___x_3593_ = lean_usize_add(v_i_3573_, v___x_3592_);
v_i_3573_ = v___x_3593_;
v_b_3574_ = v___x_3591_;
goto _start;
}
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec(v_snd_3580_);
lean_dec(v___x_3570_);
v_a_3597_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3582_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3582_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2___boxed(lean_object* v___x_3605_, lean_object* v_as_3606_, lean_object* v_sz_3607_, lean_object* v_i_3608_, lean_object* v_b_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
size_t v_sz_boxed_3612_; size_t v_i_boxed_3613_; lean_object* v_res_3614_; 
v_sz_boxed_3612_ = lean_unbox_usize(v_sz_3607_);
lean_dec(v_sz_3607_);
v_i_boxed_3613_ = lean_unbox_usize(v_i_3608_);
lean_dec(v_i_3608_);
v_res_3614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__2(v___x_3605_, v_as_3606_, v_sz_boxed_3612_, v_i_boxed_3613_, v_b_3609_, v___y_3610_);
lean_dec_ref(v___y_3610_);
lean_dec_ref(v_as_3606_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___boxed(lean_object* v_requestNo_3615_, lean_object* v_item_3616_, lean_object* v_visited_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v_requestNo_3615_, v_item_3616_, v_visited_3617_, v_a_3618_);
lean_dec_ref(v_a_3618_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(lean_object* v_v_3621_){
_start:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3622_ = l_Lean_Lsp_instToJsonLeanPrepareModuleHierarchyParams_toJson(v_v_3621_);
v___x_3623_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(lean_object* v_h_3624_, lean_object* v_r_3625_){
_start:
{
lean_object* v_id_3627_; lean_object* v_method_3628_; lean_object* v_param_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3649_; 
v_id_3627_ = lean_ctor_get(v_r_3625_, 0);
v_method_3628_ = lean_ctor_get(v_r_3625_, 1);
v_param_3629_ = lean_ctor_get(v_r_3625_, 2);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_r_3625_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3631_ = v_r_3625_;
v_isShared_3632_ = v_isSharedCheck_3649_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_param_3629_);
lean_inc(v_method_3628_);
lean_inc(v_id_3627_);
lean_dec(v_r_3625_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3649_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___y_3634_; lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0_spec__1(v_param_3629_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v___x_3640_; 
lean_dec_ref(v___x_3639_);
v___x_3640_ = lean_box(0);
v___y_3634_ = v___x_3640_;
goto v___jp_3633_;
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
v_a_3641_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3639_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3639_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
v___y_3634_ = v___x_3646_;
goto v___jp_3633_;
}
}
}
v___jp_3633_:
{
lean_object* v___x_3636_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 2, v___y_3634_);
v___x_3636_ = v___x_3631_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_id_3627_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v_method_3628_);
lean_ctor_set(v_reuseFailAlloc_3638_, 2, v___y_3634_);
v___x_3636_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_IO_FS_Stream_writeLspMessage(v_h_3624_, v___x_3636_);
return v___x_3637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0___boxed(lean_object* v_h_3650_, lean_object* v_r_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_h_3650_, v_r_3651_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(lean_object* v_r_3654_, lean_object* v_a_3655_){
_start:
{
lean_object* v___x_3657_; lean_object* v_a_3658_; lean_object* v___x_3659_; 
v___x_3657_ = l_Lean_Lsp_Ipc_stdin(v_a_3655_);
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_a_3658_);
lean_dec_ref(v___x_3657_);
v___x_3659_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0_spec__0(v_a_3658_, v_r_3654_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0___boxed(lean_object* v_r_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v_r_3660_, v_a_3661_);
lean_dec_ref(v_a_3661_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(lean_object* v_x_3666_){
_start:
{
if (lean_obj_tag(v_x_3666_) == 0)
{
lean_object* v___x_3667_; 
v___x_3667_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2___closed__0));
return v___x_3667_;
}
else
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_Lsp_instFromJsonLeanModule_fromJson(v_x_3666_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3685_; 
v_a_3677_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3679_ = v___x_3668_;
v_isShared_3680_ = v_isSharedCheck_3685_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3668_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3685_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3681_, 0, v_a_3677_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 0, v___x_3681_);
v___x_3683_ = v___x_3679_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(lean_object* v_expectedID_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Lean_Lsp_Ipc_stdout(v_a_3687_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3833_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3833_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3833_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_IO_FS_Stream_readLspMessage(v_a_3690_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3824_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3697_ = v___x_3694_;
v_isShared_3698_ = v_isSharedCheck_3824_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3824_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___y_3700_; lean_object* v___y_3701_; 
switch(lean_obj_tag(v_a_3695_))
{
case 2:
{
lean_object* v_id_3707_; lean_object* v_result_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3752_; 
v_id_3707_ = lean_ctor_get(v_a_3695_, 0);
v_result_3708_ = lean_ctor_get(v_a_3695_, 1);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_a_3695_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3710_ = v_a_3695_;
v_isShared_3711_ = v_isSharedCheck_3752_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_result_3708_);
lean_inc(v_id_3707_);
lean_dec(v_a_3695_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3752_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
uint8_t v___x_3712_; 
v___x_3712_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3707_, v_expectedID_3686_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___y_3715_; 
lean_del_object(v___x_3710_);
lean_dec(v_result_3708_);
lean_del_object(v___x_3692_);
v___x_3713_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__6));
switch(lean_obj_tag(v_expectedID_3686_))
{
case 0:
{
lean_object* v_s_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v_s_3726_ = lean_ctor_get(v_expectedID_3686_, 0);
lean_inc_ref(v_s_3726_);
lean_dec_ref(v_expectedID_3686_);
v___x_3727_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3728_ = lean_string_append(v___x_3727_, v_s_3726_);
lean_dec_ref(v_s_3726_);
v___x_3729_ = lean_string_append(v___x_3728_, v___x_3727_);
v___y_3715_ = v___x_3729_;
goto v___jp_3714_;
}
case 1:
{
lean_object* v_n_3730_; lean_object* v___x_3731_; 
v_n_3730_ = lean_ctor_get(v_expectedID_3686_, 0);
lean_inc_ref(v_n_3730_);
lean_dec_ref(v_expectedID_3686_);
v___x_3731_ = l_Lean_JsonNumber_toString(v_n_3730_);
v___y_3715_ = v___x_3731_;
goto v___jp_3714_;
}
default: 
{
lean_object* v___x_3732_; 
v___x_3732_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3715_ = v___x_3732_;
goto v___jp_3714_;
}
}
v___jp_3714_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3716_ = lean_string_append(v___x_3713_, v___y_3715_);
lean_dec_ref(v___y_3715_);
v___x_3717_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__7));
v___x_3718_ = lean_string_append(v___x_3716_, v___x_3717_);
switch(lean_obj_tag(v_id_3707_))
{
case 0:
{
lean_object* v_s_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_s_3719_ = lean_ctor_get(v_id_3707_, 0);
lean_inc_ref(v_s_3719_);
lean_dec_ref(v_id_3707_);
v___x_3720_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__8));
v___x_3721_ = lean_string_append(v___x_3720_, v_s_3719_);
lean_dec_ref(v_s_3719_);
v___x_3722_ = lean_string_append(v___x_3721_, v___x_3720_);
v___y_3700_ = v___x_3718_;
v___y_3701_ = v___x_3722_;
goto v___jp_3699_;
}
case 1:
{
lean_object* v_n_3723_; lean_object* v___x_3724_; 
v_n_3723_ = lean_ctor_get(v_id_3707_, 0);
lean_inc_ref(v_n_3723_);
lean_dec_ref(v_id_3707_);
v___x_3724_ = l_Lean_JsonNumber_toString(v_n_3723_);
v___y_3700_ = v___x_3718_;
v___y_3701_ = v___x_3724_;
goto v___jp_3699_;
}
default: 
{
lean_object* v___x_3725_; 
v___x_3725_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Lsp_Ipc_shutdown_spec__3___redArg___closed__9));
v___y_3700_ = v___x_3718_;
v___y_3701_ = v___x_3725_;
goto v___jp_3699_;
}
}
}
}
else
{
lean_object* v___x_3733_; 
lean_dec(v_id_3707_);
lean_del_object(v___x_3697_);
lean_inc(v_result_3708_);
v___x_3733_ = l_Option_fromJson_x3f___at___00Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1_spec__2(v_result_3708_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3743_; 
lean_del_object(v___x_3710_);
lean_dec(v_expectedID_3686_);
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref(v___x_3733_);
v___x_3735_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0));
v___x_3736_ = l_Lean_Json_compress(v_result_3708_);
v___x_3737_ = lean_string_append(v___x_3735_, v___x_3736_);
lean_dec_ref(v___x_3736_);
v___x_3738_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1));
v___x_3739_ = lean_string_append(v___x_3737_, v___x_3738_);
v___x_3740_ = lean_string_append(v___x_3739_, v_a_3734_);
lean_dec(v_a_3734_);
v___x_3741_ = lean_mk_io_user_error(v___x_3740_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set_tag(v___x_3692_, 1);
lean_ctor_set(v___x_3692_, 0, v___x_3741_);
v___x_3743_ = v___x_3692_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3741_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; 
lean_dec(v_result_3708_);
v_a_3745_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3745_);
lean_dec_ref(v___x_3733_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set_tag(v___x_3710_, 0);
lean_ctor_set(v___x_3710_, 1, v_a_3745_);
lean_ctor_set(v___x_3710_, 0, v_expectedID_3686_);
v___x_3747_ = v___x_3710_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_expectedID_3686_);
lean_ctor_set(v_reuseFailAlloc_3751_, 1, v_a_3745_);
v___x_3747_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3749_; 
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 0, v___x_3747_);
v___x_3749_ = v___x_3692_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
}
case 3:
{
lean_object* v_id_3753_; uint8_t v_code_3754_; lean_object* v_message_3755_; lean_object* v_data_x3f_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___x_3788_; lean_object* v___y_3790_; 
lean_del_object(v___x_3697_);
lean_dec(v_expectedID_3686_);
v_id_3753_ = lean_ctor_get(v_a_3695_, 0);
lean_inc(v_id_3753_);
v_code_3754_ = lean_ctor_get_uint8(v_a_3695_, sizeof(void*)*3);
v_message_3755_ = lean_ctor_get(v_a_3695_, 1);
lean_inc_ref(v_message_3755_);
v_data_x3f_3756_ = lean_ctor_get(v_a_3695_, 2);
lean_inc(v_data_x3f_3756_);
lean_dec_ref(v_a_3695_);
v___x_3757_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2));
v___x_3758_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7));
v___x_3788_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11));
switch(lean_obj_tag(v_id_3753_))
{
case 0:
{
lean_object* v_s_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
v_s_3806_ = lean_ctor_get(v_id_3753_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_id_3753_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v_id_3753_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_s_3806_);
lean_dec(v_id_3753_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
lean_ctor_set_tag(v___x_3808_, 3);
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_s_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
v___y_3790_ = v___x_3811_;
goto v___jp_3789_;
}
}
}
case 1:
{
lean_object* v_n_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
v_n_3814_ = lean_ctor_get(v_id_3753_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_id_3753_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v_id_3753_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_n_3814_);
lean_dec(v_id_3753_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
lean_ctor_set_tag(v___x_3816_, 2);
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_n_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
v___y_3790_ = v___x_3819_;
goto v___jp_3789_;
}
}
}
default: 
{
lean_object* v___x_3822_; 
v___x_3822_ = lean_box(0);
v___y_3790_ = v___x_3822_;
goto v___jp_3789_;
}
}
v___jp_3759_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3786_; 
lean_inc(v___y_3763_);
lean_inc_ref(v___y_3760_);
v___x_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___y_3760_);
lean_ctor_set(v___x_3764_, 1, v___y_3763_);
v___x_3765_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8));
v___x_3766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3766_, 0, v_message_3755_);
v___x_3767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3765_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = lean_box(0);
v___x_3769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3764_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9));
v___x_3772_ = l_Lean_Json_opt___at___00Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__2_spec__4(v___x_3771_, v_data_x3f_3756_);
lean_dec(v_data_x3f_3756_);
v___x_3773_ = l_List_appendTR___redArg(v___x_3770_, v___x_3772_);
v___x_3774_ = l_Lean_Json_mkObj(v___x_3773_);
lean_dec(v___x_3773_);
lean_inc_ref(v___y_3762_);
v___x_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___y_3762_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
lean_ctor_set(v___x_3776_, 1, v___x_3768_);
v___x_3777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___y_3761_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3758_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = l_Lean_Json_mkObj(v___x_3778_);
lean_dec_ref(v___x_3778_);
v___x_3780_ = l_Lean_Json_compress(v___x_3779_);
v___x_3781_ = lean_string_append(v___x_3757_, v___x_3780_);
lean_dec_ref(v___x_3780_);
v___x_3782_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10));
v___x_3783_ = lean_string_append(v___x_3781_, v___x_3782_);
v___x_3784_ = lean_mk_io_user_error(v___x_3783_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set_tag(v___x_3692_, 1);
lean_ctor_set(v___x_3692_, 0, v___x_3784_);
v___x_3786_ = v___x_3692_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
v___jp_3789_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3788_);
lean_ctor_set(v___x_3791_, 1, v___y_3790_);
v___x_3792_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12));
v___x_3793_ = ((lean_object*)(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13));
switch(v_code_3754_)
{
case 0:
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3794_;
goto v___jp_3759_;
}
case 1:
{
lean_object* v___x_3795_; 
v___x_3795_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3795_;
goto v___jp_3759_;
}
case 2:
{
lean_object* v___x_3796_; 
v___x_3796_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3796_;
goto v___jp_3759_;
}
case 3:
{
lean_object* v___x_3797_; 
v___x_3797_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3797_;
goto v___jp_3759_;
}
case 4:
{
lean_object* v___x_3798_; 
v___x_3798_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3798_;
goto v___jp_3759_;
}
case 5:
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3799_;
goto v___jp_3759_;
}
case 6:
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3800_;
goto v___jp_3759_;
}
case 7:
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3801_;
goto v___jp_3759_;
}
case 8:
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3802_;
goto v___jp_3759_;
}
case 9:
{
lean_object* v___x_3803_; 
v___x_3803_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3803_;
goto v___jp_3759_;
}
case 10:
{
lean_object* v___x_3804_; 
v___x_3804_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3804_;
goto v___jp_3759_;
}
default: 
{
lean_object* v___x_3805_; 
v___x_3805_ = lean_obj_once(&l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61, &l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61_once, _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
v___y_3760_ = v___x_3793_;
v___y_3761_ = v___x_3791_;
v___y_3762_ = v___x_3792_;
v___y_3763_ = v___x_3805_;
goto v___jp_3759_;
}
}
}
}
default: 
{
lean_del_object(v___x_3697_);
lean_dec(v_a_3695_);
lean_del_object(v___x_3692_);
goto _start;
}
}
v___jp_3699_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3702_ = lean_string_append(v___y_3700_, v___y_3701_);
lean_dec_ref(v___y_3701_);
v___x_3703_ = lean_mk_io_user_error(v___x_3702_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set_tag(v___x_3697_, 1);
lean_ctor_set(v___x_3697_, 0, v___x_3703_);
v___x_3705_ = v___x_3697_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_del_object(v___x_3692_);
lean_dec(v_expectedID_3686_);
v_a_3825_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3694_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3694_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec(v_expectedID_3686_);
v_a_3834_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3689_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3689_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1___boxed(lean_object* v_expectedID_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v_expectedID_3842_, v_a_3843_);
lean_dec_ref(v_a_3843_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports(lean_object* v_requestNo_3850_, lean_object* v_uri_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
lean_inc(v_requestNo_3850_);
v___x_3854_ = l_Lean_JsonNumber_fromNat(v_requestNo_3850_);
v___x_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
v___x_3856_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_3855_);
v___x_3857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3855_);
lean_ctor_set(v___x_3857_, 1, v___x_3856_);
lean_ctor_set(v___x_3857_, 2, v_uri_3851_);
v___x_3858_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_3857_, v_a_3852_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v___x_3859_; 
lean_dec_ref(v___x_3858_);
v___x_3859_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_3855_, v_a_3852_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3918_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3862_ = v___x_3859_;
v_isShared_3863_ = v_isSharedCheck_3918_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3859_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3918_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v_result_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3916_; 
v_result_3864_ = lean_ctor_get(v_a_3860_, 1);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_a_3860_);
if (v_isSharedCheck_3916_ == 0)
{
lean_object* v_unused_3917_; 
v_unused_3917_ = lean_ctor_get(v_a_3860_, 0);
lean_dec(v_unused_3917_);
v___x_3866_ = v_a_3860_;
v_isShared_3867_ = v_isSharedCheck_3916_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_result_3864_);
lean_dec(v_a_3860_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3916_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = lean_nat_add(v_requestNo_3850_, v___x_3868_);
lean_dec(v_requestNo_3850_);
if (lean_obj_tag(v_result_3864_) == 1)
{
lean_object* v_val_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3908_; 
lean_del_object(v___x_3862_);
v_val_3870_ = lean_ctor_get(v_result_3864_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_result_3864_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3872_ = v_result_3864_;
v_isShared_3873_ = v_isSharedCheck_3908_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_val_3870_);
lean_dec(v_result_3864_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3908_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3874_; lean_object* v___x_3876_; 
v___x_3874_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 1, v___x_3874_);
lean_ctor_set(v___x_3866_, 0, v_val_3870_);
v___x_3876_ = v___x_3866_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_val_3870_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = lean_box(1);
v___x_3878_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go(v___x_3869_, v___x_3876_, v___x_3877_, v_a_3852_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3898_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3898_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3898_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v_fst_3883_; lean_object* v_snd_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3897_; 
v_fst_3883_ = lean_ctor_get(v_a_3879_, 0);
v_snd_3884_ = lean_ctor_get(v_a_3879_, 1);
v_isSharedCheck_3897_ = !lean_is_exclusive(v_a_3879_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3886_ = v_a_3879_;
v_isShared_3887_ = v_isSharedCheck_3897_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_snd_3884_);
lean_inc(v_fst_3883_);
lean_dec(v_a_3879_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3897_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 0, v_fst_3883_);
v___x_3889_ = v___x_3872_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_fst_3883_);
v___x_3889_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3891_; 
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 0, v___x_3889_);
v___x_3891_ = v___x_3886_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_snd_3884_);
v___x_3891_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
lean_object* v___x_3893_; 
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v___x_3891_);
v___x_3893_ = v___x_3881_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
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
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_del_object(v___x_3872_);
v_a_3899_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3878_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3878_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
}
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
lean_dec(v_result_3864_);
v___x_3909_ = lean_box(0);
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 1, v___x_3869_);
lean_ctor_set(v___x_3866_, 0, v___x_3909_);
v___x_3911_ = v___x_3866_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v___x_3869_);
v___x_3911_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3913_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3911_);
v___x_3913_ = v___x_3862_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
lean_dec(v_requestNo_3850_);
v_a_3919_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3859_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3859_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec_ref(v___x_3855_);
lean_dec(v_requestNo_3850_);
v_a_3927_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3858_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3858_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImports___boxed(lean_object* v_requestNo_3935_, lean_object* v_uri_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImports(v_requestNo_3935_, v_uri_3936_, v_a_3937_);
lean_dec_ref(v_a_3937_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(lean_object* v_v_3940_){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = l_Lean_Lsp_instToJsonLeanModuleHierarchyImportedByParams_toJson(v_v_3940_);
v___x_3942_ = l_Lean_Json_Structured_fromJson_x3f(v___x_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1___boxed(lean_object* v_v_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_v_3943_);
lean_dec_ref(v_v_3943_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(lean_object* v_h_3945_, lean_object* v_r_3946_){
_start:
{
lean_object* v_id_3948_; lean_object* v_method_3949_; lean_object* v_param_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3970_; 
v_id_3948_ = lean_ctor_get(v_r_3946_, 0);
v_method_3949_ = lean_ctor_get(v_r_3946_, 1);
v_param_3950_ = lean_ctor_get(v_r_3946_, 2);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_r_3946_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3952_ = v_r_3946_;
v_isShared_3953_ = v_isSharedCheck_3970_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_param_3950_);
lean_inc(v_method_3949_);
lean_inc(v_id_3948_);
lean_dec(v_r_3946_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3970_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___y_3955_; lean_object* v___x_3960_; 
v___x_3960_ = l_Lean_Json_toStructured_x3f___at___00IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0_spec__1(v_param_3950_);
lean_dec(v_param_3950_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v___x_3961_; 
lean_dec_ref(v___x_3960_);
v___x_3961_ = lean_box(0);
v___y_3955_ = v___x_3961_;
goto v___jp_3954_;
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
v_a_3962_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3960_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3960_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
v___y_3955_ = v___x_3967_;
goto v___jp_3954_;
}
}
}
v___jp_3954_:
{
lean_object* v___x_3957_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 2, v___y_3955_);
v___x_3957_ = v___x_3952_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_id_3948_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_method_3949_);
lean_ctor_set(v_reuseFailAlloc_3959_, 2, v___y_3955_);
v___x_3957_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_IO_FS_Stream_writeLspMessage(v_h_3945_, v___x_3957_);
return v___x_3958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0___boxed(lean_object* v_h_3971_, lean_object* v_r_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_h_3971_, v_r_3972_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(lean_object* v_r_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v___x_3978_; lean_object* v_a_3979_; lean_object* v___x_3980_; 
v___x_3978_ = l_Lean_Lsp_Ipc_stdin(v_a_3976_);
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3979_);
lean_dec_ref(v___x_3978_);
v___x_3980_ = l_IO_FS_Stream_writeLspRequest___at___00Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0_spec__0(v_a_3979_, v_r_3975_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0___boxed(lean_object* v_r_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v_r_3981_, v_a_3982_);
lean_dec_ref(v_a_3982_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(lean_object* v_requestNo_3986_, lean_object* v_item_3987_, lean_object* v_visited_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_module_3991_; lean_object* v_name_3992_; uint8_t v___x_3993_; 
v_module_3991_ = lean_ctor_get(v_item_3987_, 0);
v_name_3992_ = lean_ctor_get(v_module_3991_, 0);
v___x_3993_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__0___redArg(v_name_3992_, v_visited_3988_);
if (v___x_3993_ == 0)
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
lean_inc(v_requestNo_3986_);
v___x_3994_ = l_Lean_JsonNumber_fromNat(v_requestNo_3986_);
v___x_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
v___x_3996_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___closed__0));
lean_inc_ref(v_module_3991_);
lean_inc_ref(v___x_3995_);
v___x_3997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3995_);
lean_ctor_set(v___x_3997_, 1, v___x_3996_);
lean_ctor_set(v___x_3997_, 2, v_module_3991_);
v___x_3998_ = l_Lean_Lsp_Ipc_writeRequest___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__0(v___x_3997_, v_a_3989_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v___x_3999_; 
lean_dec_ref(v___x_3998_);
v___x_3999_ = l_Lean_Lsp_Ipc_readResponseAs___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go_spec__1(v___x_3995_, v_a_3989_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v___y_4002_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref(v___x_3999_);
if (v___x_3993_ == 0)
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = lean_box(0);
lean_inc_ref(v_name_3992_);
v___x_4045_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandIncomingCallHierarchy_go_spec__4___redArg(v_name_3992_, v___x_4044_, v_visited_3988_);
v___y_4002_ = v___x_4045_;
goto v___jp_4001_;
}
else
{
v___y_4002_ = v_visited_3988_;
goto v___jp_4001_;
}
v___jp_4001_:
{
lean_object* v_result_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4042_; 
v_result_4003_ = lean_ctor_get(v_a_4000_, 1);
v_isSharedCheck_4042_ = !lean_is_exclusive(v_a_4000_);
if (v_isSharedCheck_4042_ == 0)
{
lean_object* v_unused_4043_; 
v_unused_4043_ = lean_ctor_get(v_a_4000_, 0);
lean_dec(v_unused_4043_);
v___x_4005_ = v_a_4000_;
v_isShared_4006_ = v_isSharedCheck_4042_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_result_4003_);
lean_dec(v_a_4000_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4042_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4011_; 
v___x_4007_ = lean_unsigned_to_nat(1u);
v___x_4008_ = lean_nat_add(v_requestNo_3986_, v___x_4007_);
lean_dec(v_requestNo_3986_);
v___x_4009_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 1, v___x_4009_);
lean_ctor_set(v___x_4005_, 0, v___x_4008_);
v___x_4011_ = v___x_4005_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4008_);
lean_ctor_set(v_reuseFailAlloc_4041_, 1, v___x_4009_);
v___x_4011_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
size_t v_sz_4012_; size_t v___x_4013_; lean_object* v___x_4014_; 
v_sz_4012_ = lean_array_size(v_result_4003_);
v___x_4013_ = ((size_t)0ULL);
v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___y_4002_, v_result_4003_, v_sz_4012_, v___x_4013_, v___x_4011_, v_a_3989_);
lean_dec(v_result_4003_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4032_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4017_ = v___x_4014_;
v_isShared_4018_ = v_isSharedCheck_4032_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4014_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4032_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v_fst_4019_; lean_object* v_snd_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4031_; 
v_fst_4019_ = lean_ctor_get(v_a_4015_, 0);
v_snd_4020_ = lean_ctor_get(v_a_4015_, 1);
v_isSharedCheck_4031_ = !lean_is_exclusive(v_a_4015_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4022_ = v_a_4015_;
v_isShared_4023_ = v_isSharedCheck_4031_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_snd_4020_);
lean_inc(v_fst_4019_);
lean_dec(v_a_4015_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4031_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4026_; 
v___x_4024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4024_, 0, v_item_3987_);
lean_ctor_set(v___x_4024_, 1, v_snd_4020_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 1, v_fst_4019_);
lean_ctor_set(v___x_4022_, 0, v___x_4024_);
v___x_4026_ = v___x_4022_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v___x_4024_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_fst_4019_);
v___x_4026_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
lean_object* v___x_4028_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 0, v___x_4026_);
v___x_4028_ = v___x_4017_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4026_);
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
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec_ref(v_item_3987_);
v_a_4033_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4014_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4014_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec(v_visited_3988_);
lean_dec_ref(v_item_3987_);
lean_dec(v_requestNo_3986_);
v_a_4046_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_3999_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_3999_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec_ref(v___x_3995_);
lean_dec(v_visited_3988_);
lean_dec_ref(v_item_3987_);
lean_dec(v_requestNo_3986_);
v_a_4054_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_3998_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_3998_);
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
else
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
lean_dec(v_visited_3988_);
v___x_4062_ = ((lean_object*)(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImports_go___closed__1));
v___x_4063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4063_, 0, v_item_3987_);
lean_ctor_set(v___x_4063_, 1, v___x_4062_);
v___x_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
lean_ctor_set(v___x_4064_, 1, v_requestNo_3986_);
v___x_4065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
return v___x_4065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(lean_object* v___x_4066_, lean_object* v_as_4067_, size_t v_sz_4068_, size_t v_i_4069_, lean_object* v_b_4070_, lean_object* v___y_4071_){
_start:
{
uint8_t v___x_4073_; 
v___x_4073_ = lean_usize_dec_lt(v_i_4069_, v_sz_4068_);
if (v___x_4073_ == 0)
{
lean_object* v___x_4074_; 
lean_dec(v___x_4066_);
v___x_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4074_, 0, v_b_4070_);
return v___x_4074_;
}
else
{
lean_object* v_fst_4075_; lean_object* v_snd_4076_; lean_object* v_a_4077_; lean_object* v___x_4078_; 
v_fst_4075_ = lean_ctor_get(v_b_4070_, 0);
lean_inc(v_fst_4075_);
v_snd_4076_ = lean_ctor_get(v_b_4070_, 1);
lean_inc(v_snd_4076_);
lean_dec_ref(v_b_4070_);
v_a_4077_ = lean_array_uget_borrowed(v_as_4067_, v_i_4069_);
lean_inc(v___x_4066_);
lean_inc(v_a_4077_);
v___x_4078_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_fst_4075_, v_a_4077_, v___x_4066_, v___y_4071_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v_fst_4080_; lean_object* v_snd_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4092_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
lean_inc(v_a_4079_);
lean_dec_ref(v___x_4078_);
v_fst_4080_ = lean_ctor_get(v_a_4079_, 0);
v_snd_4081_ = lean_ctor_get(v_a_4079_, 1);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_a_4079_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4083_ = v_a_4079_;
v_isShared_4084_ = v_isSharedCheck_4092_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_snd_4081_);
lean_inc(v_fst_4080_);
lean_dec(v_a_4079_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4092_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4085_ = lean_array_push(v_snd_4076_, v_fst_4080_);
if (v_isShared_4084_ == 0)
{
lean_ctor_set(v___x_4083_, 1, v___x_4085_);
lean_ctor_set(v___x_4083_, 0, v_snd_4081_);
v___x_4087_ = v___x_4083_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_snd_4081_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
size_t v___x_4088_; size_t v___x_4089_; 
v___x_4088_ = ((size_t)1ULL);
v___x_4089_ = lean_usize_add(v_i_4069_, v___x_4088_);
v_i_4069_ = v___x_4089_;
v_b_4070_ = v___x_4087_;
goto _start;
}
}
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
lean_dec(v_snd_4076_);
lean_dec(v___x_4066_);
v_a_4093_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4078_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4078_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1___boxed(lean_object* v___x_4101_, lean_object* v_as_4102_, lean_object* v_sz_4103_, lean_object* v_i_4104_, lean_object* v_b_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
size_t v_sz_boxed_4108_; size_t v_i_boxed_4109_; lean_object* v_res_4110_; 
v_sz_boxed_4108_ = lean_unbox_usize(v_sz_4103_);
lean_dec(v_sz_4103_);
v_i_boxed_4109_ = lean_unbox_usize(v_i_4104_);
lean_dec(v_i_4104_);
v_res_4110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go_spec__1(v___x_4101_, v_as_4102_, v_sz_boxed_4108_, v_i_boxed_4109_, v_b_4105_, v___y_4106_);
lean_dec_ref(v___y_4106_);
lean_dec_ref(v_as_4102_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go___boxed(lean_object* v_requestNo_4111_, lean_object* v_item_4112_, lean_object* v_visited_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v_requestNo_4111_, v_item_4112_, v_visited_4113_, v_a_4114_);
lean_dec_ref(v_a_4114_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(lean_object* v_requestNo_4117_, lean_object* v_uri_4118_, lean_object* v_a_4119_){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
lean_inc(v_requestNo_4117_);
v___x_4121_ = l_Lean_JsonNumber_fromNat(v_requestNo_4117_);
v___x_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
v___x_4123_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__0));
lean_inc_ref(v___x_4122_);
v___x_4124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4122_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
lean_ctor_set(v___x_4124_, 2, v_uri_4118_);
v___x_4125_ = l_Lean_Lsp_Ipc_writeRequest___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__0(v___x_4124_, v_a_4119_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v___x_4126_; 
lean_dec_ref(v___x_4125_);
v___x_4126_ = l_Lean_Lsp_Ipc_readResponseAs___at___00Lean_Lsp_Ipc_expandModuleHierarchyImports_spec__1(v___x_4122_, v_a_4119_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4185_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4129_ = v___x_4126_;
v_isShared_4130_ = v_isSharedCheck_4185_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4126_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4185_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v_result_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4183_; 
v_result_4131_ = lean_ctor_get(v_a_4127_, 1);
v_isSharedCheck_4183_ = !lean_is_exclusive(v_a_4127_);
if (v_isSharedCheck_4183_ == 0)
{
lean_object* v_unused_4184_; 
v_unused_4184_ = lean_ctor_get(v_a_4127_, 0);
lean_dec(v_unused_4184_);
v___x_4133_ = v_a_4127_;
v_isShared_4134_ = v_isSharedCheck_4183_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_result_4131_);
lean_dec(v_a_4127_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4183_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4135_ = lean_unsigned_to_nat(1u);
v___x_4136_ = lean_nat_add(v_requestNo_4117_, v___x_4135_);
lean_dec(v_requestNo_4117_);
if (lean_obj_tag(v_result_4131_) == 1)
{
lean_object* v_val_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4175_; 
lean_del_object(v___x_4129_);
v_val_4137_ = lean_ctor_get(v_result_4131_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_result_4131_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4139_ = v_result_4131_;
v_isShared_4140_ = v_isSharedCheck_4175_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_val_4137_);
lean_dec(v_result_4131_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4175_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4141_; lean_object* v___x_4143_; 
v___x_4141_ = ((lean_object*)(l_Lean_Lsp_Ipc_expandModuleHierarchyImports___closed__1));
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 1, v___x_4141_);
lean_ctor_set(v___x_4133_, 0, v_val_4137_);
v___x_4143_ = v___x_4133_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_val_4137_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4144_ = lean_box(1);
v___x_4145_ = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_expandModuleHierarchyImportedBy_go(v___x_4136_, v___x_4143_, v___x_4144_, v_a_4119_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4165_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4148_ = v___x_4145_;
v_isShared_4149_ = v_isSharedCheck_4165_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4145_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4165_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v_fst_4150_; lean_object* v_snd_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4164_; 
v_fst_4150_ = lean_ctor_get(v_a_4146_, 0);
v_snd_4151_ = lean_ctor_get(v_a_4146_, 1);
v_isSharedCheck_4164_ = !lean_is_exclusive(v_a_4146_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4153_ = v_a_4146_;
v_isShared_4154_ = v_isSharedCheck_4164_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_snd_4151_);
lean_inc(v_fst_4150_);
lean_dec(v_a_4146_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4164_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v_fst_4150_);
v___x_4156_ = v___x_4139_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_fst_4150_);
v___x_4156_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
lean_object* v___x_4158_; 
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 0, v___x_4156_);
v___x_4158_ = v___x_4153_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4156_);
lean_ctor_set(v_reuseFailAlloc_4162_, 1, v_snd_4151_);
v___x_4158_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
lean_object* v___x_4160_; 
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v___x_4158_);
v___x_4160_ = v___x_4148_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4158_);
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
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_del_object(v___x_4139_);
v_a_4166_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4145_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4145_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
}
else
{
lean_object* v___x_4176_; lean_object* v___x_4178_; 
lean_dec(v_result_4131_);
v___x_4176_ = lean_box(0);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 1, v___x_4136_);
lean_ctor_set(v___x_4133_, 0, v___x_4176_);
v___x_4178_ = v___x_4133_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4182_, 1, v___x_4136_);
v___x_4178_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
lean_object* v___x_4180_; 
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 0, v___x_4178_);
v___x_4180_ = v___x_4129_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4178_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
}
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_dec(v_requestNo_4117_);
v_a_4186_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_4126_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4126_);
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
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec_ref(v___x_4122_);
lean_dec(v_requestNo_4117_);
v_a_4194_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4125_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4125_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy___boxed(lean_object* v_requestNo_4202_, lean_object* v_uri_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_Lean_Lsp_Ipc_expandModuleHierarchyImportedBy(v_requestNo_4202_, v_uri_4203_, v_a_4204_);
lean_dec_ref(v_a_4204_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object* v_lean_4209_, lean_object* v_args_4210_, lean_object* v_test_4211_){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; uint8_t v___x_4216_; uint8_t v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4213_ = ((lean_object*)(l_Lean_Lsp_Ipc_ipcStdioConfig));
v___x_4214_ = lean_box(0);
v___x_4215_ = ((lean_object*)(l_Lean_Lsp_Ipc_runWith___redArg___closed__0));
v___x_4216_ = 1;
v___x_4217_ = 0;
v___x_4218_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4218_, 0, v___x_4213_);
lean_ctor_set(v___x_4218_, 1, v_lean_4209_);
lean_ctor_set(v___x_4218_, 2, v_args_4210_);
lean_ctor_set(v___x_4218_, 3, v___x_4214_);
lean_ctor_set(v___x_4218_, 4, v___x_4215_);
lean_ctor_set_uint8(v___x_4218_, sizeof(void*)*5, v___x_4216_);
lean_ctor_set_uint8(v___x_4218_, sizeof(void*)*5 + 1, v___x_4217_);
v___x_4219_ = lean_io_process_spawn(v___x_4218_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4221_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref(v___x_4219_);
v___x_4221_ = lean_apply_2(v_test_4211_, v_a_4220_, lean_box(0));
return v___x_4221_;
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
lean_dec_ref(v_test_4211_);
v_a_4222_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4219_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4219_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg___boxed(lean_object* v_lean_4230_, lean_object* v_args_4231_, lean_object* v_test_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4230_, v_args_4231_, v_test_4232_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object* v_00_u03b1_4235_, lean_object* v_lean_4236_, lean_object* v_args_4237_, lean_object* v_test_4238_){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = l_Lean_Lsp_Ipc_runWith___redArg(v_lean_4236_, v_args_4237_, v_test_4238_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___boxed(lean_object* v_00_u03b1_4241_, lean_object* v_lean_4242_, lean_object* v_args_4243_, lean_object* v_test_4244_, lean_object* v_a_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_Lean_Lsp_Ipc_runWith(v_00_u03b1_4241_, v_lean_4242_, v_args_4243_, v_test_4244_);
return v_res_4246_;
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
