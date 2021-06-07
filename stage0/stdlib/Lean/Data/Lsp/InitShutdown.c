// Lean compiler output
// Module: Lean.Data.Lsp.InitShutdown
// Imports: Init Lean.Data.Lsp.Capabilities Lean.Data.Lsp.Workspace Lean.Data.Json
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
lean_object* l_Lean_Lsp_instFromJsonTrace___closed__1;
lean_object* l_Lean_Lsp_instFromJsonTrace___closed__3;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589_(lean_object*);
extern lean_object* l_Lean_instFromJsonOption___rarg___closed__1;
lean_object* l_Lean_Lsp_instToJsonInitializeResult___closed__1;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Lsp_instFromJsonTrace___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonClientInfo;
lean_object* l_Lean_Lsp_instFromJsonTrace___closed__2;
lean_object* l_Lean_Lsp_instFromJsonInitializeParams(lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_465____boxed(lean_object*);
lean_object* l_Lean_Lsp_instToJsonInitializationOptions___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Lsp_InitializeResult_serverInfo_x3f___default;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_494_(lean_object*);
lean_object* l_Lean_Lsp_Trace_hasToJson___closed__2;
lean_object* l_Lean_Lsp_InitializeParams_processId_x3f___default;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonInitializeParams___spec__7(size_t, size_t, lean_object*);
lean_object* l_Lean_Lsp_instToJsonServerInfo;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__2;
lean_object* l_Lean_Lsp_instToJsonInitializedParams___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Lsp_Trace_hasToJson___boxed(lean_object*);
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__10;
lean_object* l_Lean_Lsp_Trace_hasToJson(uint8_t);
lean_object* l_List_join___rarg(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonDocumentFilter____x40_Lean_Data_Lsp_Basic___hyg_1611____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonInitializedParams(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonServerInfo___closed__1;
lean_object* l_Lean_Lsp_instToJsonInitializeParams;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__1;
lean_object* l_Lean_Lsp_instFromJsonInitializeParams___boxed(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonInitializedParams___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonInitializationOptions;
extern lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_1148____closed__1;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__9;
lean_object* l_Lean_Lsp_instFromJsonInitializedParams___closed__1;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__2;
lean_object* l_Lean_Lsp_InitializeParams_clientInfo_x3f___default;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_55____boxed(lean_object*);
lean_object* l_Lean_Lsp_Trace_hasToJson_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonServerInfo___closed__1;
lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24_(lean_object*);
uint8_t l_Lean_Lsp_InitializeParams_trace___default;
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__4;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__4___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__8;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Trace_hasToJson___closed__1;
lean_object* l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__5(size_t, size_t, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_195____boxed(lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__5;
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonDocumentFilter____x40_Lean_Data_Lsp_Basic___hyg_1639____spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_ClientCapabilities_hasToJson___closed__1;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__7;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_55_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__12;
lean_object* l_Lean_Lsp_instFromJsonTrace_match__1(lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__14;
lean_object* l_Lean_Lsp_Trace_hasToJson_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_26_(lean_object*);
lean_object* l_Lean_Lsp_ServerInfo_version_x3f___default;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__3;
lean_object* l_Lean_Lsp_instToJsonInitializedParams(lean_object*);
lean_object* l_Lean_Lsp_instToJsonInitializationOptions;
lean_object* l_Lean_Lsp_instFromJsonInitializeResult;
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_197_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_465_(lean_object*);
lean_object* l_Lean_Lsp_Trace_hasToJson_match__1(lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_195_(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonClientInfo___closed__1;
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonTrace_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__6;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonInitializeResult;
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_1148____spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__13;
lean_object* l_Lean_Lsp_instToJsonClientInfo;
lean_object* l_Lean_Lsp_instFromJsonTrace(lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_26____boxed(lean_object*);
extern lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1;
lean_object* l_Lean_Json_mkObj(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_26____closed__6;
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__3(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonInitializeResult___closed__1;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonInitializeParams___closed__1;
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonServerInfo;
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_115_(lean_object*);
lean_object* l_Lean_Lsp_InitializeParams_rootUri_x3f___default;
lean_object* l_Lean_Lsp_InitializeParams_initializationOptions_x3f___default;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____boxed(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonInitializeParams___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__3;
lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_58_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____closed__1;
extern lean_object* l_Lean_Lsp_instFromJsonClientCapabilities___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_494____boxed(lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175_(lean_object*);
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_1177____spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175____closed__1;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298_(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonInitializationOptions___closed__1;
lean_object* l_Lean_Lsp_InitializeParams_workspaceFolders_x3f___default;
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_ClientInfo_version_x3f___default;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonClientInfo___closed__1;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__11;
lean_object* l_Lean_Lsp_Trace_hasToJson___closed__3;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560_(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(lean_object*, lean_object*);
#define _init_l_Lean_Lsp_ClientInfo_version_x3f___default(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_box(0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_ClientInfo_version_x3f___default_end;\
}\
l_Lean_Lsp_ClientInfo_version_x3f___default_end: ((void) 0);}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_26_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_1148____closed__1;
x_10 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonDocumentFilter____x40_Lean_Data_Lsp_Basic___hyg_1611____spec__1(x_9, x_3);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_List_join___rarg(x_12);
x_14 = l_Lean_Json_mkObj(x_13);
return x_14;
}
}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_26____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_26_(x_1);
lean_dec(x_1);
return x_2;
}
}
#define _init_l_Lean_Lsp_instToJsonClientInfo___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_26____boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instToJsonClientInfo___closed__1_end;\
}\
l_Lean_Lsp_instToJsonClientInfo___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_instToJsonClientInfo(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Lsp_instToJsonClientInfo___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instToJsonClientInfo_end;\
}\
l_Lean_Lsp_instToJsonClientInfo_end: ((void) 0);}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_55_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_1148____closed__1;
x_7 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonDocumentFilter____x40_Lean_Data_Lsp_Basic___hyg_1639____spec__1(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_55____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_55_(x_1);
lean_dec(x_1);
return x_2;
}
}
#define _init_l_Lean_Lsp_instFromJsonClientInfo___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_55____boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instFromJsonClientInfo___closed__1_end;\
}\
l_Lean_Lsp_instFromJsonClientInfo___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_instFromJsonClientInfo(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Lsp_instFromJsonClientInfo___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instFromJsonClientInfo_end;\
}\
l_Lean_Lsp_instFromJsonClientInfo_end: ((void) 0);}
#define _init_l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("off");\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__1_end;\
}\
l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("messages");\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__2_end;\
}\
l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__2_end: ((void) 0);}
#define _init_l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("verbose");\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__3_end;\
}\
l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__3_end: ((void) 0);}
lean_object* l_Lean_Lsp_instFromJsonTrace_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_2);
x_10 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__2;
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_3);
x_12 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__3;
x_13 = lean_string_dec_eq(x_7, x_12);
lean_dec(x_7);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_apply_1(x_5, x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_apply_1(x_3, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_apply_1(x_2, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Lsp_instFromJsonTrace_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonTrace_match__1___rarg), 5, 0);
return x_2;
}
}
#define _init_l_Lean_Lsp_instFromJsonTrace___closed__1(__INIT_VAR__) { \
{\
uint8_t x_1; lean_object* x_2; lean_object* x_3; \
x_1 = 2;\
x_2 = lean_box(x_1);\
x_3 = lean_alloc_ctor(1, 1, 0);\
lean_ctor_set(x_3, 0, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Lsp_instFromJsonTrace___closed__1_end;\
}\
l_Lean_Lsp_instFromJsonTrace___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_instFromJsonTrace___closed__2(__INIT_VAR__) { \
{\
uint8_t x_1; lean_object* x_2; lean_object* x_3; \
x_1 = 1;\
x_2 = lean_box(x_1);\
x_3 = lean_alloc_ctor(1, 1, 0);\
lean_ctor_set(x_3, 0, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Lsp_instFromJsonTrace___closed__2_end;\
}\
l_Lean_Lsp_instFromJsonTrace___closed__2_end: ((void) 0);}
#define _init_l_Lean_Lsp_instFromJsonTrace___closed__3(__INIT_VAR__) { \
{\
uint8_t x_1; lean_object* x_2; lean_object* x_3; \
x_1 = 0;\
x_2 = lean_box(x_1);\
x_3 = lean_alloc_ctor(1, 1, 0);\
lean_ctor_set(x_3, 0, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Lsp_instFromJsonTrace___closed__3_end;\
}\
l_Lean_Lsp_instFromJsonTrace___closed__3_end: ((void) 0);}
lean_object* l_Lean_Lsp_instFromJsonTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getStr_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__2;
x_8 = lean_string_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__3;
x_10 = lean_string_dec_eq(x_4, x_9);
lean_dec(x_4);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Lsp_instFromJsonTrace___closed__1;
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = l_Lean_Lsp_instFromJsonTrace___closed__2;
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = l_Lean_Lsp_instFromJsonTrace___closed__3;
return x_14;
}
}
}
}
lean_object* l_Lean_Lsp_instFromJsonTrace___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFromJsonTrace(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Lsp_Trace_hasToJson_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Lsp_Trace_hasToJson_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_Trace_hasToJson_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Lsp_Trace_hasToJson_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Lsp_Trace_hasToJson_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
#define _init_l_Lean_Lsp_Trace_hasToJson___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__1;\
x_2 = lean_alloc_ctor(3, 1, 0);\
lean_ctor_set(x_2, 0, x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Lsp_Trace_hasToJson___closed__1_end;\
}\
l_Lean_Lsp_Trace_hasToJson___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_Trace_hasToJson___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__2;\
x_2 = lean_alloc_ctor(3, 1, 0);\
lean_ctor_set(x_2, 0, x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Lsp_Trace_hasToJson___closed__2_end;\
}\
l_Lean_Lsp_Trace_hasToJson___closed__2_end: ((void) 0);}
#define _init_l_Lean_Lsp_Trace_hasToJson___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__3;\
x_2 = lean_alloc_ctor(3, 1, 0);\
lean_ctor_set(x_2, 0, x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Lsp_Trace_hasToJson___closed__3_end;\
}\
l_Lean_Lsp_Trace_hasToJson___closed__3_end: ((void) 0);}
lean_object* l_Lean_Lsp_Trace_hasToJson(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_Trace_hasToJson___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_Trace_hasToJson___closed__2;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_Trace_hasToJson___closed__3;
return x_4;
}
}
}
}
lean_object* l_Lean_Lsp_Trace_hasToJson___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Lsp_Trace_hasToJson(x_2);
return x_3;
}
}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("editDelay");\
__INIT_VAR__ = x_1; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175____closed__1_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175____closed__1_end: ((void) 0);}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175____closed__1;
x_3 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_1148____spec__1(x_2, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_List_join___rarg(x_5);
x_7 = l_Lean_Json_mkObj(x_6);
return x_7;
}
}
#define _init_l_Lean_Lsp_instToJsonInitializationOptions___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175_), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instToJsonInitializationOptions___closed__1_end;\
}\
l_Lean_Lsp_instToJsonInitializationOptions___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_instToJsonInitializationOptions(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Lsp_instToJsonInitializationOptions___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instToJsonInitializationOptions_end;\
}\
l_Lean_Lsp_instToJsonInitializationOptions_end: ((void) 0);}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_195_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_1177____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_195____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_195_(x_1);
lean_dec(x_1);
return x_2;
}
}
#define _init_l_Lean_Lsp_instFromJsonInitializationOptions___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_195____boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instFromJsonInitializationOptions___closed__1_end;\
}\
l_Lean_Lsp_instFromJsonInitializationOptions___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_instFromJsonInitializationOptions(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Lsp_instFromJsonInitializationOptions___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instFromJsonInitializationOptions_end;\
}\
l_Lean_Lsp_instFromJsonInitializationOptions_end: ((void) 0);}
#define _init_l_Lean_Lsp_InitializeParams_processId_x3f___default(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_box(0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_InitializeParams_processId_x3f___default_end;\
}\
l_Lean_Lsp_InitializeParams_processId_x3f___default_end: ((void) 0);}
#define _init_l_Lean_Lsp_InitializeParams_clientInfo_x3f___default(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_box(0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_InitializeParams_clientInfo_x3f___default_end;\
}\
l_Lean_Lsp_InitializeParams_clientInfo_x3f___default_end: ((void) 0);}
#define _init_l_Lean_Lsp_InitializeParams_rootUri_x3f___default(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_box(0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_InitializeParams_rootUri_x3f___default_end;\
}\
l_Lean_Lsp_InitializeParams_rootUri_x3f___default_end: ((void) 0);}
#define _init_l_Lean_Lsp_InitializeParams_initializationOptions_x3f___default(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_box(0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_InitializeParams_initializationOptions_x3f___default_end;\
}\
l_Lean_Lsp_InitializeParams_initializationOptions_x3f___default_end: ((void) 0);}
#define _init_l_Lean_Lsp_InitializeParams_trace___default(__INIT_VAR__) { \
{\
uint8_t x_1; \
x_1 = 0;\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_InitializeParams_trace___default_end;\
}\
l_Lean_Lsp_InitializeParams_trace___default_end: ((void) 0);}
#define _init_l_Lean_Lsp_InitializeParams_workspaceFolders_x3f___default(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_box(0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_InitializeParams_workspaceFolders_x3f___default_end;\
}\
l_Lean_Lsp_InitializeParams_workspaceFolders_x3f___default_end: ((void) 0);}
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_26_(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175_(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24_(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = x_4;
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__5(x_6, x_7, x_8);
x_10 = x_9;
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("processId");\
__INIT_VAR__ = x_1; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__1_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__1_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("clientInfo");\
__INIT_VAR__ = x_1; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__2_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__2_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("rootUri");\
__INIT_VAR__ = x_1; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__3_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__3_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("initializationOptions");\
__INIT_VAR__ = x_1; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__4_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__4_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("capabilities");\
__INIT_VAR__ = x_1; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__5_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__5_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__6(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__5;\
x_2 = l_Lean_Lsp_ClientCapabilities_hasToJson___closed__1;\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__6_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__6_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__7(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__6;\
x_3 = lean_alloc_ctor(1, 2, 0);\
lean_ctor_set(x_3, 0, x_2);\
lean_ctor_set(x_3, 1, x_1);\
__INIT_VAR__ = x_3; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__7_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__7_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__8(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("workspaceFolders");\
__INIT_VAR__ = x_1; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__8_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__8_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__9(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_26____closed__6;\
x_2 = l_Lean_Lsp_Trace_hasToJson___closed__1;\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__9_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__9_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__10(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__9;\
x_3 = lean_alloc_ctor(1, 2, 0);\
lean_ctor_set(x_3, 0, x_2);\
lean_ctor_set(x_3, 1, x_1);\
__INIT_VAR__ = x_3; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__10_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__10_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__11(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_26____closed__6;\
x_2 = l_Lean_Lsp_Trace_hasToJson___closed__2;\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__11_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__11_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__12(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__11;\
x_3 = lean_alloc_ctor(1, 2, 0);\
lean_ctor_set(x_3, 0, x_2);\
lean_ctor_set(x_3, 1, x_1);\
__INIT_VAR__ = x_3; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__12_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__12_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__13(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_26____closed__6;\
x_2 = l_Lean_Lsp_Trace_hasToJson___closed__3;\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__13_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__13_end: ((void) 0);}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__14(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__13;\
x_3 = lean_alloc_ctor(1, 2, 0);\
lean_ctor_set(x_3, 0, x_2);\
lean_ctor_set(x_3, 1, x_1);\
__INIT_VAR__ = x_3; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__14_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__14_end: ((void) 0);}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__1;
x_4 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__2;
x_7 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__2(x_6, x_5);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__3;
x_10 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonDocumentFilter____x40_Lean_Data_Lsp_Basic___hyg_1611____spec__1(x_9, x_8);
lean_dec(x_8);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__4;
x_13 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__3(x_12, x_11);
x_14 = lean_box(0);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__8;
x_18 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__4(x_17, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
switch (x_15) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__10;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__7;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_List_join___rarg(x_27);
x_29 = l_Lean_Json_mkObj(x_28);
return x_29;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__12;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_19);
x_32 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__7;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_List_join___rarg(x_37);
x_39 = l_Lean_Json_mkObj(x_38);
return x_39;
}
default: 
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__14;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_19);
x_42 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__7;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_13);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_10);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_7);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_List_join___rarg(x_47);
x_49 = l_Lean_Json_mkObj(x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____spec__5(x_4, x_5, x_3);
return x_6;
}
}
#define _init_l_Lean_Lsp_instToJsonInitializeParams___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298_), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instToJsonInitializeParams___closed__1_end;\
}\
l_Lean_Lsp_instToJsonInitializeParams___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_instToJsonInitializeParams(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Lsp_instToJsonInitializeParams___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instToJsonInitializeParams_end;\
}\
l_Lean_Lsp_instToJsonInitializeParams_end: ((void) 0);}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getInt_x3f(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonClientInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_55_(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_195_(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_instFromJsonClientCapabilities___closed__1;
return x_3;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__1;
x_8 = lean_string_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__2;
x_10 = lean_string_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__3;
x_12 = lean_string_dec_eq(x_6, x_11);
lean_dec(x_6);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Lsp_instFromJsonTrace___closed__1;
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = l_Lean_Lsp_instFromJsonTrace___closed__2;
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_6);
x_16 = l_Lean_Lsp_instFromJsonTrace___closed__3;
return x_16;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonInitializeParams___spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = x_3;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_58_(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = x_2 + x_14;
x_16 = x_13;
x_17 = lean_array_uset(x_9, x_2, x_16);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = x_4;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonInitializeParams___spec__7(x_6, x_7, x_8);
x_10 = x_9;
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_box(0);
return x_11;
}
}
}
lean_object* l_Lean_Lsp_instFromJsonInitializeParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(x_1, x_2);
x_4 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__2;
x_5 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(x_1, x_4);
x_6 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__3;
x_7 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_1, x_6);
x_8 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__4;
x_9 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(x_1, x_8);
x_10 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_26____closed__6;
x_11 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(x_1, x_10);
x_12 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__8;
x_13 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(x_1, x_12);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_box(0);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_7);
lean_ctor_set(x_16, 3, x_9);
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set(x_16, 5, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*6, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_5);
lean_ctor_set(x_21, 2, x_7);
lean_ctor_set(x_21, 3, x_9);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set(x_21, 5, x_13);
x_22 = lean_unbox(x_19);
lean_dec(x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*6, x_22);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_7);
lean_ctor_set(x_25, 3, x_9);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_13);
x_26 = lean_unbox(x_23);
lean_dec(x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*6, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonInitializeParams___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Lsp_instFromJsonInitializeParams___spec__7(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Lsp_instFromJsonInitializeParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFromJsonInitializeParams(x_1);
lean_dec(x_1);
return x_2;
}
}
#define _init_l_Lean_Lsp_instFromJsonInitializedParams___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = lean_box(0);\
x_2 = lean_alloc_ctor(1, 1, 0);\
lean_ctor_set(x_2, 0, x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Lsp_instFromJsonInitializedParams___closed__1_end;\
}\
l_Lean_Lsp_instFromJsonInitializedParams___closed__1_end: ((void) 0);}
lean_object* l_Lean_Lsp_instFromJsonInitializedParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFromJsonInitializedParams___closed__1;
return x_2;
}
}
lean_object* l_Lean_Lsp_instFromJsonInitializedParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFromJsonInitializedParams(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Lsp_instToJsonInitializedParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_Lsp_instToJsonInitializedParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instToJsonInitializedParams(x_1);
lean_dec(x_1);
return x_2;
}
}
#define _init_l_Lean_Lsp_ServerInfo_version_x3f___default(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_box(0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_ServerInfo_version_x3f___default_end;\
}\
l_Lean_Lsp_ServerInfo_version_x3f___default_end: ((void) 0);}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_465_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_1148____closed__1;
x_10 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonDocumentFilter____x40_Lean_Data_Lsp_Basic___hyg_1611____spec__1(x_9, x_3);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_List_join___rarg(x_12);
x_14 = l_Lean_Json_mkObj(x_13);
return x_14;
}
}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_465____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_465_(x_1);
lean_dec(x_1);
return x_2;
}
}
#define _init_l_Lean_Lsp_instToJsonServerInfo___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_465____boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instToJsonServerInfo___closed__1_end;\
}\
l_Lean_Lsp_instToJsonServerInfo___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_instToJsonServerInfo(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Lsp_instToJsonServerInfo___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instToJsonServerInfo_end;\
}\
l_Lean_Lsp_instToJsonServerInfo_end: ((void) 0);}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_494_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_1148____closed__1;
x_7 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonDocumentFilter____x40_Lean_Data_Lsp_Basic___hyg_1639____spec__1(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_494____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_494_(x_1);
lean_dec(x_1);
return x_2;
}
}
#define _init_l_Lean_Lsp_instFromJsonServerInfo___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_494____boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instFromJsonServerInfo___closed__1_end;\
}\
l_Lean_Lsp_instFromJsonServerInfo___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_instFromJsonServerInfo(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Lsp_instFromJsonServerInfo___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instFromJsonServerInfo_end;\
}\
l_Lean_Lsp_instFromJsonServerInfo_end: ((void) 0);}
#define _init_l_Lean_Lsp_InitializeResult_serverInfo_x3f___default(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_box(0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_InitializeResult_serverInfo_x3f___default_end;\
}\
l_Lean_Lsp_InitializeResult_serverInfo_x3f___default_end: ((void) 0);}
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_465_(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
#define _init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("serverInfo");\
__INIT_VAR__ = x_1; goto l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____closed__1_end;\
}\
l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____closed__1_end: ((void) 0);}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_115_(x_2);
x_4 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__5;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____closed__1;
x_10 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____spec__1(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_List_join___rarg(x_12);
x_14 = l_Lean_Json_mkObj(x_13);
return x_14;
}
}
lean_object* l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
#define _init_l_Lean_Lsp_instToJsonInitializeResult___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560_), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instToJsonInitializeResult___closed__1_end;\
}\
l_Lean_Lsp_instToJsonInitializeResult___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_instToJsonInitializeResult(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Lsp_instToJsonInitializeResult___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instToJsonInitializeResult_end;\
}\
l_Lean_Lsp_instToJsonInitializeResult_end: ((void) 0);}
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_197_(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_instFromJsonOption___rarg___closed__1;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonServerInfo____x40_Lean_Data_Lsp_InitShutdown___hyg_494_(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__5;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____closed__1;
x_7 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__2(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589_(x_1);
lean_dec(x_1);
return x_2;
}
}
#define _init_l_Lean_Lsp_instFromJsonInitializeResult___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_fromJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_589____boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instFromJsonInitializeResult___closed__1_end;\
}\
l_Lean_Lsp_instFromJsonInitializeResult___closed__1_end: ((void) 0);}
#define _init_l_Lean_Lsp_instFromJsonInitializeResult(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Lsp_instFromJsonInitializeResult___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Lsp_instFromJsonInitializeResult_end;\
}\
l_Lean_Lsp_instFromJsonInitializeResult_end: ((void) 0);}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Capabilities(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Workspace(lean_object*);
lean_object* initialize_Lean_Data_Json(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Lsp_InitShutdown(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Capabilities(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Workspace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
_init_l_Lean_Lsp_ClientInfo_version_x3f___default(l_Lean_Lsp_ClientInfo_version_x3f___default);
lean_mark_persistent(l_Lean_Lsp_ClientInfo_version_x3f___default);
_init_l_Lean_Lsp_instToJsonClientInfo___closed__1(l_Lean_Lsp_instToJsonClientInfo___closed__1);
lean_mark_persistent(l_Lean_Lsp_instToJsonClientInfo___closed__1);
_init_l_Lean_Lsp_instToJsonClientInfo(l_Lean_Lsp_instToJsonClientInfo);
lean_mark_persistent(l_Lean_Lsp_instToJsonClientInfo);
_init_l_Lean_Lsp_instFromJsonClientInfo___closed__1(l_Lean_Lsp_instFromJsonClientInfo___closed__1);
lean_mark_persistent(l_Lean_Lsp_instFromJsonClientInfo___closed__1);
_init_l_Lean_Lsp_instFromJsonClientInfo(l_Lean_Lsp_instFromJsonClientInfo);
lean_mark_persistent(l_Lean_Lsp_instFromJsonClientInfo);
_init_l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__1(l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__1);
lean_mark_persistent(l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__1);
_init_l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__2(l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__2);
lean_mark_persistent(l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__2);
_init_l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__3(l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__3);
lean_mark_persistent(l_Lean_Lsp_instFromJsonTrace_match__1___rarg___closed__3);
_init_l_Lean_Lsp_instFromJsonTrace___closed__1(l_Lean_Lsp_instFromJsonTrace___closed__1);
lean_mark_persistent(l_Lean_Lsp_instFromJsonTrace___closed__1);
_init_l_Lean_Lsp_instFromJsonTrace___closed__2(l_Lean_Lsp_instFromJsonTrace___closed__2);
lean_mark_persistent(l_Lean_Lsp_instFromJsonTrace___closed__2);
_init_l_Lean_Lsp_instFromJsonTrace___closed__3(l_Lean_Lsp_instFromJsonTrace___closed__3);
lean_mark_persistent(l_Lean_Lsp_instFromJsonTrace___closed__3);
_init_l_Lean_Lsp_Trace_hasToJson___closed__1(l_Lean_Lsp_Trace_hasToJson___closed__1);
lean_mark_persistent(l_Lean_Lsp_Trace_hasToJson___closed__1);
_init_l_Lean_Lsp_Trace_hasToJson___closed__2(l_Lean_Lsp_Trace_hasToJson___closed__2);
lean_mark_persistent(l_Lean_Lsp_Trace_hasToJson___closed__2);
_init_l_Lean_Lsp_Trace_hasToJson___closed__3(l_Lean_Lsp_Trace_hasToJson___closed__3);
lean_mark_persistent(l_Lean_Lsp_Trace_hasToJson___closed__3);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175____closed__1(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175____closed__1);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializationOptions____x40_Lean_Data_Lsp_InitShutdown___hyg_175____closed__1);
_init_l_Lean_Lsp_instToJsonInitializationOptions___closed__1(l_Lean_Lsp_instToJsonInitializationOptions___closed__1);
lean_mark_persistent(l_Lean_Lsp_instToJsonInitializationOptions___closed__1);
_init_l_Lean_Lsp_instToJsonInitializationOptions(l_Lean_Lsp_instToJsonInitializationOptions);
lean_mark_persistent(l_Lean_Lsp_instToJsonInitializationOptions);
_init_l_Lean_Lsp_instFromJsonInitializationOptions___closed__1(l_Lean_Lsp_instFromJsonInitializationOptions___closed__1);
lean_mark_persistent(l_Lean_Lsp_instFromJsonInitializationOptions___closed__1);
_init_l_Lean_Lsp_instFromJsonInitializationOptions(l_Lean_Lsp_instFromJsonInitializationOptions);
lean_mark_persistent(l_Lean_Lsp_instFromJsonInitializationOptions);
_init_l_Lean_Lsp_InitializeParams_processId_x3f___default(l_Lean_Lsp_InitializeParams_processId_x3f___default);
lean_mark_persistent(l_Lean_Lsp_InitializeParams_processId_x3f___default);
_init_l_Lean_Lsp_InitializeParams_clientInfo_x3f___default(l_Lean_Lsp_InitializeParams_clientInfo_x3f___default);
lean_mark_persistent(l_Lean_Lsp_InitializeParams_clientInfo_x3f___default);
_init_l_Lean_Lsp_InitializeParams_rootUri_x3f___default(l_Lean_Lsp_InitializeParams_rootUri_x3f___default);
lean_mark_persistent(l_Lean_Lsp_InitializeParams_rootUri_x3f___default);
_init_l_Lean_Lsp_InitializeParams_initializationOptions_x3f___default(l_Lean_Lsp_InitializeParams_initializationOptions_x3f___default);
lean_mark_persistent(l_Lean_Lsp_InitializeParams_initializationOptions_x3f___default);
_init_l_Lean_Lsp_InitializeParams_trace___default(l_Lean_Lsp_InitializeParams_trace___default);
_init_l_Lean_Lsp_InitializeParams_workspaceFolders_x3f___default(l_Lean_Lsp_InitializeParams_workspaceFolders_x3f___default);
lean_mark_persistent(l_Lean_Lsp_InitializeParams_workspaceFolders_x3f___default);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__1(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__1);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__1);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__2(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__2);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__2);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__3(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__3);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__3);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__4(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__4);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__4);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__5(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__5);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__5);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__6(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__6);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__6);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__7(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__7);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__7);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__8(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__8);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__8);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__9(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__9);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__9);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__10(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__10);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__10);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__11(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__11);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__11);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__12(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__12);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__12);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__13(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__13);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__13);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__14(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__14);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_298____closed__14);
_init_l_Lean_Lsp_instToJsonInitializeParams___closed__1(l_Lean_Lsp_instToJsonInitializeParams___closed__1);
lean_mark_persistent(l_Lean_Lsp_instToJsonInitializeParams___closed__1);
_init_l_Lean_Lsp_instToJsonInitializeParams(l_Lean_Lsp_instToJsonInitializeParams);
lean_mark_persistent(l_Lean_Lsp_instToJsonInitializeParams);
_init_l_Lean_Lsp_instFromJsonInitializedParams___closed__1(l_Lean_Lsp_instFromJsonInitializedParams___closed__1);
lean_mark_persistent(l_Lean_Lsp_instFromJsonInitializedParams___closed__1);
_init_l_Lean_Lsp_ServerInfo_version_x3f___default(l_Lean_Lsp_ServerInfo_version_x3f___default);
lean_mark_persistent(l_Lean_Lsp_ServerInfo_version_x3f___default);
_init_l_Lean_Lsp_instToJsonServerInfo___closed__1(l_Lean_Lsp_instToJsonServerInfo___closed__1);
lean_mark_persistent(l_Lean_Lsp_instToJsonServerInfo___closed__1);
_init_l_Lean_Lsp_instToJsonServerInfo(l_Lean_Lsp_instToJsonServerInfo);
lean_mark_persistent(l_Lean_Lsp_instToJsonServerInfo);
_init_l_Lean_Lsp_instFromJsonServerInfo___closed__1(l_Lean_Lsp_instFromJsonServerInfo___closed__1);
lean_mark_persistent(l_Lean_Lsp_instFromJsonServerInfo___closed__1);
_init_l_Lean_Lsp_instFromJsonServerInfo(l_Lean_Lsp_instFromJsonServerInfo);
lean_mark_persistent(l_Lean_Lsp_instFromJsonServerInfo);
_init_l_Lean_Lsp_InitializeResult_serverInfo_x3f___default(l_Lean_Lsp_InitializeResult_serverInfo_x3f___default);
lean_mark_persistent(l_Lean_Lsp_InitializeResult_serverInfo_x3f___default);
_init_l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____closed__1(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____closed__1);
lean_mark_persistent(l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_560____closed__1);
_init_l_Lean_Lsp_instToJsonInitializeResult___closed__1(l_Lean_Lsp_instToJsonInitializeResult___closed__1);
lean_mark_persistent(l_Lean_Lsp_instToJsonInitializeResult___closed__1);
_init_l_Lean_Lsp_instToJsonInitializeResult(l_Lean_Lsp_instToJsonInitializeResult);
lean_mark_persistent(l_Lean_Lsp_instToJsonInitializeResult);
_init_l_Lean_Lsp_instFromJsonInitializeResult___closed__1(l_Lean_Lsp_instFromJsonInitializeResult___closed__1);
lean_mark_persistent(l_Lean_Lsp_instFromJsonInitializeResult___closed__1);
_init_l_Lean_Lsp_instFromJsonInitializeResult(l_Lean_Lsp_instFromJsonInitializeResult);
lean_mark_persistent(l_Lean_Lsp_instFromJsonInitializeResult);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
