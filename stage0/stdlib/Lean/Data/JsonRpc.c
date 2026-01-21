// Lean compiler output
// Module: Lean.Data.JsonRpc
// Imports: public import Lean.Data.Json.Stream public import Lean.Data.Json.FromToJson.Basic
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_RequestID_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequestID;
LEAN_EXPORT uint64_t l_Lean_JsonRpc_instHashableRequestID_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22;
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default___redArg(lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToStringRequestID___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object*, uint8_t, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_metaData(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim___redArg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readMessage___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_toMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instOrdRequestID_ord(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOfNatRequestID(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode;
uint8_t l_Lean_instDecidableEqJsonNumber_decEq(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_lt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx(uint8_t);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12;
static lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequestID_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedErrorCode;
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__2;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessageKind___closed__0;
static lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4;
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedErrorCode_default;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID;
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1;
static lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedMessage_default;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim___redArg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_str_elim___redArg(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14;
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1;
static lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4;
static lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instLTRequestID;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object*);
static lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__3;
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqErrorCode_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequestID_default;
lean_object* l_IO_FS_Stream_readJson(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ofMessage_x3f(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instBEqRequestID___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedMessageDirection_default;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18;
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ltProp;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8;
static lean_object* l_Lean_JsonRpc_instToJsonMessageDirection___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx(uint8_t);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedMessage;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9;
static lean_object* l_Lean_JsonRpc_instHashableRequestID___closed__0;
static lean_object* l_IO_FS_Stream_readMessage___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequestID_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19;
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instBEqErrorCode___closed__0;
static lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1;
static lean_object* l_IO_FS_Stream_readNotificationAs___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx(uint8_t);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedMessageMetaData_default;
static lean_object* l_Lean_JsonRpc_instInhabitedMessage_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object*);
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default(lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object*, uint8_t, lean_object*, lean_object*);
uint64_t l_Lean_instHashableJsonNumber_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11;
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(lean_object*);
static lean_object* l_Lean_JsonRpc_instOrdRequestID___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageKind___closed__0;
static lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ofMessage_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(lean_object*);
lean_object* l_Option_toJson___redArg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__2;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
static lean_object* l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__5;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
static lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4;
static lean_object* l_Lean_JsonRpc_instCoeStringRequestID___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_strCore(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedMessageDirection;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instHashableRequestID_hash___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection;
lean_object* l_Lean_Json_Parser_num(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___redArg(lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instHashableRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__2;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID_ord___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14;
lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__0;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage;
lean_object* l_IO_FS_Stream_writeJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection;
static lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2;
uint8_t l_Lean_JsonNumber_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonRequestID___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
static lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0;
lean_object* lean_int_neg(lean_object*);
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg___boxed(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonRequestID___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ofMessage_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ofMessage_x3f(lean_object*);
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instInhabitedResponseError___closed__0;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedMessageMetaData;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3;
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID;
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_RequestID_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_JsonRpc_RequestID_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_JsonRpc_RequestID_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_str_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_RequestID_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_str_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_RequestID_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_RequestID_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_RequestID_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_RequestID_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_RequestID_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedRequestID_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instInhabitedRequestID_default;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequestID_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_string_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = l_Lean_instDecidableEqJsonNumber_decEq(x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequestID_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonRpc_instBEqRequestID_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqRequestID___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequestID_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instBEqRequestID___closed__0;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_JsonRpc_instHashableRequestID_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = lean_string_hash(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 1;
x_8 = l_Lean_instHashableJsonNumber_hash(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
default: 
{
uint64_t x_10; 
x_10 = 2;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instHashableRequestID_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_instHashableRequestID_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instHashableRequestID___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instHashableRequestID_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instHashableRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instHashableRequestID___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instOrdRequestID_ord(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_string_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_string_dec_eq(x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_9 = 0;
return x_9;
}
}
case 1:
{
uint8_t x_10; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = 0;
return x_10;
}
default: 
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = 0;
return x_11;
}
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_12; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = 2;
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_2);
lean_inc_ref(x_14);
lean_inc_ref(x_13);
x_15 = l_Lean_JsonNumber_lt(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_JsonNumber_lt(x_14, x_13);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = 2;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
x_19 = 0;
return x_19;
}
}
default: 
{
uint8_t x_20; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = 0;
return x_20;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = 2;
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonRpc_instOrdRequestID_ord(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonRpc_instOrdRequestID___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instOrdRequestID_ord___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instOrdRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instOrdRequestID___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOfNatRequestID(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonNumber_fromNat(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
x_4 = lean_string_append(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_string_append(x_4, x_3);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = l_Lean_JsonNumber_toString(x_6);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instToStringRequestID___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToStringRequestID___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToStringRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instToStringRequestID___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(8u);
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = lean_unsigned_to_nat(9u);
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(10u);
return x_12;
}
default: 
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(11u);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_JsonRpc_ErrorCode_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_JsonRpc_ErrorCode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_JsonRpc_ErrorCode_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_parseError_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_invalidParams_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_internalError_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_contentModified_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_workerExited_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode_default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqErrorCode_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_JsonRpc_ErrorCode_ctorIdx(x_1);
x_4 = l_Lean_JsonRpc_ErrorCode_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_JsonRpc_instBEqErrorCode_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqErrorCode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqErrorCode_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqErrorCode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instBEqErrorCode___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected error code", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32900u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32901u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 11;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 10;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 9;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 8;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 7;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 6;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 5;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 4;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3;
x_8 = lean_int_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5;
x_10 = lean_int_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7;
x_12 = lean_int_dec_eq(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9;
x_14 = lean_int_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11;
x_16 = lean_int_dec_eq(x_5, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13;
x_18 = lean_int_dec_eq(x_5, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15;
x_20 = lean_int_dec_eq(x_5, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17;
x_22 = lean_int_dec_eq(x_5, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19;
x_24 = lean_int_dec_eq(x_5, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21;
x_26 = lean_int_dec_eq(x_5, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23;
x_28 = lean_int_dec_eq(x_5, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25;
x_30 = lean_int_dec_eq(x_5, x_29);
if (x_30 == 0)
{
goto block_3;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_6, x_31);
if (x_32 == 0)
{
goto block_3;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26;
return x_33;
}
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_6, x_34);
if (x_35 == 0)
{
goto block_3;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27;
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_eq(x_6, x_37);
if (x_38 == 0)
{
goto block_3;
}
else
{
lean_object* x_39; 
x_39 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28;
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_6, x_40);
if (x_41 == 0)
{
goto block_3;
}
else
{
lean_object* x_42; 
x_42 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29;
return x_42;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_eq(x_6, x_43);
if (x_44 == 0)
{
goto block_3;
}
else
{
lean_object* x_45; 
x_45 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30;
return x_45;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_6, x_46);
if (x_47 == 0)
{
goto block_3;
}
else
{
lean_object* x_48; 
x_48 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31;
return x_48;
}
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_eq(x_6, x_49);
if (x_50 == 0)
{
goto block_3;
}
else
{
lean_object* x_51; 
x_51 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32;
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_eq(x_6, x_52);
if (x_53 == 0)
{
goto block_3;
}
else
{
lean_object* x_54; 
x_54 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33;
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_dec_eq(x_6, x_55);
if (x_56 == 0)
{
goto block_3;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34;
return x_57;
}
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_6, x_58);
if (x_59 == 0)
{
goto block_3;
}
else
{
lean_object* x_60; 
x_60 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35;
return x_60;
}
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_eq(x_6, x_61);
if (x_62 == 0)
{
goto block_3;
}
else
{
lean_object* x_63; 
x_63 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36;
return x_63;
}
}
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_nat_dec_eq(x_6, x_64);
if (x_65 == 0)
{
goto block_3;
}
else
{
lean_object* x_66; 
x_66 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37;
return x_66;
}
}
}
else
{
goto block_3;
}
block_3:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1;
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
return x_12;
}
default: 
{
lean_object* x_13; 
x_13 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_Message_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_2(x_2, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec_ref(x_1);
x_17 = lean_box(x_14);
x_18 = lean_apply_4(x_2, x_13, x_17, x_15, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_JsonRpc_Message_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_JsonRpc_Message_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_Message_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_Message_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_Message_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_Message_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_Message_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_Message_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_Message_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_Message_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedMessage_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
x_3 = l_Lean_JsonRpc_instInhabitedRequestID_default;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedMessage_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instInhabitedMessage_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedMessage() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instInhabitedMessage_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_JsonRpc_instInhabitedRequestID_default;
x_3 = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = l_Lean_JsonRpc_instBEqRequestID_beq(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_string_dec_eq(x_5, x_8);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_apply_2(x_1, x_6, x_9);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_JsonRpc_instBEqRequest_beq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_JsonRpc_instBEqRequest_beq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_JsonRpc_instBEqRequest_beq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_2, 2, x_6);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_ctor_set(x_2, 2, x_5);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_2, 2, x_9);
return x_2;
}
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_13 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_13);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_17 = x_13;
} else {
 lean_dec_ref(x_13);
 x_17 = lean_box(0);
}
if (lean_is_scalar(x_17)) {
 x_18 = lean_alloc_ctor(1, 1, 0);
} else {
 x_18 = x_17;
}
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Json_Structured_toJson(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ofMessage_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(x_3);
lean_ctor_set(x_1, 2, x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(x_8);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_string_dec_eq(x_4, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_apply_2(x_1, x_5, x_7);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_JsonRpc_instBEqNotification_beq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_JsonRpc_instBEqNotification_beq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_JsonRpc_instBEqNotification_beq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_5);
x_6 = lean_box(0);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_6);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_12);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_16 = x_12;
} else {
 lean_dec_ref(x_12);
 x_16 = lean_box(0);
}
if (lean_is_scalar(x_16)) {
 x_17 = lean_alloc_ctor(1, 1, 0);
} else {
 x_17 = x_16;
}
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ofMessage_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(x_3);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec_ref(x_1);
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_instInhabitedRequestID_default;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = l_Lean_JsonRpc_instBEqRequestID_beq(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_apply_2(x_1, x_5, x_7);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_JsonRpc_instBEqResponse_beq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_JsonRpc_instBEqResponse_beq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_JsonRpc_instBEqResponse_beq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set_tag(x_2, 2);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ofMessage_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_ctor_set_tag(x_1, 0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
x_3 = 0;
x_4 = l_Lean_JsonRpc_instInhabitedRequestID_default;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0;
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instInhabitedResponseError_default(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instInhabitedResponseError___closed__0;
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_10 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = l_Lean_JsonRpc_instBEqRequestID_beq(x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = l_Lean_JsonRpc_instBEqErrorCode_beq(x_5, x_9);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_string_dec_eq(x_6, x_10);
lean_dec_ref(x_10);
lean_dec_ref(x_6);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_1);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = l_Option_instBEq_beq___redArg(x_1, x_7, x_11);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_JsonRpc_instBEqResponseError_beq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 2);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 2, x_6);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_7);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_8);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 2);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_apply_1(x_1, x_15);
lean_ctor_set(x_3, 0, x_16);
lean_ctor_set_tag(x_2, 3);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_apply_1(x_1, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 2, x_19);
return x_2;
}
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_20);
lean_dec(x_2);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_24 = x_3;
} else {
 lean_dec_ref(x_3);
 x_24 = lean_box(0);
}
x_25 = lean_apply_1(x_1, x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_21);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 2, x_4);
return x_1;
}
else
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_6);
return x_9;
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ofMessage_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_ctor_set_tag(x_1, 0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec_ref(x_1);
x_10 = lean_box(0);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instCoeStringRequestID___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeStringRequestID___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instCoeStringRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instCoeStringRequestID___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instCoeJsonNumberRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_RequestID_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_string_dec_lt(x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = 0;
return x_6;
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
x_9 = l_Lean_JsonNumber_lt(x_7, x_8);
return x_9;
}
case 0:
{
uint8_t x_10; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = 1;
return x_10;
}
default: 
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = 0;
return x_11;
}
}
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 1:
{
uint8_t x_12; 
lean_dec_ref(x_2);
x_12 = 1;
return x_12;
}
case 0:
{
uint8_t x_13; 
lean_dec_ref(x_2);
x_13 = 1;
return x_13;
}
default: 
{
uint8_t x_14; 
lean_dec(x_2);
x_14 = 0;
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonRpc_RequestID_lt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonRpc_RequestID_ltProp() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instLTRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_JsonRpc_RequestID_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonRpc_instDecidableLtRequestID(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a request id needs to be a number or a string", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_ctor_set_tag(x_1, 0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
case 2:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_ctor_set_tag(x_1, 1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
default: 
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1;
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonRequestID___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instFromJsonRequestID___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 3);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
case 1:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_ctor_set_tag(x_1, 2);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
default: 
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonRequestID___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonRequestID___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instToJsonRequestID___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("jsonrpc", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("2.0", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2;
x_2 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("id", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("method", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("params", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("message", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("data", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
switch (lean_obj_tag(x_9)) {
case 0:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
lean_ctor_set_tag(x_9, 3);
x_13 = x_9;
goto block_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_13 = x_27;
goto block_24;
}
}
case 1:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
lean_ctor_set_tag(x_9, 2);
x_13 = x_9;
goto block_24;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
lean_dec(x_9);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_13 = x_30;
goto block_24;
}
}
default: 
{
lean_object* x_31; 
x_31 = lean_box(0);
x_13 = x_31;
goto block_24;
}
}
block_24:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_22 = l_Lean_Json_opt___redArg(x_1, x_21, x_11);
x_23 = l_List_appendTR___redArg(x_20, x_22);
x_5 = x_23;
goto block_8;
}
}
case 1:
{
uint8_t x_32; 
lean_dec_ref(x_2);
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 1);
x_35 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_36);
lean_ctor_set(x_3, 0, x_35);
x_37 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_38 = l_Lean_Json_opt___redArg(x_1, x_37, x_34);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_38);
x_5 = x_39;
goto block_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_42 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_46 = l_Lean_Json_opt___redArg(x_1, x_45, x_41);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_5 = x_47;
goto block_8;
}
}
case 2:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_50 = x_3;
} else {
 lean_dec_ref(x_3);
 x_50 = lean_box(0);
}
x_51 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
switch (lean_obj_tag(x_48)) {
case 0:
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
lean_ctor_set_tag(x_48, 3);
x_52 = x_48;
goto block_59;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_48, 0);
lean_inc(x_61);
lean_dec(x_48);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_52 = x_62;
goto block_59;
}
}
case 1:
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_48);
if (x_63 == 0)
{
lean_ctor_set_tag(x_48, 2);
x_52 = x_48;
goto block_59;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_48, 0);
lean_inc(x_64);
lean_dec(x_48);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_52 = x_65;
goto block_59;
}
}
default: 
{
lean_object* x_66; 
x_66 = lean_box(0);
x_52 = x_66;
goto block_59;
}
}
block_59:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
 lean_ctor_set_tag(x_53, 0);
}
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_5 = x_58;
goto block_8;
}
}
default: 
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_1);
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_69 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_3, 2);
lean_inc(x_70);
lean_dec_ref(x_3);
x_90 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
switch (lean_obj_tag(x_67)) {
case 0:
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_67);
if (x_108 == 0)
{
lean_ctor_set_tag(x_67, 3);
x_91 = x_67;
goto block_107;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_67, 0);
lean_inc(x_109);
lean_dec(x_67);
x_110 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_91 = x_110;
goto block_107;
}
}
case 1:
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_67);
if (x_111 == 0)
{
lean_ctor_set_tag(x_67, 2);
x_91 = x_67;
goto block_107;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_67, 0);
lean_inc(x_112);
lean_dec(x_67);
x_113 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_91 = x_113;
goto block_107;
}
}
default: 
{
lean_object* x_114; 
x_114 = lean_box(0);
x_91 = x_114;
goto block_107;
}
}
block_89:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_69);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_83 = l_Lean_Json_opt___redArg(x_2, x_82, x_70);
x_84 = l_List_appendTR___redArg(x_81, x_83);
x_85 = l_Lean_Json_mkObj(x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_71);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_87);
x_5 = x_88;
goto block_8;
}
block_107:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_94 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
switch (x_68) {
case 0:
{
lean_object* x_95; 
x_95 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_95;
goto block_89;
}
case 1:
{
lean_object* x_96; 
x_96 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_96;
goto block_89;
}
case 2:
{
lean_object* x_97; 
x_97 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_97;
goto block_89;
}
case 3:
{
lean_object* x_98; 
x_98 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_98;
goto block_89;
}
case 4:
{
lean_object* x_99; 
x_99 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_99;
goto block_89;
}
case 5:
{
lean_object* x_100; 
x_100 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_100;
goto block_89;
}
case 6:
{
lean_object* x_101; 
x_101 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_101;
goto block_89;
}
case 7:
{
lean_object* x_102; 
x_102 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_102;
goto block_89;
}
case 8:
{
lean_object* x_103; 
x_103 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_103;
goto block_89;
}
case 9:
{
lean_object* x_104; 
x_104 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_104;
goto block_89;
}
case 10:
{
lean_object* x_105; 
x_105 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_105;
goto block_89;
}
default: 
{
lean_object* x_106; 
x_106 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
x_71 = x_93;
x_72 = x_94;
x_73 = x_92;
x_74 = x_106;
goto block_89;
}
}
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Json_mkObj(x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Structured_toJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_2 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonMessage___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instToJsonMessage___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only version 2.0 of JSON RPC is supported", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
lean_inc(x_5);
x_21 = l_Lean_Json_getObjVal_x3f(x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec_ref(x_21);
if (lean_obj_tag(x_25) == 3)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
x_28 = lean_string_dec_eq(x_26, x_27);
lean_dec_ref(x_26);
if (x_28 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_7;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
lean_inc(x_5);
x_30 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_1, x_29);
if (lean_obj_tag(x_30) == 0)
{
goto block_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_30, 0);
lean_inc(x_82);
x_83 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc_ref(x_3);
lean_inc(x_5);
x_84 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_3, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_84);
lean_dec(x_82);
goto block_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_30);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_91 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_92 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_4, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
lean_dec_ref(x_92);
x_93 = lean_box(0);
x_87 = x_93;
goto block_90;
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
x_87 = x_92;
goto block_90;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_87 = x_96;
goto block_90;
}
}
block_90:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_85);
lean_ctor_set(x_88, 2, x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
block_62:
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec_ref(x_30);
x_35 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_36 = l_Lean_Json_getObjVal_x3f(x_5, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_34);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec_ref(x_36);
x_41 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
lean_inc(x_40);
x_42 = l_Lean_Json_getObjValAs_x3f___redArg(x_40, x_2, x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_40);
lean_dec(x_34);
lean_dec_ref(x_3);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec_ref(x_42);
x_47 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
lean_inc(x_40);
x_48 = l_Lean_Json_getObjValAs_x3f___redArg(x_40, x_3, x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_46);
lean_dec(x_40);
lean_dec(x_34);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
lean_dec_ref(x_48);
x_53 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_54 = l_Lean_Json_getObjVal_x3f(x_40, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
lean_dec_ref(x_54);
x_55 = lean_box(0);
x_56 = lean_unbox(x_46);
lean_dec(x_46);
x_8 = x_34;
x_9 = x_52;
x_10 = x_56;
x_11 = x_55;
goto block_14;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = lean_unbox(x_46);
lean_dec(x_46);
x_8 = x_34;
x_9 = x_52;
x_10 = x_58;
x_11 = x_54;
goto block_14;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_unbox(x_46);
lean_dec(x_46);
x_8 = x_34;
x_9 = x_52;
x_10 = x_61;
x_11 = x_60;
goto block_14;
}
}
}
}
}
}
}
block_81:
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc_ref(x_3);
lean_inc(x_5);
x_64 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_3, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
lean_dec_ref(x_4);
if (lean_obj_tag(x_30) == 0)
{
goto block_62;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_30, 0);
lean_inc(x_65);
x_66 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
lean_inc(x_5);
x_67 = l_Lean_Json_getObjVal_x3f(x_5, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_dec_ref(x_67);
lean_dec(x_65);
goto block_62;
}
else
{
uint8_t x_68; 
lean_dec_ref(x_30);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_67, 0, x_70);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_30);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
lean_dec_ref(x_64);
x_75 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_76 = l_Lean_Json_getObjValAs_x3f___redArg(x_5, x_4, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
lean_dec_ref(x_76);
x_77 = lean_box(0);
x_15 = x_74;
x_16 = x_77;
goto block_19;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
x_15 = x_74;
x_16 = x_76;
goto block_19;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_15 = x_74;
x_16 = x_80;
goto block_19;
}
}
}
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_7;
}
}
block_7:
{
lean_object* x_6; 
x_6 = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1;
return x_6;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getStr_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Structured_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_JsonRpc_instFromJsonMessage___closed__1;
x_2 = l_Lean_JsonRpc_instFromJsonMessage___closed__0;
x_3 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__0;
x_4 = l_Lean_JsonRpc_instFromJsonRequestID___closed__0;
x_5 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0), 5, 4);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instFromJsonMessage___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not a notification", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
lean_inc(x_3);
x_23 = l_Lean_Json_getObjVal_x3f(x_3, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec_ref(x_23);
if (lean_obj_tag(x_27) == 3)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
x_30 = lean_string_dec_eq(x_28, x_29);
lean_dec_ref(x_28);
if (x_30 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = l_Lean_JsonRpc_instFromJsonRequestID___closed__0;
x_32 = l_Lean_JsonRpc_instFromJsonMessage___closed__0;
x_33 = l_Lean_JsonRpc_instFromJsonMessage___closed__1;
x_34 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__0;
x_35 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
lean_inc(x_3);
x_36 = l_Lean_Json_getObjValAs_x3f___redArg(x_3, x_31, x_35);
if (lean_obj_tag(x_36) == 0)
{
goto block_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_3);
x_70 = l_Lean_Json_getObjValAs_x3f___redArg(x_3, x_32, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_dec_ref(x_70);
goto block_68;
}
else
{
lean_dec_ref(x_70);
lean_dec_ref(x_36);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_5;
}
}
block_56:
{
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_36);
x_40 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_41 = l_Lean_Json_getObjVal_x3f(x_3, x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec_ref(x_41);
x_46 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
lean_inc(x_45);
x_47 = l_Lean_Json_getObjValAs_x3f___redArg(x_45, x_34, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_47);
x_51 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
x_52 = l_Lean_Json_getObjValAs_x3f___redArg(x_45, x_32, x_51);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
lean_dec_ref(x_52);
goto block_5;
}
}
}
}
}
block_68:
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_3);
x_58 = l_Lean_Json_getObjValAs_x3f___redArg(x_3, x_32, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_obj_tag(x_36) == 0)
{
goto block_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
lean_inc(x_3);
x_60 = l_Lean_Json_getObjVal_x3f(x_3, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_dec_ref(x_60);
goto block_56;
}
else
{
lean_dec_ref(x_60);
lean_dec_ref(x_36);
lean_dec(x_3);
goto block_5;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_36);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec_ref(x_58);
x_62 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_63 = l_Lean_Json_getObjValAs_x3f___redArg(x_3, x_33, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec_ref(x_63);
x_64 = lean_box(0);
x_6 = x_61;
x_7 = x_64;
goto block_19;
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
x_6 = x_61;
x_7 = x_63;
goto block_19;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_6 = x_61;
x_7 = x_67;
goto block_19;
}
}
}
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_21;
}
}
block_5:
{
lean_object* x_4; 
x_4 = l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1;
return x_4;
}
block_19:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Option_toJson___redArg(x_1, x_7);
x_9 = lean_apply_1(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
block_21:
{
lean_object* x_20; 
x_20 = l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2;
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instFromJsonNotification___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_MessageMetaData_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
default: 
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_box(x_11);
x_15 = lean_apply_4(x_2, x_10, x_14, x_12, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_JsonRpc_MessageMetaData_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
x_2 = l_Lean_JsonRpc_instInhabitedRequestID_default;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedMessageMetaData_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedMessageMetaData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instInhabitedMessageMetaData_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_metaData(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
default: 
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
return x_1;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_1);
x_14 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_11);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_toMessage(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
default: 
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
return x_1;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_dec(x_1);
x_17 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_14);
return x_17;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected \"", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get_fast(x_2, x_3);
x_7 = 34;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
if (x_5 == 0)
{
uint8_t x_11; 
lean_inc(x_3);
lean_inc(x_2);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_14);
x_15 = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
x_16 = l_Lean_Json_Parser_strCore(x_15, x_1);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_17 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
x_20 = l_Lean_Json_Parser_strCore(x_19, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc_ref(x_1);
x_2 = l_Lean_Json_Parser_num(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec_ref(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
return x_2;
}
else
{
lean_object* x_16; 
lean_inc(x_14);
lean_free_object(x_2);
lean_dec(x_12);
x_16 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_16, 1, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_nat_dec_eq(x_14, x_27);
lean_dec(x_14);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_16);
lean_dec(x_26);
x_29 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
x_30 = l_Std_Internal_Parsec_String_pstring(x_29, x_25);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 1);
lean_dec(x_32);
x_33 = lean_box(2);
lean_ctor_set(x_30, 1, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_ctor_get(x_41, 1);
x_44 = lean_nat_dec_eq(x_14, x_43);
lean_dec(x_14);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
x_46 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
x_47 = l_Std_Internal_Parsec_String_pstring(x_46, x_41);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(2);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_54 = x_47;
} else {
 lean_dec_ref(x_47);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_2);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_56, 1);
x_60 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
else
{
lean_object* x_62; 
lean_inc(x_59);
lean_dec(x_57);
x_62 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_56);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_59);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_64);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_68, 1);
x_72 = lean_nat_dec_eq(x_59, x_71);
lean_dec(x_59);
if (x_72 == 0)
{
lean_object* x_73; 
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
x_75 = l_Std_Internal_Parsec_String_pstring(x_74, x_68);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_box(2);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 3:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_ctor_set_tag(x_3, 0);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 2:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_ctor_set_tag(x_3, 1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
default: 
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1;
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3;
x_10 = lean_int_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5;
x_12 = lean_int_dec_eq(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7;
x_14 = lean_int_dec_eq(x_7, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9;
x_16 = lean_int_dec_eq(x_7, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11;
x_18 = lean_int_dec_eq(x_7, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13;
x_20 = lean_int_dec_eq(x_7, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15;
x_22 = lean_int_dec_eq(x_7, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17;
x_24 = lean_int_dec_eq(x_7, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19;
x_26 = lean_int_dec_eq(x_7, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21;
x_28 = lean_int_dec_eq(x_7, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23;
x_30 = lean_int_dec_eq(x_7, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25;
x_32 = lean_int_dec_eq(x_7, x_31);
lean_dec(x_7);
if (x_32 == 0)
{
lean_dec(x_8);
goto block_4;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_8, x_33);
lean_dec(x_8);
if (x_34 == 0)
{
goto block_4;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26;
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_7);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_8, x_36);
lean_dec(x_8);
if (x_37 == 0)
{
goto block_4;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27;
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_7);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_eq(x_8, x_39);
lean_dec(x_8);
if (x_40 == 0)
{
goto block_4;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28;
return x_41;
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_7);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_eq(x_8, x_42);
lean_dec(x_8);
if (x_43 == 0)
{
goto block_4;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29;
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_7);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_eq(x_8, x_45);
lean_dec(x_8);
if (x_46 == 0)
{
goto block_4;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30;
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_7);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_8, x_48);
lean_dec(x_8);
if (x_49 == 0)
{
goto block_4;
}
else
{
lean_object* x_50; 
x_50 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31;
return x_50;
}
}
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_7);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_8, x_51);
lean_dec(x_8);
if (x_52 == 0)
{
goto block_4;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32;
return x_53;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_7);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_8, x_54);
lean_dec(x_8);
if (x_55 == 0)
{
goto block_4;
}
else
{
lean_object* x_56; 
x_56 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33;
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_7);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_dec_eq(x_8, x_57);
lean_dec(x_8);
if (x_58 == 0)
{
goto block_4;
}
else
{
lean_object* x_59; 
x_59 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34;
return x_59;
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
lean_dec(x_7);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_eq(x_8, x_60);
lean_dec(x_8);
if (x_61 == 0)
{
goto block_4;
}
else
{
lean_object* x_62; 
x_62 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35;
return x_62;
}
}
}
else
{
lean_object* x_63; uint8_t x_64; 
lean_dec(x_7);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_nat_dec_eq(x_8, x_63);
lean_dec(x_8);
if (x_64 == 0)
{
goto block_4;
}
else
{
lean_object* x_65; 
x_65 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36;
return x_65;
}
}
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_7);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_8, x_66);
lean_dec(x_8);
if (x_67 == 0)
{
goto block_4;
}
else
{
lean_object* x_68; 
x_68 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37;
return x_68;
}
}
}
else
{
lean_dec(x_5);
goto block_4;
}
block_4:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected response error message kind", 36, 36);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected `id`, `jsonrpc` or `error` field", 41, 41);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected `method` or `result` field", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_string_utf8_byte_size(x_20);
x_23 = lean_nat_dec_eq(x_21, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_inc(x_21);
lean_inc(x_20);
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = lean_string_utf8_next_fast(x_20, x_21);
lean_dec(x_21);
lean_ctor_set(x_2, 1, x_27);
x_28 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_2);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
x_34 = lean_string_utf8_byte_size(x_32);
x_35 = lean_nat_dec_eq(x_33, x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_inc(x_33);
lean_inc(x_32);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_50; lean_object* x_56; uint8_t x_57; 
x_37 = lean_ctor_get(x_29, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_dec(x_38);
x_39 = lean_string_utf8_next_fast(x_32, x_33);
lean_dec(x_33);
lean_ctor_set(x_29, 1, x_39);
x_56 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
x_57 = lean_string_dec_eq(x_30, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
x_59 = lean_string_dec_eq(x_30, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_61 = lean_string_dec_eq(x_30, x_60);
lean_dec(x_30);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_31);
lean_dec_ref(x_1);
x_62 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_29);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
else
{
lean_object* x_64; 
x_64 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
lean_dec(x_31);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_ctor_set_tag(x_64, 1);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_29);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_29);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
lean_dec_ref(x_64);
lean_inc(x_70);
x_71 = l_Lean_Json_getObjVal_x3f(x_70, x_58);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_dec(x_70);
lean_dec(x_31);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_50 = x_72;
goto block_53;
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec_ref(x_71);
if (lean_obj_tag(x_73) == 3)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
x_76 = lean_string_dec_eq(x_74, x_75);
lean_dec_ref(x_74);
if (x_76 == 0)
{
lean_dec(x_70);
lean_dec(x_31);
goto block_55;
}
else
{
lean_object* x_77; 
lean_inc(x_70);
x_77 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(x_70, x_56);
if (lean_obj_tag(x_77) == 0)
{
goto block_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_70);
x_107 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_70, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_dec_ref(x_107);
goto block_105;
}
else
{
lean_dec_ref(x_107);
lean_dec_ref(x_77);
lean_dec(x_70);
lean_dec(x_31);
goto block_49;
}
}
block_100:
{
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
lean_dec(x_70);
lean_dec(x_31);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_50 = x_78;
goto block_53;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = l_Lean_Json_getObjVal_x3f(x_70, x_60);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
lean_dec(x_79);
lean_dec(x_31);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_50 = x_81;
goto block_53;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec_ref(x_80);
x_83 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
lean_inc(x_82);
x_84 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(x_82, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_31);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_50 = x_85;
goto block_53;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
lean_inc(x_82);
x_88 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_82, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_31);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_50 = x_89;
goto block_53;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec_ref(x_88);
x_91 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_92 = l_Lean_Json_getObjVal_x3f(x_82, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
lean_dec_ref(x_92);
x_93 = lean_box(0);
x_94 = lean_unbox(x_86);
lean_dec(x_86);
x_40 = x_79;
x_41 = x_94;
x_42 = x_90;
x_43 = x_93;
goto block_46;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_92);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = lean_unbox(x_86);
lean_dec(x_86);
x_40 = x_79;
x_41 = x_96;
x_42 = x_90;
x_43 = x_92;
goto block_46;
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
lean_dec(x_92);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_unbox(x_86);
lean_dec(x_86);
x_40 = x_79;
x_41 = x_99;
x_42 = x_90;
x_43 = x_98;
goto block_46;
}
}
}
}
}
}
}
block_105:
{
lean_object* x_101; lean_object* x_102; 
x_101 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_70);
x_102 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_70, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_dec_ref(x_102);
if (lean_obj_tag(x_77) == 0)
{
goto block_100;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
lean_inc(x_70);
x_104 = l_Lean_Json_getObjVal_x3f(x_70, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_dec_ref(x_104);
goto block_100;
}
else
{
lean_dec_ref(x_104);
lean_dec_ref(x_77);
lean_dec(x_70);
lean_dec(x_31);
goto block_49;
}
}
}
else
{
lean_dec_ref(x_102);
lean_dec_ref(x_77);
lean_dec(x_70);
lean_dec(x_31);
goto block_49;
}
}
}
}
else
{
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_31);
goto block_55;
}
}
}
}
}
else
{
lean_object* x_108; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_108 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_29);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_156; uint8_t x_157; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
x_156 = lean_string_utf8_byte_size(x_111);
x_157 = lean_nat_dec_eq(x_112, x_156);
if (x_157 == 0)
{
x_113 = x_59;
goto block_155;
}
else
{
x_113 = x_57;
goto block_155;
}
block_155:
{
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_box(0);
if (lean_is_scalar(x_110)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_110;
 lean_ctor_set_tag(x_115, 1);
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
else
{
uint8_t x_116; 
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_110);
x_116 = !lean_is_exclusive(x_109);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_109, 1);
lean_dec(x_117);
x_118 = lean_ctor_get(x_109, 0);
lean_dec(x_118);
x_119 = lean_string_utf8_next_fast(x_111, x_112);
lean_dec(x_112);
lean_ctor_set(x_109, 1, x_119);
x_120 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_109);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
lean_dec(x_123);
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_ctor_get(x_122, 1);
x_126 = lean_string_utf8_byte_size(x_124);
x_127 = lean_nat_dec_eq(x_125, x_126);
if (x_127 == 0)
{
lean_inc(x_125);
lean_inc(x_124);
lean_free_object(x_120);
lean_dec(x_122);
x_3 = x_125;
x_4 = x_124;
goto block_19;
}
else
{
if (x_57 == 0)
{
lean_object* x_128; 
x_128 = lean_box(0);
lean_ctor_set_tag(x_120, 1);
lean_ctor_set(x_120, 1, x_128);
return x_120;
}
else
{
lean_inc(x_125);
lean_inc(x_124);
lean_free_object(x_120);
lean_dec(x_122);
x_3 = x_125;
x_4 = x_124;
goto block_19;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_120, 0);
lean_inc(x_129);
lean_dec(x_120);
x_130 = lean_ctor_get(x_129, 0);
x_131 = lean_ctor_get(x_129, 1);
x_132 = lean_string_utf8_byte_size(x_130);
x_133 = lean_nat_dec_eq(x_131, x_132);
if (x_133 == 0)
{
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_129);
x_3 = x_131;
x_4 = x_130;
goto block_19;
}
else
{
if (x_57 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
else
{
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_129);
x_3 = x_131;
x_4 = x_130;
goto block_19;
}
}
}
}
else
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_120);
if (x_136 == 0)
{
return x_120;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_120, 0);
x_138 = lean_ctor_get(x_120, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_120);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_109);
x_140 = lean_string_utf8_next_fast(x_111, x_112);
lean_dec(x_112);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_111);
lean_ctor_set(x_141, 1, x_140);
x_142 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_143, 1);
x_147 = lean_string_utf8_byte_size(x_145);
x_148 = lean_nat_dec_eq(x_146, x_147);
if (x_148 == 0)
{
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_144);
lean_dec(x_143);
x_3 = x_146;
x_4 = x_145;
goto block_19;
}
else
{
if (x_57 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_144;
 lean_ctor_set_tag(x_150, 1);
}
lean_ctor_set(x_150, 0, x_143);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
else
{
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_144);
lean_dec(x_143);
x_3 = x_146;
x_4 = x_145;
goto block_19;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_142, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_142, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_153 = x_142;
} else {
 lean_dec_ref(x_142);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
}
}
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_108);
if (x_158 == 0)
{
return x_108;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_108, 0);
x_160 = lean_ctor_get(x_108, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_108);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
else
{
lean_object* x_162; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_162 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(x_29);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
x_169 = lean_ctor_get(x_163, 0);
x_170 = lean_ctor_get(x_163, 1);
x_171 = lean_string_utf8_byte_size(x_169);
x_172 = lean_nat_dec_eq(x_170, x_171);
if (x_172 == 0)
{
if (x_57 == 0)
{
lean_dec(x_164);
goto block_168;
}
else
{
uint8_t x_173; 
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_165);
x_173 = !lean_is_exclusive(x_163);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_163, 1);
lean_dec(x_174);
x_175 = lean_ctor_get(x_163, 0);
lean_dec(x_175);
x_176 = lean_string_utf8_next_fast(x_169, x_170);
lean_dec(x_170);
lean_ctor_set(x_163, 1, x_176);
x_177 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_163);
if (lean_obj_tag(x_177) == 0)
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_179 = lean_ctor_get(x_177, 0);
x_180 = lean_ctor_get(x_177, 1);
lean_dec(x_180);
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_ctor_get(x_179, 1);
x_183 = lean_string_utf8_byte_size(x_181);
x_184 = lean_nat_dec_eq(x_182, x_183);
if (x_184 == 0)
{
uint8_t x_185; 
lean_inc(x_182);
lean_inc(x_181);
lean_free_object(x_177);
x_185 = !lean_is_exclusive(x_179);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_179, 1);
lean_dec(x_186);
x_187 = lean_ctor_get(x_179, 0);
lean_dec(x_187);
x_188 = lean_string_utf8_next_fast(x_181, x_182);
lean_dec(x_182);
lean_ctor_set(x_179, 1, x_188);
x_189 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_179);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_191 = lean_ctor_get(x_189, 0);
x_192 = lean_ctor_get(x_189, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_191, 0);
x_194 = lean_ctor_get(x_191, 1);
x_195 = lean_string_utf8_byte_size(x_193);
x_196 = lean_nat_dec_eq(x_194, x_195);
if (x_196 == 0)
{
uint8_t x_197; 
lean_inc(x_194);
lean_inc(x_193);
x_197 = !lean_is_exclusive(x_191);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_191, 1);
lean_dec(x_198);
x_199 = lean_ctor_get(x_191, 0);
lean_dec(x_199);
x_200 = lean_string_utf8_next_fast(x_193, x_194);
lean_dec(x_194);
lean_ctor_set(x_191, 1, x_200);
x_201 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_191);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_208; uint8_t x_209; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_204 = x_201;
} else {
 lean_dec_ref(x_201);
 x_204 = lean_box(0);
}
x_208 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_209 = lean_string_dec_eq(x_203, x_208);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; 
lean_dec(x_204);
x_210 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_211 = lean_string_dec_eq(x_203, x_210);
lean_dec(x_203);
if (x_211 == 0)
{
lean_object* x_212; 
lean_dec(x_164);
x_212 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
lean_ctor_set_tag(x_189, 1);
lean_ctor_set(x_189, 1, x_212);
lean_ctor_set(x_189, 0, x_202);
return x_189;
}
else
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_213, 0, x_164);
lean_ctor_set(x_189, 1, x_213);
lean_ctor_set(x_189, 0, x_202);
return x_189;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
lean_dec(x_203);
lean_free_object(x_189);
x_214 = lean_ctor_get(x_202, 0);
x_215 = lean_ctor_get(x_202, 1);
x_216 = lean_string_utf8_byte_size(x_214);
x_217 = lean_nat_dec_eq(x_215, x_216);
if (x_217 == 0)
{
if (x_209 == 0)
{
lean_dec(x_164);
goto block_207;
}
else
{
uint8_t x_218; 
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_204);
x_218 = !lean_is_exclusive(x_202);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = lean_ctor_get(x_202, 1);
lean_dec(x_219);
x_220 = lean_ctor_get(x_202, 0);
lean_dec(x_220);
x_221 = lean_string_utf8_next_fast(x_214, x_215);
lean_dec(x_215);
lean_ctor_set(x_202, 1, x_221);
x_222 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_202);
if (lean_obj_tag(x_222) == 0)
{
uint8_t x_223; 
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_222, 1);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_164);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_222, 1, x_225);
return x_222;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_222, 0);
x_227 = lean_ctor_get(x_222, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_222);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_164);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
else
{
uint8_t x_230; 
lean_dec(x_164);
x_230 = !lean_is_exclusive(x_222);
if (x_230 == 0)
{
return x_222;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_222, 0);
x_232 = lean_ctor_get(x_222, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_222);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_202);
x_234 = lean_string_utf8_next_fast(x_214, x_215);
lean_dec(x_215);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_214);
lean_ctor_set(x_235, 1, x_234);
x_236 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_235);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_164);
lean_ctor_set(x_240, 1, x_238);
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_239;
}
lean_ctor_set(x_241, 0, x_237);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_164);
x_242 = lean_ctor_get(x_236, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_236, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_244 = x_236;
} else {
 lean_dec_ref(x_236);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
}
else
{
lean_dec(x_164);
goto block_207;
}
}
block_207:
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_box(0);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_204;
 lean_ctor_set_tag(x_206, 1);
}
lean_ctor_set(x_206, 0, x_202);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
else
{
uint8_t x_246; 
lean_free_object(x_189);
lean_dec(x_164);
x_246 = !lean_is_exclusive(x_201);
if (x_246 == 0)
{
return x_201;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_201, 0);
x_248 = lean_ctor_get(x_201, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_201);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_191);
x_250 = lean_string_utf8_next_fast(x_193, x_194);
lean_dec(x_194);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_193);
lean_ctor_set(x_251, 1, x_250);
x_252 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_251);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_259; uint8_t x_260; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_255 = x_252;
} else {
 lean_dec_ref(x_252);
 x_255 = lean_box(0);
}
x_259 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_260 = lean_string_dec_eq(x_254, x_259);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; 
lean_dec(x_255);
x_261 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_262 = lean_string_dec_eq(x_254, x_261);
lean_dec(x_254);
if (x_262 == 0)
{
lean_object* x_263; 
lean_dec(x_164);
x_263 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
lean_ctor_set_tag(x_189, 1);
lean_ctor_set(x_189, 1, x_263);
lean_ctor_set(x_189, 0, x_253);
return x_189;
}
else
{
lean_object* x_264; 
x_264 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_264, 0, x_164);
lean_ctor_set(x_189, 1, x_264);
lean_ctor_set(x_189, 0, x_253);
return x_189;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
lean_dec(x_254);
lean_free_object(x_189);
x_265 = lean_ctor_get(x_253, 0);
x_266 = lean_ctor_get(x_253, 1);
x_267 = lean_string_utf8_byte_size(x_265);
x_268 = lean_nat_dec_eq(x_266, x_267);
if (x_268 == 0)
{
if (x_260 == 0)
{
lean_dec(x_164);
goto block_258;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_255);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_269 = x_253;
} else {
 lean_dec_ref(x_253);
 x_269 = lean_box(0);
}
x_270 = lean_string_utf8_next_fast(x_265, x_266);
lean_dec(x_266);
if (lean_is_scalar(x_269)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_269;
}
lean_ctor_set(x_271, 0, x_265);
lean_ctor_set(x_271, 1, x_270);
x_272 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_164);
lean_ctor_set(x_276, 1, x_274);
if (lean_is_scalar(x_275)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_275;
}
lean_ctor_set(x_277, 0, x_273);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_164);
x_278 = lean_ctor_get(x_272, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_272, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_280 = x_272;
} else {
 lean_dec_ref(x_272);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
}
else
{
lean_dec(x_164);
goto block_258;
}
}
block_258:
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_box(0);
if (lean_is_scalar(x_255)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_255;
 lean_ctor_set_tag(x_257, 1);
}
lean_ctor_set(x_257, 0, x_253);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_free_object(x_189);
lean_dec(x_164);
x_282 = lean_ctor_get(x_252, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_252, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_284 = x_252;
} else {
 lean_dec_ref(x_252);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
}
else
{
lean_object* x_286; 
lean_dec(x_164);
x_286 = lean_box(0);
lean_ctor_set_tag(x_189, 1);
lean_ctor_set(x_189, 1, x_286);
return x_189;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_287 = lean_ctor_get(x_189, 0);
lean_inc(x_287);
lean_dec(x_189);
x_288 = lean_ctor_get(x_287, 0);
x_289 = lean_ctor_get(x_287, 1);
x_290 = lean_string_utf8_byte_size(x_288);
x_291 = lean_nat_dec_eq(x_289, x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_inc(x_289);
lean_inc(x_288);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_292 = x_287;
} else {
 lean_dec_ref(x_287);
 x_292 = lean_box(0);
}
x_293 = lean_string_utf8_next_fast(x_288, x_289);
lean_dec(x_289);
if (lean_is_scalar(x_292)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_292;
}
lean_ctor_set(x_294, 0, x_288);
lean_ctor_set(x_294, 1, x_293);
x_295 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_302; uint8_t x_303; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_298 = x_295;
} else {
 lean_dec_ref(x_295);
 x_298 = lean_box(0);
}
x_302 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_303 = lean_string_dec_eq(x_297, x_302);
if (x_303 == 0)
{
lean_object* x_304; uint8_t x_305; 
lean_dec(x_298);
x_304 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_305 = lean_string_dec_eq(x_297, x_304);
lean_dec(x_297);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_164);
x_306 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_296);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_308, 0, x_164);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_296);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
lean_dec(x_297);
x_310 = lean_ctor_get(x_296, 0);
x_311 = lean_ctor_get(x_296, 1);
x_312 = lean_string_utf8_byte_size(x_310);
x_313 = lean_nat_dec_eq(x_311, x_312);
if (x_313 == 0)
{
if (x_303 == 0)
{
lean_dec(x_164);
goto block_301;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_298);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_314 = x_296;
} else {
 lean_dec_ref(x_296);
 x_314 = lean_box(0);
}
x_315 = lean_string_utf8_next_fast(x_310, x_311);
lean_dec(x_311);
if (lean_is_scalar(x_314)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_314;
}
lean_ctor_set(x_316, 0, x_310);
lean_ctor_set(x_316, 1, x_315);
x_317 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_316);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_320 = x_317;
} else {
 lean_dec_ref(x_317);
 x_320 = lean_box(0);
}
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_164);
lean_ctor_set(x_321, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_320;
}
lean_ctor_set(x_322, 0, x_318);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_164);
x_323 = lean_ctor_get(x_317, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_317, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_325 = x_317;
} else {
 lean_dec_ref(x_317);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
}
else
{
lean_dec(x_164);
goto block_301;
}
}
block_301:
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_box(0);
if (lean_is_scalar(x_298)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_298;
 lean_ctor_set_tag(x_300, 1);
}
lean_ctor_set(x_300, 0, x_296);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_164);
x_327 = lean_ctor_get(x_295, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_295, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_329 = x_295;
} else {
 lean_dec_ref(x_295);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_164);
x_331 = lean_box(0);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_287);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
else
{
uint8_t x_333; 
lean_dec(x_164);
x_333 = !lean_is_exclusive(x_189);
if (x_333 == 0)
{
return x_189;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_189, 0);
x_335 = lean_ctor_get(x_189, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_189);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_179);
x_337 = lean_string_utf8_next_fast(x_181, x_182);
lean_dec(x_182);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_181);
lean_ctor_set(x_338, 1, x_337);
x_339 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_338);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_341 = x_339;
} else {
 lean_dec_ref(x_339);
 x_341 = lean_box(0);
}
x_342 = lean_ctor_get(x_340, 0);
x_343 = lean_ctor_get(x_340, 1);
x_344 = lean_string_utf8_byte_size(x_342);
x_345 = lean_nat_dec_eq(x_343, x_344);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_inc(x_343);
lean_inc(x_342);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_346 = x_340;
} else {
 lean_dec_ref(x_340);
 x_346 = lean_box(0);
}
x_347 = lean_string_utf8_next_fast(x_342, x_343);
lean_dec(x_343);
if (lean_is_scalar(x_346)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_346;
}
lean_ctor_set(x_348, 0, x_342);
lean_ctor_set(x_348, 1, x_347);
x_349 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_348);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_356; uint8_t x_357; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_352 = x_349;
} else {
 lean_dec_ref(x_349);
 x_352 = lean_box(0);
}
x_356 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_357 = lean_string_dec_eq(x_351, x_356);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; 
lean_dec(x_352);
x_358 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_359 = lean_string_dec_eq(x_351, x_358);
lean_dec(x_351);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_164);
x_360 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_341)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_341;
 lean_ctor_set_tag(x_361, 1);
}
lean_ctor_set(x_361, 0, x_350);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
else
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_362, 0, x_164);
if (lean_is_scalar(x_341)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_341;
}
lean_ctor_set(x_363, 0, x_350);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; 
lean_dec(x_351);
lean_dec(x_341);
x_364 = lean_ctor_get(x_350, 0);
x_365 = lean_ctor_get(x_350, 1);
x_366 = lean_string_utf8_byte_size(x_364);
x_367 = lean_nat_dec_eq(x_365, x_366);
if (x_367 == 0)
{
if (x_357 == 0)
{
lean_dec(x_164);
goto block_355;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_352);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_368 = x_350;
} else {
 lean_dec_ref(x_350);
 x_368 = lean_box(0);
}
x_369 = lean_string_utf8_next_fast(x_364, x_365);
lean_dec(x_365);
if (lean_is_scalar(x_368)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_368;
}
lean_ctor_set(x_370, 0, x_364);
lean_ctor_set(x_370, 1, x_369);
x_371 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_370);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_374 = x_371;
} else {
 lean_dec_ref(x_371);
 x_374 = lean_box(0);
}
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_164);
lean_ctor_set(x_375, 1, x_373);
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_372);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_164);
x_377 = lean_ctor_get(x_371, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_371, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_379 = x_371;
} else {
 lean_dec_ref(x_371);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_378);
return x_380;
}
}
}
else
{
lean_dec(x_164);
goto block_355;
}
}
block_355:
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_box(0);
if (lean_is_scalar(x_352)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_352;
 lean_ctor_set_tag(x_354, 1);
}
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_341);
lean_dec(x_164);
x_381 = lean_ctor_get(x_349, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_349, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_383 = x_349;
} else {
 lean_dec_ref(x_349);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
}
else
{
lean_object* x_385; lean_object* x_386; 
lean_dec(x_164);
x_385 = lean_box(0);
if (lean_is_scalar(x_341)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_341;
 lean_ctor_set_tag(x_386, 1);
}
lean_ctor_set(x_386, 0, x_340);
lean_ctor_set(x_386, 1, x_385);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_164);
x_387 = lean_ctor_get(x_339, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_339, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_389 = x_339;
} else {
 lean_dec_ref(x_339);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_388);
return x_390;
}
}
}
else
{
lean_object* x_391; 
lean_dec(x_164);
x_391 = lean_box(0);
lean_ctor_set_tag(x_177, 1);
lean_ctor_set(x_177, 1, x_391);
return x_177;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_392 = lean_ctor_get(x_177, 0);
lean_inc(x_392);
lean_dec(x_177);
x_393 = lean_ctor_get(x_392, 0);
x_394 = lean_ctor_get(x_392, 1);
x_395 = lean_string_utf8_byte_size(x_393);
x_396 = lean_nat_dec_eq(x_394, x_395);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_inc(x_394);
lean_inc(x_393);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_397 = x_392;
} else {
 lean_dec_ref(x_392);
 x_397 = lean_box(0);
}
x_398 = lean_string_utf8_next_fast(x_393, x_394);
lean_dec(x_394);
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_393);
lean_ctor_set(x_399, 1, x_398);
x_400 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_399);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_402 = x_400;
} else {
 lean_dec_ref(x_400);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_401, 0);
x_404 = lean_ctor_get(x_401, 1);
x_405 = lean_string_utf8_byte_size(x_403);
x_406 = lean_nat_dec_eq(x_404, x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_inc(x_404);
lean_inc(x_403);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_407 = x_401;
} else {
 lean_dec_ref(x_401);
 x_407 = lean_box(0);
}
x_408 = lean_string_utf8_next_fast(x_403, x_404);
lean_dec(x_404);
if (lean_is_scalar(x_407)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_407;
}
lean_ctor_set(x_409, 0, x_403);
lean_ctor_set(x_409, 1, x_408);
x_410 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_409);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_417; uint8_t x_418; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_413 = x_410;
} else {
 lean_dec_ref(x_410);
 x_413 = lean_box(0);
}
x_417 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_418 = lean_string_dec_eq(x_412, x_417);
if (x_418 == 0)
{
lean_object* x_419; uint8_t x_420; 
lean_dec(x_413);
x_419 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_420 = lean_string_dec_eq(x_412, x_419);
lean_dec(x_412);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; 
lean_dec(x_164);
x_421 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_402)) {
 x_422 = lean_alloc_ctor(1, 2, 0);
} else {
 x_422 = x_402;
 lean_ctor_set_tag(x_422, 1);
}
lean_ctor_set(x_422, 0, x_411);
lean_ctor_set(x_422, 1, x_421);
return x_422;
}
else
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_423, 0, x_164);
if (lean_is_scalar(x_402)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_402;
}
lean_ctor_set(x_424, 0, x_411);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
lean_dec(x_412);
lean_dec(x_402);
x_425 = lean_ctor_get(x_411, 0);
x_426 = lean_ctor_get(x_411, 1);
x_427 = lean_string_utf8_byte_size(x_425);
x_428 = lean_nat_dec_eq(x_426, x_427);
if (x_428 == 0)
{
if (x_418 == 0)
{
lean_dec(x_164);
goto block_416;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_413);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_429 = x_411;
} else {
 lean_dec_ref(x_411);
 x_429 = lean_box(0);
}
x_430 = lean_string_utf8_next_fast(x_425, x_426);
lean_dec(x_426);
if (lean_is_scalar(x_429)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_429;
}
lean_ctor_set(x_431, 0, x_425);
lean_ctor_set(x_431, 1, x_430);
x_432 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_431);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_435 = x_432;
} else {
 lean_dec_ref(x_432);
 x_435 = lean_box(0);
}
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_164);
lean_ctor_set(x_436, 1, x_434);
if (lean_is_scalar(x_435)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_435;
}
lean_ctor_set(x_437, 0, x_433);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_164);
x_438 = lean_ctor_get(x_432, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_432, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_440 = x_432;
} else {
 lean_dec_ref(x_432);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
}
else
{
lean_dec(x_164);
goto block_416;
}
}
block_416:
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_box(0);
if (lean_is_scalar(x_413)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_413;
 lean_ctor_set_tag(x_415, 1);
}
lean_ctor_set(x_415, 0, x_411);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_402);
lean_dec(x_164);
x_442 = lean_ctor_get(x_410, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_410, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_444 = x_410;
} else {
 lean_dec_ref(x_410);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; 
lean_dec(x_164);
x_446 = lean_box(0);
if (lean_is_scalar(x_402)) {
 x_447 = lean_alloc_ctor(1, 2, 0);
} else {
 x_447 = x_402;
 lean_ctor_set_tag(x_447, 1);
}
lean_ctor_set(x_447, 0, x_401);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_164);
x_448 = lean_ctor_get(x_400, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_400, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_450 = x_400;
} else {
 lean_dec_ref(x_400);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_448);
lean_ctor_set(x_451, 1, x_449);
return x_451;
}
}
else
{
lean_object* x_452; lean_object* x_453; 
lean_dec(x_164);
x_452 = lean_box(0);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_392);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
else
{
uint8_t x_454; 
lean_dec(x_164);
x_454 = !lean_is_exclusive(x_177);
if (x_454 == 0)
{
return x_177;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_177, 0);
x_456 = lean_ctor_get(x_177, 1);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_177);
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
return x_457;
}
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_163);
x_458 = lean_string_utf8_next_fast(x_169, x_170);
lean_dec(x_170);
x_459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_459, 0, x_169);
lean_ctor_set(x_459, 1, x_458);
x_460 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_459);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_462 = x_460;
} else {
 lean_dec_ref(x_460);
 x_462 = lean_box(0);
}
x_463 = lean_ctor_get(x_461, 0);
x_464 = lean_ctor_get(x_461, 1);
x_465 = lean_string_utf8_byte_size(x_463);
x_466 = lean_nat_dec_eq(x_464, x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_462);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_467 = x_461;
} else {
 lean_dec_ref(x_461);
 x_467 = lean_box(0);
}
x_468 = lean_string_utf8_next_fast(x_463, x_464);
lean_dec(x_464);
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_463);
lean_ctor_set(x_469, 1, x_468);
x_470 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_469);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_472 = x_470;
} else {
 lean_dec_ref(x_470);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_471, 0);
x_474 = lean_ctor_get(x_471, 1);
x_475 = lean_string_utf8_byte_size(x_473);
x_476 = lean_nat_dec_eq(x_474, x_475);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_inc(x_474);
lean_inc(x_473);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 x_477 = x_471;
} else {
 lean_dec_ref(x_471);
 x_477 = lean_box(0);
}
x_478 = lean_string_utf8_next_fast(x_473, x_474);
lean_dec(x_474);
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_473);
lean_ctor_set(x_479, 1, x_478);
x_480 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_479);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_487; uint8_t x_488; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_483 = x_480;
} else {
 lean_dec_ref(x_480);
 x_483 = lean_box(0);
}
x_487 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_488 = lean_string_dec_eq(x_482, x_487);
if (x_488 == 0)
{
lean_object* x_489; uint8_t x_490; 
lean_dec(x_483);
x_489 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_490 = lean_string_dec_eq(x_482, x_489);
lean_dec(x_482);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; 
lean_dec(x_164);
x_491 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_472)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_472;
 lean_ctor_set_tag(x_492, 1);
}
lean_ctor_set(x_492, 0, x_481);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
else
{
lean_object* x_493; lean_object* x_494; 
x_493 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_493, 0, x_164);
if (lean_is_scalar(x_472)) {
 x_494 = lean_alloc_ctor(0, 2, 0);
} else {
 x_494 = x_472;
}
lean_ctor_set(x_494, 0, x_481);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; 
lean_dec(x_482);
lean_dec(x_472);
x_495 = lean_ctor_get(x_481, 0);
x_496 = lean_ctor_get(x_481, 1);
x_497 = lean_string_utf8_byte_size(x_495);
x_498 = lean_nat_dec_eq(x_496, x_497);
if (x_498 == 0)
{
if (x_488 == 0)
{
lean_dec(x_164);
goto block_486;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_inc(x_496);
lean_inc(x_495);
lean_dec(x_483);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_499 = x_481;
} else {
 lean_dec_ref(x_481);
 x_499 = lean_box(0);
}
x_500 = lean_string_utf8_next_fast(x_495, x_496);
lean_dec(x_496);
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_501 = x_499;
}
lean_ctor_set(x_501, 0, x_495);
lean_ctor_set(x_501, 1, x_500);
x_502 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_501);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_505 = x_502;
} else {
 lean_dec_ref(x_502);
 x_505 = lean_box(0);
}
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_164);
lean_ctor_set(x_506, 1, x_504);
if (lean_is_scalar(x_505)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_505;
}
lean_ctor_set(x_507, 0, x_503);
lean_ctor_set(x_507, 1, x_506);
return x_507;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_164);
x_508 = lean_ctor_get(x_502, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_502, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_510 = x_502;
} else {
 lean_dec_ref(x_502);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_509);
return x_511;
}
}
}
else
{
lean_dec(x_164);
goto block_486;
}
}
block_486:
{
lean_object* x_484; lean_object* x_485; 
x_484 = lean_box(0);
if (lean_is_scalar(x_483)) {
 x_485 = lean_alloc_ctor(1, 2, 0);
} else {
 x_485 = x_483;
 lean_ctor_set_tag(x_485, 1);
}
lean_ctor_set(x_485, 0, x_481);
lean_ctor_set(x_485, 1, x_484);
return x_485;
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_472);
lean_dec(x_164);
x_512 = lean_ctor_get(x_480, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_480, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_514 = x_480;
} else {
 lean_dec_ref(x_480);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_512);
lean_ctor_set(x_515, 1, x_513);
return x_515;
}
}
else
{
lean_object* x_516; lean_object* x_517; 
lean_dec(x_164);
x_516 = lean_box(0);
if (lean_is_scalar(x_472)) {
 x_517 = lean_alloc_ctor(1, 2, 0);
} else {
 x_517 = x_472;
 lean_ctor_set_tag(x_517, 1);
}
lean_ctor_set(x_517, 0, x_471);
lean_ctor_set(x_517, 1, x_516);
return x_517;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_164);
x_518 = lean_ctor_get(x_470, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_470, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_520 = x_470;
} else {
 lean_dec_ref(x_470);
 x_520 = lean_box(0);
}
if (lean_is_scalar(x_520)) {
 x_521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_521 = x_520;
}
lean_ctor_set(x_521, 0, x_518);
lean_ctor_set(x_521, 1, x_519);
return x_521;
}
}
else
{
lean_object* x_522; lean_object* x_523; 
lean_dec(x_164);
x_522 = lean_box(0);
if (lean_is_scalar(x_462)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_462;
 lean_ctor_set_tag(x_523, 1);
}
lean_ctor_set(x_523, 0, x_461);
lean_ctor_set(x_523, 1, x_522);
return x_523;
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_164);
x_524 = lean_ctor_get(x_460, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_460, 1);
lean_inc(x_525);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_526 = x_460;
} else {
 lean_dec_ref(x_460);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(1, 2, 0);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_524);
lean_ctor_set(x_527, 1, x_525);
return x_527;
}
}
}
}
else
{
lean_dec(x_164);
goto block_168;
}
block_168:
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_box(0);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_165;
 lean_ctor_set_tag(x_167, 1);
}
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
else
{
uint8_t x_528; 
x_528 = !lean_is_exclusive(x_162);
if (x_528 == 0)
{
return x_162;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_162, 0);
x_530 = lean_ctor_get(x_162, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_162);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
return x_531;
}
}
}
block_46:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_41);
if (lean_is_scalar(x_31)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_31;
}
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
block_49:
{
lean_object* x_47; lean_object* x_48; 
x_47 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_29);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
block_53:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_29);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
block_55:
{
lean_object* x_54; 
x_54 = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
x_50 = x_54;
goto block_53;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; lean_object* x_536; lean_object* x_537; lean_object* x_544; lean_object* x_550; uint8_t x_551; 
lean_dec(x_29);
x_532 = lean_string_utf8_next_fast(x_32, x_33);
lean_dec(x_33);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_32);
lean_ctor_set(x_533, 1, x_532);
x_550 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
x_551 = lean_string_dec_eq(x_30, x_550);
if (x_551 == 0)
{
lean_object* x_552; uint8_t x_553; 
x_552 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
x_553 = lean_string_dec_eq(x_30, x_552);
if (x_553 == 0)
{
lean_object* x_554; uint8_t x_555; 
x_554 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_555 = lean_string_dec_eq(x_30, x_554);
lean_dec(x_30);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; 
lean_dec(x_31);
lean_dec_ref(x_1);
x_556 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3;
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_533);
lean_ctor_set(x_557, 1, x_556);
return x_557;
}
else
{
lean_object* x_558; 
x_558 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_31);
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 x_560 = x_558;
} else {
 lean_dec_ref(x_558);
 x_560 = lean_box(0);
}
if (lean_is_scalar(x_560)) {
 x_561 = lean_alloc_ctor(1, 1, 0);
} else {
 x_561 = x_560;
 lean_ctor_set_tag(x_561, 1);
}
lean_ctor_set(x_561, 0, x_559);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_533);
lean_ctor_set(x_562, 1, x_561);
return x_562;
}
else
{
lean_object* x_563; lean_object* x_564; 
x_563 = lean_ctor_get(x_558, 0);
lean_inc(x_563);
lean_dec_ref(x_558);
lean_inc(x_563);
x_564 = l_Lean_Json_getObjVal_x3f(x_563, x_552);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; 
lean_dec(x_563);
lean_dec(x_31);
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
lean_dec_ref(x_564);
x_544 = x_565;
goto block_547;
}
else
{
lean_object* x_566; 
x_566 = lean_ctor_get(x_564, 0);
lean_inc(x_566);
lean_dec_ref(x_564);
if (lean_obj_tag(x_566) == 3)
{
lean_object* x_567; lean_object* x_568; uint8_t x_569; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc_ref(x_567);
lean_dec_ref(x_566);
x_568 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
x_569 = lean_string_dec_eq(x_567, x_568);
lean_dec_ref(x_567);
if (x_569 == 0)
{
lean_dec(x_563);
lean_dec(x_31);
goto block_549;
}
else
{
lean_object* x_570; 
lean_inc(x_563);
x_570 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(x_563, x_550);
if (lean_obj_tag(x_570) == 0)
{
goto block_597;
}
else
{
lean_object* x_598; lean_object* x_599; 
x_598 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_563);
x_599 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_563, x_598);
if (lean_obj_tag(x_599) == 0)
{
lean_dec_ref(x_599);
goto block_597;
}
else
{
lean_dec_ref(x_599);
lean_dec_ref(x_570);
lean_dec(x_563);
lean_dec(x_31);
goto block_543;
}
}
block_592:
{
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; 
lean_dec(x_563);
lean_dec(x_31);
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
lean_dec_ref(x_570);
x_544 = x_571;
goto block_547;
}
else
{
lean_object* x_572; lean_object* x_573; 
x_572 = lean_ctor_get(x_570, 0);
lean_inc(x_572);
lean_dec_ref(x_570);
x_573 = l_Lean_Json_getObjVal_x3f(x_563, x_554);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; 
lean_dec(x_572);
lean_dec(x_31);
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
lean_dec_ref(x_573);
x_544 = x_574;
goto block_547;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_573, 0);
lean_inc(x_575);
lean_dec_ref(x_573);
x_576 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
lean_inc(x_575);
x_577 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(x_575, x_576);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; 
lean_dec(x_575);
lean_dec(x_572);
lean_dec(x_31);
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
lean_dec_ref(x_577);
x_544 = x_578;
goto block_547;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_577, 0);
lean_inc(x_579);
lean_dec_ref(x_577);
x_580 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
lean_inc(x_575);
x_581 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_575, x_580);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; 
lean_dec(x_579);
lean_dec(x_575);
lean_dec(x_572);
lean_dec(x_31);
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
lean_dec_ref(x_581);
x_544 = x_582;
goto block_547;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_581, 0);
lean_inc(x_583);
lean_dec_ref(x_581);
x_584 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_585 = l_Lean_Json_getObjVal_x3f(x_575, x_584);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; uint8_t x_587; 
lean_dec_ref(x_585);
x_586 = lean_box(0);
x_587 = lean_unbox(x_579);
lean_dec(x_579);
x_534 = x_572;
x_535 = x_587;
x_536 = x_583;
x_537 = x_586;
goto block_540;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
x_588 = lean_ctor_get(x_585, 0);
lean_inc(x_588);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 x_589 = x_585;
} else {
 lean_dec_ref(x_585);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(1, 1, 0);
} else {
 x_590 = x_589;
}
lean_ctor_set(x_590, 0, x_588);
x_591 = lean_unbox(x_579);
lean_dec(x_579);
x_534 = x_572;
x_535 = x_591;
x_536 = x_583;
x_537 = x_590;
goto block_540;
}
}
}
}
}
}
block_597:
{
lean_object* x_593; lean_object* x_594; 
x_593 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_563);
x_594 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_563, x_593);
if (lean_obj_tag(x_594) == 0)
{
lean_dec_ref(x_594);
if (lean_obj_tag(x_570) == 0)
{
goto block_592;
}
else
{
lean_object* x_595; lean_object* x_596; 
x_595 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
lean_inc(x_563);
x_596 = l_Lean_Json_getObjVal_x3f(x_563, x_595);
if (lean_obj_tag(x_596) == 0)
{
lean_dec_ref(x_596);
goto block_592;
}
else
{
lean_dec_ref(x_596);
lean_dec_ref(x_570);
lean_dec(x_563);
lean_dec(x_31);
goto block_543;
}
}
}
else
{
lean_dec_ref(x_594);
lean_dec_ref(x_570);
lean_dec(x_563);
lean_dec(x_31);
goto block_543;
}
}
}
}
else
{
lean_dec(x_566);
lean_dec(x_563);
lean_dec(x_31);
goto block_549;
}
}
}
}
}
else
{
lean_object* x_600; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_600 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_533);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; lean_object* x_625; uint8_t x_626; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_602 = x_600;
} else {
 lean_dec_ref(x_600);
 x_602 = lean_box(0);
}
x_603 = lean_ctor_get(x_601, 0);
x_604 = lean_ctor_get(x_601, 1);
x_625 = lean_string_utf8_byte_size(x_603);
x_626 = lean_nat_dec_eq(x_604, x_625);
if (x_626 == 0)
{
x_605 = x_553;
goto block_624;
}
else
{
x_605 = x_551;
goto block_624;
}
block_624:
{
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; 
x_606 = lean_box(0);
if (lean_is_scalar(x_602)) {
 x_607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_607 = x_602;
 lean_ctor_set_tag(x_607, 1);
}
lean_ctor_set(x_607, 0, x_601);
lean_ctor_set(x_607, 1, x_606);
return x_607;
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_inc(x_604);
lean_inc(x_603);
lean_dec(x_602);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_608 = x_601;
} else {
 lean_dec_ref(x_601);
 x_608 = lean_box(0);
}
x_609 = lean_string_utf8_next_fast(x_603, x_604);
lean_dec(x_604);
if (lean_is_scalar(x_608)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_608;
}
lean_ctor_set(x_610, 0, x_603);
lean_ctor_set(x_610, 1, x_609);
x_611 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_610);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; uint8_t x_617; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_613 = x_611;
} else {
 lean_dec_ref(x_611);
 x_613 = lean_box(0);
}
x_614 = lean_ctor_get(x_612, 0);
x_615 = lean_ctor_get(x_612, 1);
x_616 = lean_string_utf8_byte_size(x_614);
x_617 = lean_nat_dec_eq(x_615, x_616);
if (x_617 == 0)
{
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_613);
lean_dec(x_612);
x_3 = x_615;
x_4 = x_614;
goto block_19;
}
else
{
if (x_551 == 0)
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_box(0);
if (lean_is_scalar(x_613)) {
 x_619 = lean_alloc_ctor(1, 2, 0);
} else {
 x_619 = x_613;
 lean_ctor_set_tag(x_619, 1);
}
lean_ctor_set(x_619, 0, x_612);
lean_ctor_set(x_619, 1, x_618);
return x_619;
}
else
{
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_613);
lean_dec(x_612);
x_3 = x_615;
x_4 = x_614;
goto block_19;
}
}
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_620 = lean_ctor_get(x_611, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_611, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_622 = x_611;
} else {
 lean_dec_ref(x_611);
 x_622 = lean_box(0);
}
if (lean_is_scalar(x_622)) {
 x_623 = lean_alloc_ctor(1, 2, 0);
} else {
 x_623 = x_622;
}
lean_ctor_set(x_623, 0, x_620);
lean_ctor_set(x_623, 1, x_621);
return x_623;
}
}
}
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_627 = lean_ctor_get(x_600, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_600, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_629 = x_600;
} else {
 lean_dec_ref(x_600);
 x_629 = lean_box(0);
}
if (lean_is_scalar(x_629)) {
 x_630 = lean_alloc_ctor(1, 2, 0);
} else {
 x_630 = x_629;
}
lean_ctor_set(x_630, 0, x_627);
lean_ctor_set(x_630, 1, x_628);
return x_630;
}
}
}
else
{
lean_object* x_631; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_631 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(x_533);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_638; lean_object* x_639; lean_object* x_640; uint8_t x_641; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_634 = x_631;
} else {
 lean_dec_ref(x_631);
 x_634 = lean_box(0);
}
x_638 = lean_ctor_get(x_632, 0);
x_639 = lean_ctor_get(x_632, 1);
x_640 = lean_string_utf8_byte_size(x_638);
x_641 = lean_nat_dec_eq(x_639, x_640);
if (x_641 == 0)
{
if (x_551 == 0)
{
lean_dec(x_633);
goto block_637;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_634);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_642 = x_632;
} else {
 lean_dec_ref(x_632);
 x_642 = lean_box(0);
}
x_643 = lean_string_utf8_next_fast(x_638, x_639);
lean_dec(x_639);
if (lean_is_scalar(x_642)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_642;
}
lean_ctor_set(x_644, 0, x_638);
lean_ctor_set(x_644, 1, x_643);
x_645 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_644);
if (lean_obj_tag(x_645) == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; uint8_t x_651; 
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 lean_ctor_release(x_645, 1);
 x_647 = x_645;
} else {
 lean_dec_ref(x_645);
 x_647 = lean_box(0);
}
x_648 = lean_ctor_get(x_646, 0);
x_649 = lean_ctor_get(x_646, 1);
x_650 = lean_string_utf8_byte_size(x_648);
x_651 = lean_nat_dec_eq(x_649, x_650);
if (x_651 == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_647);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_652 = x_646;
} else {
 lean_dec_ref(x_646);
 x_652 = lean_box(0);
}
x_653 = lean_string_utf8_next_fast(x_648, x_649);
lean_dec(x_649);
if (lean_is_scalar(x_652)) {
 x_654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_654 = x_652;
}
lean_ctor_set(x_654, 0, x_648);
lean_ctor_set(x_654, 1, x_653);
x_655 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_654);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_657 = x_655;
} else {
 lean_dec_ref(x_655);
 x_657 = lean_box(0);
}
x_658 = lean_ctor_get(x_656, 0);
x_659 = lean_ctor_get(x_656, 1);
x_660 = lean_string_utf8_byte_size(x_658);
x_661 = lean_nat_dec_eq(x_659, x_660);
if (x_661 == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
lean_inc(x_659);
lean_inc(x_658);
if (lean_is_exclusive(x_656)) {
 lean_ctor_release(x_656, 0);
 lean_ctor_release(x_656, 1);
 x_662 = x_656;
} else {
 lean_dec_ref(x_656);
 x_662 = lean_box(0);
}
x_663 = lean_string_utf8_next_fast(x_658, x_659);
lean_dec(x_659);
if (lean_is_scalar(x_662)) {
 x_664 = lean_alloc_ctor(0, 2, 0);
} else {
 x_664 = x_662;
}
lean_ctor_set(x_664, 0, x_658);
lean_ctor_set(x_664, 1, x_663);
x_665 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_664);
if (lean_obj_tag(x_665) == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_672; uint8_t x_673; 
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
if (lean_is_exclusive(x_665)) {
 lean_ctor_release(x_665, 0);
 lean_ctor_release(x_665, 1);
 x_668 = x_665;
} else {
 lean_dec_ref(x_665);
 x_668 = lean_box(0);
}
x_672 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_673 = lean_string_dec_eq(x_667, x_672);
if (x_673 == 0)
{
lean_object* x_674; uint8_t x_675; 
lean_dec(x_668);
x_674 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_675 = lean_string_dec_eq(x_667, x_674);
lean_dec(x_667);
if (x_675 == 0)
{
lean_object* x_676; lean_object* x_677; 
lean_dec(x_633);
x_676 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_657)) {
 x_677 = lean_alloc_ctor(1, 2, 0);
} else {
 x_677 = x_657;
 lean_ctor_set_tag(x_677, 1);
}
lean_ctor_set(x_677, 0, x_666);
lean_ctor_set(x_677, 1, x_676);
return x_677;
}
else
{
lean_object* x_678; lean_object* x_679; 
x_678 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_678, 0, x_633);
if (lean_is_scalar(x_657)) {
 x_679 = lean_alloc_ctor(0, 2, 0);
} else {
 x_679 = x_657;
}
lean_ctor_set(x_679, 0, x_666);
lean_ctor_set(x_679, 1, x_678);
return x_679;
}
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; uint8_t x_683; 
lean_dec(x_667);
lean_dec(x_657);
x_680 = lean_ctor_get(x_666, 0);
x_681 = lean_ctor_get(x_666, 1);
x_682 = lean_string_utf8_byte_size(x_680);
x_683 = lean_nat_dec_eq(x_681, x_682);
if (x_683 == 0)
{
if (x_673 == 0)
{
lean_dec(x_633);
goto block_671;
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
lean_inc(x_681);
lean_inc(x_680);
lean_dec(x_668);
if (lean_is_exclusive(x_666)) {
 lean_ctor_release(x_666, 0);
 lean_ctor_release(x_666, 1);
 x_684 = x_666;
} else {
 lean_dec_ref(x_666);
 x_684 = lean_box(0);
}
x_685 = lean_string_utf8_next_fast(x_680, x_681);
lean_dec(x_681);
if (lean_is_scalar(x_684)) {
 x_686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_686 = x_684;
}
lean_ctor_set(x_686, 0, x_680);
lean_ctor_set(x_686, 1, x_685);
x_687 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_686);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_690 = x_687;
} else {
 lean_dec_ref(x_687);
 x_690 = lean_box(0);
}
x_691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_691, 0, x_633);
lean_ctor_set(x_691, 1, x_689);
if (lean_is_scalar(x_690)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_690;
}
lean_ctor_set(x_692, 0, x_688);
lean_ctor_set(x_692, 1, x_691);
return x_692;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_633);
x_693 = lean_ctor_get(x_687, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_687, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_695 = x_687;
} else {
 lean_dec_ref(x_687);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(1, 2, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_693);
lean_ctor_set(x_696, 1, x_694);
return x_696;
}
}
}
else
{
lean_dec(x_633);
goto block_671;
}
}
block_671:
{
lean_object* x_669; lean_object* x_670; 
x_669 = lean_box(0);
if (lean_is_scalar(x_668)) {
 x_670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_670 = x_668;
 lean_ctor_set_tag(x_670, 1);
}
lean_ctor_set(x_670, 0, x_666);
lean_ctor_set(x_670, 1, x_669);
return x_670;
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec(x_657);
lean_dec(x_633);
x_697 = lean_ctor_get(x_665, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_665, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_665)) {
 lean_ctor_release(x_665, 0);
 lean_ctor_release(x_665, 1);
 x_699 = x_665;
} else {
 lean_dec_ref(x_665);
 x_699 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_700 = lean_alloc_ctor(1, 2, 0);
} else {
 x_700 = x_699;
}
lean_ctor_set(x_700, 0, x_697);
lean_ctor_set(x_700, 1, x_698);
return x_700;
}
}
else
{
lean_object* x_701; lean_object* x_702; 
lean_dec(x_633);
x_701 = lean_box(0);
if (lean_is_scalar(x_657)) {
 x_702 = lean_alloc_ctor(1, 2, 0);
} else {
 x_702 = x_657;
 lean_ctor_set_tag(x_702, 1);
}
lean_ctor_set(x_702, 0, x_656);
lean_ctor_set(x_702, 1, x_701);
return x_702;
}
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_633);
x_703 = lean_ctor_get(x_655, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_655, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_705 = x_655;
} else {
 lean_dec_ref(x_655);
 x_705 = lean_box(0);
}
if (lean_is_scalar(x_705)) {
 x_706 = lean_alloc_ctor(1, 2, 0);
} else {
 x_706 = x_705;
}
lean_ctor_set(x_706, 0, x_703);
lean_ctor_set(x_706, 1, x_704);
return x_706;
}
}
else
{
lean_object* x_707; lean_object* x_708; 
lean_dec(x_633);
x_707 = lean_box(0);
if (lean_is_scalar(x_647)) {
 x_708 = lean_alloc_ctor(1, 2, 0);
} else {
 x_708 = x_647;
 lean_ctor_set_tag(x_708, 1);
}
lean_ctor_set(x_708, 0, x_646);
lean_ctor_set(x_708, 1, x_707);
return x_708;
}
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_633);
x_709 = lean_ctor_get(x_645, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_645, 1);
lean_inc(x_710);
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 lean_ctor_release(x_645, 1);
 x_711 = x_645;
} else {
 lean_dec_ref(x_645);
 x_711 = lean_box(0);
}
if (lean_is_scalar(x_711)) {
 x_712 = lean_alloc_ctor(1, 2, 0);
} else {
 x_712 = x_711;
}
lean_ctor_set(x_712, 0, x_709);
lean_ctor_set(x_712, 1, x_710);
return x_712;
}
}
}
else
{
lean_dec(x_633);
goto block_637;
}
block_637:
{
lean_object* x_635; lean_object* x_636; 
x_635 = lean_box(0);
if (lean_is_scalar(x_634)) {
 x_636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_636 = x_634;
 lean_ctor_set_tag(x_636, 1);
}
lean_ctor_set(x_636, 0, x_632);
lean_ctor_set(x_636, 1, x_635);
return x_636;
}
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_713 = lean_ctor_get(x_631, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_631, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_715 = x_631;
} else {
 lean_dec_ref(x_631);
 x_715 = lean_box(0);
}
if (lean_is_scalar(x_715)) {
 x_716 = lean_alloc_ctor(1, 2, 0);
} else {
 x_716 = x_715;
}
lean_ctor_set(x_716, 0, x_713);
lean_ctor_set(x_716, 1, x_714);
return x_716;
}
}
block_540:
{
lean_object* x_538; lean_object* x_539; 
x_538 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_538, 0, x_534);
lean_ctor_set(x_538, 1, x_536);
lean_ctor_set(x_538, 2, x_537);
lean_ctor_set_uint8(x_538, sizeof(void*)*3, x_535);
if (lean_is_scalar(x_31)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_31;
}
lean_ctor_set(x_539, 0, x_533);
lean_ctor_set(x_539, 1, x_538);
return x_539;
}
block_543:
{
lean_object* x_541; lean_object* x_542; 
x_541 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1;
x_542 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_542, 0, x_533);
lean_ctor_set(x_542, 1, x_541);
return x_542;
}
block_547:
{
lean_object* x_545; lean_object* x_546; 
x_545 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_545, 0, x_544);
x_546 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_546, 0, x_533);
lean_ctor_set(x_546, 1, x_545);
return x_546;
}
block_549:
{
lean_object* x_548; 
x_548 = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
x_544 = x_548;
goto block_547;
}
}
}
else
{
lean_object* x_717; lean_object* x_718; 
lean_dec(x_30);
lean_dec_ref(x_1);
x_717 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_718 = x_31;
 lean_ctor_set_tag(x_718, 1);
}
lean_ctor_set(x_718, 0, x_29);
lean_ctor_set(x_718, 1, x_717);
return x_718;
}
}
else
{
uint8_t x_719; 
lean_dec_ref(x_1);
x_719 = !lean_is_exclusive(x_28);
if (x_719 == 0)
{
return x_28;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_720 = lean_ctor_get(x_28, 0);
x_721 = lean_ctor_get(x_28, 1);
lean_inc(x_721);
lean_inc(x_720);
lean_dec(x_28);
x_722 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_722, 0, x_720);
lean_ctor_set(x_722, 1, x_721);
return x_722;
}
}
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; 
lean_dec(x_2);
x_723 = lean_string_utf8_next_fast(x_20, x_21);
lean_dec(x_21);
x_724 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_724, 0, x_20);
lean_ctor_set(x_724, 1, x_723);
x_725 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_724);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; uint8_t x_732; 
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_725, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_728 = x_725;
} else {
 lean_dec_ref(x_725);
 x_728 = lean_box(0);
}
x_729 = lean_ctor_get(x_726, 0);
x_730 = lean_ctor_get(x_726, 1);
x_731 = lean_string_utf8_byte_size(x_729);
x_732 = lean_nat_dec_eq(x_730, x_731);
if (x_732 == 0)
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; uint8_t x_737; lean_object* x_738; lean_object* x_739; lean_object* x_746; lean_object* x_752; uint8_t x_753; 
lean_inc(x_730);
lean_inc(x_729);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_733 = x_726;
} else {
 lean_dec_ref(x_726);
 x_733 = lean_box(0);
}
x_734 = lean_string_utf8_next_fast(x_729, x_730);
lean_dec(x_730);
if (lean_is_scalar(x_733)) {
 x_735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_735 = x_733;
}
lean_ctor_set(x_735, 0, x_729);
lean_ctor_set(x_735, 1, x_734);
x_752 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
x_753 = lean_string_dec_eq(x_727, x_752);
if (x_753 == 0)
{
lean_object* x_754; uint8_t x_755; 
x_754 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
x_755 = lean_string_dec_eq(x_727, x_754);
if (x_755 == 0)
{
lean_object* x_756; uint8_t x_757; 
x_756 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_757 = lean_string_dec_eq(x_727, x_756);
lean_dec(x_727);
if (x_757 == 0)
{
lean_object* x_758; lean_object* x_759; 
lean_dec(x_728);
lean_dec_ref(x_1);
x_758 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3;
x_759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_759, 0, x_735);
lean_ctor_set(x_759, 1, x_758);
return x_759;
}
else
{
lean_object* x_760; 
x_760 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_760) == 0)
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_728);
x_761 = lean_ctor_get(x_760, 0);
lean_inc(x_761);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 x_762 = x_760;
} else {
 lean_dec_ref(x_760);
 x_762 = lean_box(0);
}
if (lean_is_scalar(x_762)) {
 x_763 = lean_alloc_ctor(1, 1, 0);
} else {
 x_763 = x_762;
 lean_ctor_set_tag(x_763, 1);
}
lean_ctor_set(x_763, 0, x_761);
x_764 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_764, 0, x_735);
lean_ctor_set(x_764, 1, x_763);
return x_764;
}
else
{
lean_object* x_765; lean_object* x_766; 
x_765 = lean_ctor_get(x_760, 0);
lean_inc(x_765);
lean_dec_ref(x_760);
lean_inc(x_765);
x_766 = l_Lean_Json_getObjVal_x3f(x_765, x_754);
if (lean_obj_tag(x_766) == 0)
{
lean_object* x_767; 
lean_dec(x_765);
lean_dec(x_728);
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
lean_dec_ref(x_766);
x_746 = x_767;
goto block_749;
}
else
{
lean_object* x_768; 
x_768 = lean_ctor_get(x_766, 0);
lean_inc(x_768);
lean_dec_ref(x_766);
if (lean_obj_tag(x_768) == 3)
{
lean_object* x_769; lean_object* x_770; uint8_t x_771; 
x_769 = lean_ctor_get(x_768, 0);
lean_inc_ref(x_769);
lean_dec_ref(x_768);
x_770 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
x_771 = lean_string_dec_eq(x_769, x_770);
lean_dec_ref(x_769);
if (x_771 == 0)
{
lean_dec(x_765);
lean_dec(x_728);
goto block_751;
}
else
{
lean_object* x_772; 
lean_inc(x_765);
x_772 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(x_765, x_752);
if (lean_obj_tag(x_772) == 0)
{
goto block_799;
}
else
{
lean_object* x_800; lean_object* x_801; 
x_800 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_765);
x_801 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_765, x_800);
if (lean_obj_tag(x_801) == 0)
{
lean_dec_ref(x_801);
goto block_799;
}
else
{
lean_dec_ref(x_801);
lean_dec_ref(x_772);
lean_dec(x_765);
lean_dec(x_728);
goto block_745;
}
}
block_794:
{
if (lean_obj_tag(x_772) == 0)
{
lean_object* x_773; 
lean_dec(x_765);
lean_dec(x_728);
x_773 = lean_ctor_get(x_772, 0);
lean_inc(x_773);
lean_dec_ref(x_772);
x_746 = x_773;
goto block_749;
}
else
{
lean_object* x_774; lean_object* x_775; 
x_774 = lean_ctor_get(x_772, 0);
lean_inc(x_774);
lean_dec_ref(x_772);
x_775 = l_Lean_Json_getObjVal_x3f(x_765, x_756);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; 
lean_dec(x_774);
lean_dec(x_728);
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
lean_dec_ref(x_775);
x_746 = x_776;
goto block_749;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_777 = lean_ctor_get(x_775, 0);
lean_inc(x_777);
lean_dec_ref(x_775);
x_778 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
lean_inc(x_777);
x_779 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(x_777, x_778);
if (lean_obj_tag(x_779) == 0)
{
lean_object* x_780; 
lean_dec(x_777);
lean_dec(x_774);
lean_dec(x_728);
x_780 = lean_ctor_get(x_779, 0);
lean_inc(x_780);
lean_dec_ref(x_779);
x_746 = x_780;
goto block_749;
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_781 = lean_ctor_get(x_779, 0);
lean_inc(x_781);
lean_dec_ref(x_779);
x_782 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
lean_inc(x_777);
x_783 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_777, x_782);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; 
lean_dec(x_781);
lean_dec(x_777);
lean_dec(x_774);
lean_dec(x_728);
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
lean_dec_ref(x_783);
x_746 = x_784;
goto block_749;
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_785 = lean_ctor_get(x_783, 0);
lean_inc(x_785);
lean_dec_ref(x_783);
x_786 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_787 = l_Lean_Json_getObjVal_x3f(x_777, x_786);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; uint8_t x_789; 
lean_dec_ref(x_787);
x_788 = lean_box(0);
x_789 = lean_unbox(x_781);
lean_dec(x_781);
x_736 = x_774;
x_737 = x_789;
x_738 = x_785;
x_739 = x_788;
goto block_742;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; uint8_t x_793; 
x_790 = lean_ctor_get(x_787, 0);
lean_inc(x_790);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 x_791 = x_787;
} else {
 lean_dec_ref(x_787);
 x_791 = lean_box(0);
}
if (lean_is_scalar(x_791)) {
 x_792 = lean_alloc_ctor(1, 1, 0);
} else {
 x_792 = x_791;
}
lean_ctor_set(x_792, 0, x_790);
x_793 = lean_unbox(x_781);
lean_dec(x_781);
x_736 = x_774;
x_737 = x_793;
x_738 = x_785;
x_739 = x_792;
goto block_742;
}
}
}
}
}
}
block_799:
{
lean_object* x_795; lean_object* x_796; 
x_795 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_765);
x_796 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_765, x_795);
if (lean_obj_tag(x_796) == 0)
{
lean_dec_ref(x_796);
if (lean_obj_tag(x_772) == 0)
{
goto block_794;
}
else
{
lean_object* x_797; lean_object* x_798; 
x_797 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
lean_inc(x_765);
x_798 = l_Lean_Json_getObjVal_x3f(x_765, x_797);
if (lean_obj_tag(x_798) == 0)
{
lean_dec_ref(x_798);
goto block_794;
}
else
{
lean_dec_ref(x_798);
lean_dec_ref(x_772);
lean_dec(x_765);
lean_dec(x_728);
goto block_745;
}
}
}
else
{
lean_dec_ref(x_796);
lean_dec_ref(x_772);
lean_dec(x_765);
lean_dec(x_728);
goto block_745;
}
}
}
}
else
{
lean_dec(x_768);
lean_dec(x_765);
lean_dec(x_728);
goto block_751;
}
}
}
}
}
else
{
lean_object* x_802; 
lean_dec(x_728);
lean_dec(x_727);
lean_dec_ref(x_1);
x_802 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_735);
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; uint8_t x_807; lean_object* x_827; uint8_t x_828; 
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
if (lean_is_exclusive(x_802)) {
 lean_ctor_release(x_802, 0);
 lean_ctor_release(x_802, 1);
 x_804 = x_802;
} else {
 lean_dec_ref(x_802);
 x_804 = lean_box(0);
}
x_805 = lean_ctor_get(x_803, 0);
x_806 = lean_ctor_get(x_803, 1);
x_827 = lean_string_utf8_byte_size(x_805);
x_828 = lean_nat_dec_eq(x_806, x_827);
if (x_828 == 0)
{
x_807 = x_755;
goto block_826;
}
else
{
x_807 = x_753;
goto block_826;
}
block_826:
{
if (x_807 == 0)
{
lean_object* x_808; lean_object* x_809; 
x_808 = lean_box(0);
if (lean_is_scalar(x_804)) {
 x_809 = lean_alloc_ctor(1, 2, 0);
} else {
 x_809 = x_804;
 lean_ctor_set_tag(x_809, 1);
}
lean_ctor_set(x_809, 0, x_803);
lean_ctor_set(x_809, 1, x_808);
return x_809;
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_inc(x_806);
lean_inc(x_805);
lean_dec(x_804);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_810 = x_803;
} else {
 lean_dec_ref(x_803);
 x_810 = lean_box(0);
}
x_811 = lean_string_utf8_next_fast(x_805, x_806);
lean_dec(x_806);
if (lean_is_scalar(x_810)) {
 x_812 = lean_alloc_ctor(0, 2, 0);
} else {
 x_812 = x_810;
}
lean_ctor_set(x_812, 0, x_805);
lean_ctor_set(x_812, 1, x_811);
x_813 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_812);
if (lean_obj_tag(x_813) == 0)
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; uint8_t x_819; 
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_815 = x_813;
} else {
 lean_dec_ref(x_813);
 x_815 = lean_box(0);
}
x_816 = lean_ctor_get(x_814, 0);
x_817 = lean_ctor_get(x_814, 1);
x_818 = lean_string_utf8_byte_size(x_816);
x_819 = lean_nat_dec_eq(x_817, x_818);
if (x_819 == 0)
{
lean_inc(x_817);
lean_inc(x_816);
lean_dec(x_815);
lean_dec(x_814);
x_3 = x_817;
x_4 = x_816;
goto block_19;
}
else
{
if (x_753 == 0)
{
lean_object* x_820; lean_object* x_821; 
x_820 = lean_box(0);
if (lean_is_scalar(x_815)) {
 x_821 = lean_alloc_ctor(1, 2, 0);
} else {
 x_821 = x_815;
 lean_ctor_set_tag(x_821, 1);
}
lean_ctor_set(x_821, 0, x_814);
lean_ctor_set(x_821, 1, x_820);
return x_821;
}
else
{
lean_inc(x_817);
lean_inc(x_816);
lean_dec(x_815);
lean_dec(x_814);
x_3 = x_817;
x_4 = x_816;
goto block_19;
}
}
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_822 = lean_ctor_get(x_813, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_813, 1);
lean_inc(x_823);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_824 = x_813;
} else {
 lean_dec_ref(x_813);
 x_824 = lean_box(0);
}
if (lean_is_scalar(x_824)) {
 x_825 = lean_alloc_ctor(1, 2, 0);
} else {
 x_825 = x_824;
}
lean_ctor_set(x_825, 0, x_822);
lean_ctor_set(x_825, 1, x_823);
return x_825;
}
}
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_829 = lean_ctor_get(x_802, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_802, 1);
lean_inc(x_830);
if (lean_is_exclusive(x_802)) {
 lean_ctor_release(x_802, 0);
 lean_ctor_release(x_802, 1);
 x_831 = x_802;
} else {
 lean_dec_ref(x_802);
 x_831 = lean_box(0);
}
if (lean_is_scalar(x_831)) {
 x_832 = lean_alloc_ctor(1, 2, 0);
} else {
 x_832 = x_831;
}
lean_ctor_set(x_832, 0, x_829);
lean_ctor_set(x_832, 1, x_830);
return x_832;
}
}
}
else
{
lean_object* x_833; 
lean_dec(x_728);
lean_dec(x_727);
lean_dec_ref(x_1);
x_833 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(x_735);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_840; lean_object* x_841; lean_object* x_842; uint8_t x_843; 
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_836 = x_833;
} else {
 lean_dec_ref(x_833);
 x_836 = lean_box(0);
}
x_840 = lean_ctor_get(x_834, 0);
x_841 = lean_ctor_get(x_834, 1);
x_842 = lean_string_utf8_byte_size(x_840);
x_843 = lean_nat_dec_eq(x_841, x_842);
if (x_843 == 0)
{
if (x_753 == 0)
{
lean_dec(x_835);
goto block_839;
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
lean_inc(x_841);
lean_inc(x_840);
lean_dec(x_836);
if (lean_is_exclusive(x_834)) {
 lean_ctor_release(x_834, 0);
 lean_ctor_release(x_834, 1);
 x_844 = x_834;
} else {
 lean_dec_ref(x_834);
 x_844 = lean_box(0);
}
x_845 = lean_string_utf8_next_fast(x_840, x_841);
lean_dec(x_841);
if (lean_is_scalar(x_844)) {
 x_846 = lean_alloc_ctor(0, 2, 0);
} else {
 x_846 = x_844;
}
lean_ctor_set(x_846, 0, x_840);
lean_ctor_set(x_846, 1, x_845);
x_847 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_846);
if (lean_obj_tag(x_847) == 0)
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; uint8_t x_853; 
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 x_849 = x_847;
} else {
 lean_dec_ref(x_847);
 x_849 = lean_box(0);
}
x_850 = lean_ctor_get(x_848, 0);
x_851 = lean_ctor_get(x_848, 1);
x_852 = lean_string_utf8_byte_size(x_850);
x_853 = lean_nat_dec_eq(x_851, x_852);
if (x_853 == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; 
lean_inc(x_851);
lean_inc(x_850);
lean_dec(x_849);
if (lean_is_exclusive(x_848)) {
 lean_ctor_release(x_848, 0);
 lean_ctor_release(x_848, 1);
 x_854 = x_848;
} else {
 lean_dec_ref(x_848);
 x_854 = lean_box(0);
}
x_855 = lean_string_utf8_next_fast(x_850, x_851);
lean_dec(x_851);
if (lean_is_scalar(x_854)) {
 x_856 = lean_alloc_ctor(0, 2, 0);
} else {
 x_856 = x_854;
}
lean_ctor_set(x_856, 0, x_850);
lean_ctor_set(x_856, 1, x_855);
x_857 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_856);
if (lean_obj_tag(x_857) == 0)
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; uint8_t x_863; 
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_859 = x_857;
} else {
 lean_dec_ref(x_857);
 x_859 = lean_box(0);
}
x_860 = lean_ctor_get(x_858, 0);
x_861 = lean_ctor_get(x_858, 1);
x_862 = lean_string_utf8_byte_size(x_860);
x_863 = lean_nat_dec_eq(x_861, x_862);
if (x_863 == 0)
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
lean_inc(x_861);
lean_inc(x_860);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 x_864 = x_858;
} else {
 lean_dec_ref(x_858);
 x_864 = lean_box(0);
}
x_865 = lean_string_utf8_next_fast(x_860, x_861);
lean_dec(x_861);
if (lean_is_scalar(x_864)) {
 x_866 = lean_alloc_ctor(0, 2, 0);
} else {
 x_866 = x_864;
}
lean_ctor_set(x_866, 0, x_860);
lean_ctor_set(x_866, 1, x_865);
x_867 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_866);
if (lean_obj_tag(x_867) == 0)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_874; uint8_t x_875; 
x_868 = lean_ctor_get(x_867, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_867, 1);
lean_inc(x_869);
if (lean_is_exclusive(x_867)) {
 lean_ctor_release(x_867, 0);
 lean_ctor_release(x_867, 1);
 x_870 = x_867;
} else {
 lean_dec_ref(x_867);
 x_870 = lean_box(0);
}
x_874 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_875 = lean_string_dec_eq(x_869, x_874);
if (x_875 == 0)
{
lean_object* x_876; uint8_t x_877; 
lean_dec(x_870);
x_876 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_877 = lean_string_dec_eq(x_869, x_876);
lean_dec(x_869);
if (x_877 == 0)
{
lean_object* x_878; lean_object* x_879; 
lean_dec(x_835);
x_878 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_859)) {
 x_879 = lean_alloc_ctor(1, 2, 0);
} else {
 x_879 = x_859;
 lean_ctor_set_tag(x_879, 1);
}
lean_ctor_set(x_879, 0, x_868);
lean_ctor_set(x_879, 1, x_878);
return x_879;
}
else
{
lean_object* x_880; lean_object* x_881; 
x_880 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_880, 0, x_835);
if (lean_is_scalar(x_859)) {
 x_881 = lean_alloc_ctor(0, 2, 0);
} else {
 x_881 = x_859;
}
lean_ctor_set(x_881, 0, x_868);
lean_ctor_set(x_881, 1, x_880);
return x_881;
}
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; uint8_t x_885; 
lean_dec(x_869);
lean_dec(x_859);
x_882 = lean_ctor_get(x_868, 0);
x_883 = lean_ctor_get(x_868, 1);
x_884 = lean_string_utf8_byte_size(x_882);
x_885 = lean_nat_dec_eq(x_883, x_884);
if (x_885 == 0)
{
if (x_875 == 0)
{
lean_dec(x_835);
goto block_873;
}
else
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
lean_inc(x_883);
lean_inc(x_882);
lean_dec(x_870);
if (lean_is_exclusive(x_868)) {
 lean_ctor_release(x_868, 0);
 lean_ctor_release(x_868, 1);
 x_886 = x_868;
} else {
 lean_dec_ref(x_868);
 x_886 = lean_box(0);
}
x_887 = lean_string_utf8_next_fast(x_882, x_883);
lean_dec(x_883);
if (lean_is_scalar(x_886)) {
 x_888 = lean_alloc_ctor(0, 2, 0);
} else {
 x_888 = x_886;
}
lean_ctor_set(x_888, 0, x_882);
lean_ctor_set(x_888, 1, x_887);
x_889 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_888);
if (lean_obj_tag(x_889) == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_892 = x_889;
} else {
 lean_dec_ref(x_889);
 x_892 = lean_box(0);
}
x_893 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_893, 0, x_835);
lean_ctor_set(x_893, 1, x_891);
if (lean_is_scalar(x_892)) {
 x_894 = lean_alloc_ctor(0, 2, 0);
} else {
 x_894 = x_892;
}
lean_ctor_set(x_894, 0, x_890);
lean_ctor_set(x_894, 1, x_893);
return x_894;
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
lean_dec(x_835);
x_895 = lean_ctor_get(x_889, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_889, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_897 = x_889;
} else {
 lean_dec_ref(x_889);
 x_897 = lean_box(0);
}
if (lean_is_scalar(x_897)) {
 x_898 = lean_alloc_ctor(1, 2, 0);
} else {
 x_898 = x_897;
}
lean_ctor_set(x_898, 0, x_895);
lean_ctor_set(x_898, 1, x_896);
return x_898;
}
}
}
else
{
lean_dec(x_835);
goto block_873;
}
}
block_873:
{
lean_object* x_871; lean_object* x_872; 
x_871 = lean_box(0);
if (lean_is_scalar(x_870)) {
 x_872 = lean_alloc_ctor(1, 2, 0);
} else {
 x_872 = x_870;
 lean_ctor_set_tag(x_872, 1);
}
lean_ctor_set(x_872, 0, x_868);
lean_ctor_set(x_872, 1, x_871);
return x_872;
}
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_859);
lean_dec(x_835);
x_899 = lean_ctor_get(x_867, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_867, 1);
lean_inc(x_900);
if (lean_is_exclusive(x_867)) {
 lean_ctor_release(x_867, 0);
 lean_ctor_release(x_867, 1);
 x_901 = x_867;
} else {
 lean_dec_ref(x_867);
 x_901 = lean_box(0);
}
if (lean_is_scalar(x_901)) {
 x_902 = lean_alloc_ctor(1, 2, 0);
} else {
 x_902 = x_901;
}
lean_ctor_set(x_902, 0, x_899);
lean_ctor_set(x_902, 1, x_900);
return x_902;
}
}
else
{
lean_object* x_903; lean_object* x_904; 
lean_dec(x_835);
x_903 = lean_box(0);
if (lean_is_scalar(x_859)) {
 x_904 = lean_alloc_ctor(1, 2, 0);
} else {
 x_904 = x_859;
 lean_ctor_set_tag(x_904, 1);
}
lean_ctor_set(x_904, 0, x_858);
lean_ctor_set(x_904, 1, x_903);
return x_904;
}
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
lean_dec(x_835);
x_905 = lean_ctor_get(x_857, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_857, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_907 = x_857;
} else {
 lean_dec_ref(x_857);
 x_907 = lean_box(0);
}
if (lean_is_scalar(x_907)) {
 x_908 = lean_alloc_ctor(1, 2, 0);
} else {
 x_908 = x_907;
}
lean_ctor_set(x_908, 0, x_905);
lean_ctor_set(x_908, 1, x_906);
return x_908;
}
}
else
{
lean_object* x_909; lean_object* x_910; 
lean_dec(x_835);
x_909 = lean_box(0);
if (lean_is_scalar(x_849)) {
 x_910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_910 = x_849;
 lean_ctor_set_tag(x_910, 1);
}
lean_ctor_set(x_910, 0, x_848);
lean_ctor_set(x_910, 1, x_909);
return x_910;
}
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
lean_dec(x_835);
x_911 = lean_ctor_get(x_847, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_847, 1);
lean_inc(x_912);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 x_913 = x_847;
} else {
 lean_dec_ref(x_847);
 x_913 = lean_box(0);
}
if (lean_is_scalar(x_913)) {
 x_914 = lean_alloc_ctor(1, 2, 0);
} else {
 x_914 = x_913;
}
lean_ctor_set(x_914, 0, x_911);
lean_ctor_set(x_914, 1, x_912);
return x_914;
}
}
}
else
{
lean_dec(x_835);
goto block_839;
}
block_839:
{
lean_object* x_837; lean_object* x_838; 
x_837 = lean_box(0);
if (lean_is_scalar(x_836)) {
 x_838 = lean_alloc_ctor(1, 2, 0);
} else {
 x_838 = x_836;
 lean_ctor_set_tag(x_838, 1);
}
lean_ctor_set(x_838, 0, x_834);
lean_ctor_set(x_838, 1, x_837);
return x_838;
}
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_915 = lean_ctor_get(x_833, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_833, 1);
lean_inc(x_916);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_917 = x_833;
} else {
 lean_dec_ref(x_833);
 x_917 = lean_box(0);
}
if (lean_is_scalar(x_917)) {
 x_918 = lean_alloc_ctor(1, 2, 0);
} else {
 x_918 = x_917;
}
lean_ctor_set(x_918, 0, x_915);
lean_ctor_set(x_918, 1, x_916);
return x_918;
}
}
block_742:
{
lean_object* x_740; lean_object* x_741; 
x_740 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_740, 0, x_736);
lean_ctor_set(x_740, 1, x_738);
lean_ctor_set(x_740, 2, x_739);
lean_ctor_set_uint8(x_740, sizeof(void*)*3, x_737);
if (lean_is_scalar(x_728)) {
 x_741 = lean_alloc_ctor(0, 2, 0);
} else {
 x_741 = x_728;
}
lean_ctor_set(x_741, 0, x_735);
lean_ctor_set(x_741, 1, x_740);
return x_741;
}
block_745:
{
lean_object* x_743; lean_object* x_744; 
x_743 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1;
x_744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_744, 0, x_735);
lean_ctor_set(x_744, 1, x_743);
return x_744;
}
block_749:
{
lean_object* x_747; lean_object* x_748; 
x_747 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_747, 0, x_746);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_735);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
block_751:
{
lean_object* x_750; 
x_750 = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
x_746 = x_750;
goto block_749;
}
}
else
{
lean_object* x_919; lean_object* x_920; 
lean_dec(x_727);
lean_dec_ref(x_1);
x_919 = lean_box(0);
if (lean_is_scalar(x_728)) {
 x_920 = lean_alloc_ctor(1, 2, 0);
} else {
 x_920 = x_728;
 lean_ctor_set_tag(x_920, 1);
}
lean_ctor_set(x_920, 0, x_726);
lean_ctor_set(x_920, 1, x_919);
return x_920;
}
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
lean_dec_ref(x_1);
x_921 = lean_ctor_get(x_725, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_725, 1);
lean_inc(x_922);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_923 = x_725;
} else {
 lean_dec_ref(x_725);
 x_923 = lean_box(0);
}
if (lean_is_scalar(x_923)) {
 x_924 = lean_alloc_ctor(1, 2, 0);
} else {
 x_924 = x_923;
}
lean_ctor_set(x_924, 0, x_921);
lean_ctor_set(x_924, 1, x_922);
return x_924;
}
}
}
else
{
lean_object* x_925; lean_object* x_926; 
lean_dec_ref(x_1);
x_925 = lean_box(0);
x_926 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_926, 0, x_2);
lean_ctor_set(x_926, 1, x_925);
return x_926;
}
block_19:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_string_utf8_next_fast(x_4, x_3);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_7, 1, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Std_Internal_Parsec_String_Parser_run___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_JsonRpc_MessageDirection_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_MessageDirection_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_JsonRpc_MessageDirection_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_JsonRpc_MessageDirection_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no inductive tag found", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("serverToClient", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clientToServer", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getTag_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2;
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3;
x_8 = lean_string_dec_eq(x_4, x_7);
lean_dec(x_4);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6;
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7;
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageDirection() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessageDirection___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessageDirection() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instToJsonMessageDirection___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_JsonRpc_MessageKind_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_MessageKind_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_JsonRpc_MessageKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_MessageKind_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_JsonRpc_MessageKind_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_MessageKind_request_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_MessageKind_request_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_MessageKind_notification_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_MessageKind_notification_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_MessageKind_response_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_MessageKind_response_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_JsonRpc_MessageKind_responseError_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("responseError", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("request", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("notification", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("response", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_getTag_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2;
x_8 = lean_string_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3;
x_10 = lean_string_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4;
x_12 = lean_string_dec_eq(x_4, x_11);
lean_dec(x_4);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5;
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6;
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7;
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8;
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_4);
x_17 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9;
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessageKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageKind___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2;
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_JsonRpc_instToJsonMessageKind_toJson(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessageKind___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessageKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instToJsonMessageKind___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 2:
{
uint8_t x_4; 
x_4 = 2;
return x_4;
}
default: 
{
uint8_t x_5; 
x_5 = 3;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_MessageKind_ofMessage(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_Structured_fromJson_x3f(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readMessage___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("JSON '", 6, 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' did not have the format of a JSON-RPC message.\n", 49, 49);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readJson(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_31; lean_object* x_32; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_6 = x_4;
} else {
 lean_dec_ref(x_4);
 x_6 = lean_box(0);
}
x_31 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
lean_inc(x_5);
x_32 = l_Lean_Json_getObjVal_x3f(x_5, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_6);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_19 = x_33;
goto block_28;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
if (lean_obj_tag(x_34) == 3)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
x_37 = lean_string_dec_eq(x_35, x_36);
lean_dec_ref(x_35);
if (x_37 == 0)
{
lean_dec(x_6);
goto block_30;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
lean_inc(x_5);
x_39 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(x_5, x_38);
if (lean_obj_tag(x_39) == 0)
{
goto block_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_39, 0);
lean_inc(x_83);
x_84 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_5);
x_85 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_5, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_dec_ref(x_85);
lean_dec(x_83);
goto block_82;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_39);
lean_dec(x_6);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_92 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_93 = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(x_5, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
lean_dec_ref(x_93);
x_94 = lean_box(0);
x_88 = x_94;
goto block_91;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
x_88 = x_93;
goto block_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_88 = x_97;
goto block_91;
}
}
block_91:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_88);
if (lean_is_scalar(x_87)) {
 x_90 = lean_alloc_ctor(0, 1, 0);
} else {
 x_90 = x_87;
 lean_ctor_set_tag(x_90, 0);
}
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
block_63:
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_6);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_19 = x_40;
goto block_28;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
lean_inc(x_5);
x_43 = l_Lean_Json_getObjVal_x3f(x_5, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
lean_dec(x_41);
lean_dec(x_6);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_19 = x_44;
goto block_28;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
lean_inc(x_45);
x_47 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(x_45, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_6);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_19 = x_48;
goto block_28;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
lean_inc(x_45);
x_51 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_45, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
lean_dec(x_49);
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_6);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_19 = x_52;
goto block_28;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_5);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_55 = l_Lean_Json_getObjVal_x3f(x_45, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
lean_dec_ref(x_55);
x_56 = lean_box(0);
x_57 = lean_unbox(x_49);
lean_dec(x_49);
x_7 = x_57;
x_8 = x_41;
x_9 = x_53;
x_10 = x_56;
goto block_13;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = lean_unbox(x_49);
lean_dec(x_49);
x_7 = x_59;
x_8 = x_41;
x_9 = x_53;
x_10 = x_55;
goto block_13;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_unbox(x_49);
lean_dec(x_49);
x_7 = x_62;
x_8 = x_41;
x_9 = x_53;
x_10 = x_61;
goto block_13;
}
}
}
}
}
}
}
block_82:
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_5);
x_65 = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_5, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_dec_ref(x_65);
if (lean_obj_tag(x_39) == 0)
{
goto block_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_39, 0);
lean_inc(x_66);
x_67 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
lean_inc(x_5);
x_68 = l_Lean_Json_getObjVal_x3f(x_5, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_dec_ref(x_68);
lean_dec(x_66);
goto block_63;
}
else
{
uint8_t x_69; 
lean_dec_ref(x_39);
lean_dec(x_6);
lean_dec(x_5);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_tag(x_68, 0);
lean_ctor_set(x_68, 0, x_71);
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_39);
lean_dec(x_6);
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
lean_dec_ref(x_65);
x_76 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_77 = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(x_5, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
lean_dec_ref(x_77);
x_78 = lean_box(0);
x_14 = x_75;
x_15 = x_78;
goto block_18;
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_77);
if (x_79 == 0)
{
x_14 = x_75;
x_15 = x_77;
goto block_18;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_14 = x_75;
x_15 = x_81;
goto block_18;
}
}
}
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_6);
goto block_30;
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_7);
if (lean_is_scalar(x_6)) {
 x_12 = lean_alloc_ctor(0, 1, 0);
} else {
 x_12 = x_6;
}
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
block_28:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = l_IO_FS_Stream_readMessage___closed__0;
x_21 = l_Lean_Json_compress(x_5);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = l_IO_FS_Stream_readMessage___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_19);
lean_dec_ref(x_19);
x_26 = lean_mk_io_user_error(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_30:
{
lean_object* x_29; 
x_29 = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
x_19 = x_29;
goto block_28;
}
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_4);
if (x_98 == 0)
{
return x_4;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_4, 0);
lean_inc(x_99);
lean_dec(x_4);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readMessage(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected method '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', got method '", 15, 15);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unexpected param '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' for method '", 14, 14);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected JSON-RPC request, got: '", 33, 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readMessage(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_8 = x_6;
} else {
 lean_dec_ref(x_6);
 x_8 = lean_box(0);
}
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_string_dec_eq(x_11, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_4);
x_14 = l_IO_FS_Stream_readRequestAs___redArg___closed__0;
x_15 = lean_string_append(x_14, x_3);
lean_dec_ref(x_3);
x_16 = l_IO_FS_Stream_readRequestAs___redArg___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_11);
lean_dec_ref(x_11);
x_19 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_mk_io_user_error(x_20);
if (lean_is_scalar(x_8)) {
 x_22 = lean_alloc_ctor(1, 1, 0);
} else {
 x_22 = x_8;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_11);
x_23 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_24 = l_Option_toJson___redArg(x_23, x_12);
lean_inc(x_24);
x_25 = lean_apply_1(x_4, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_7);
lean_dec(x_10);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_IO_FS_Stream_readRequestAs___redArg___closed__3;
x_28 = l_Lean_Json_compress(x_24);
x_29 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
x_30 = l_IO_FS_Stream_readRequestAs___redArg___closed__4;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_3);
lean_dec_ref(x_3);
x_33 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_26);
lean_dec(x_26);
x_36 = lean_mk_io_user_error(x_35);
if (lean_is_scalar(x_8)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_8;
 lean_ctor_set_tag(x_37, 1);
}
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_24);
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec_ref(x_25);
lean_ctor_set(x_7, 2, x_38);
lean_ctor_set(x_7, 1, x_3);
if (lean_is_scalar(x_8)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_8;
}
lean_ctor_set(x_39, 0, x_7);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
x_42 = lean_ctor_get(x_7, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_7);
x_43 = lean_string_dec_eq(x_41, x_3);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec_ref(x_4);
x_44 = l_IO_FS_Stream_readRequestAs___redArg___closed__0;
x_45 = lean_string_append(x_44, x_3);
lean_dec_ref(x_3);
x_46 = l_IO_FS_Stream_readRequestAs___redArg___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_string_append(x_47, x_41);
lean_dec_ref(x_41);
x_49 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_mk_io_user_error(x_50);
if (lean_is_scalar(x_8)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_8;
 lean_ctor_set_tag(x_52, 1);
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_41);
x_53 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_54 = l_Option_toJson___redArg(x_53, x_42);
lean_inc(x_54);
x_55 = lean_apply_1(x_4, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_40);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_IO_FS_Stream_readRequestAs___redArg___closed__3;
x_58 = l_Lean_Json_compress(x_54);
x_59 = lean_string_append(x_57, x_58);
lean_dec_ref(x_58);
x_60 = l_IO_FS_Stream_readRequestAs___redArg___closed__4;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_3);
lean_dec_ref(x_3);
x_63 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_56);
lean_dec(x_56);
x_66 = lean_mk_io_user_error(x_65);
if (lean_is_scalar(x_8)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_8;
 lean_ctor_set_tag(x_67, 1);
}
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
x_68 = lean_ctor_get(x_55, 0);
lean_inc(x_68);
lean_dec_ref(x_55);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_40);
lean_ctor_set(x_69, 1, x_3);
lean_ctor_set(x_69, 2, x_68);
if (lean_is_scalar(x_8)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_8;
}
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_71 = l_IO_FS_Stream_readRequestAs___redArg___closed__6;
x_72 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_73 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_7, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_7, 2);
lean_inc(x_86);
lean_dec_ref(x_7);
x_87 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_84);
if (x_100 == 0)
{
lean_ctor_set_tag(x_84, 3);
x_88 = x_84;
goto block_99;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_84, 0);
lean_inc(x_101);
lean_dec(x_84);
x_102 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_88 = x_102;
goto block_99;
}
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_84);
if (x_103 == 0)
{
lean_ctor_set_tag(x_84, 2);
x_88 = x_84;
goto block_99;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_84, 0);
lean_inc(x_104);
lean_dec(x_84);
x_105 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_88 = x_105;
goto block_99;
}
}
block_99:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_91 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_91, 0, x_85);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_97 = l_Lean_Json_opt___redArg(x_72, x_96, x_86);
x_98 = l_List_appendTR___redArg(x_95, x_97);
x_74 = x_98;
goto block_83;
}
}
case 1:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_7, 1);
lean_inc(x_107);
lean_dec_ref(x_7);
x_108 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_109 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_109, 0, x_106);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_112 = l_Lean_Json_opt___redArg(x_72, x_111, x_107);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
x_74 = x_113;
goto block_83;
}
case 2:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_7, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_7, 1);
lean_inc(x_115);
lean_dec_ref(x_7);
x_116 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_114);
if (x_125 == 0)
{
lean_ctor_set_tag(x_114, 3);
x_117 = x_114;
goto block_124;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_114, 0);
lean_inc(x_126);
lean_dec(x_114);
x_127 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_117 = x_127;
goto block_124;
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_114);
if (x_128 == 0)
{
lean_ctor_set_tag(x_114, 2);
x_117 = x_114;
goto block_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_114, 0);
lean_inc(x_129);
lean_dec(x_114);
x_130 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_117 = x_130;
goto block_124;
}
}
block_124:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_115);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_122);
x_74 = x_123;
goto block_83;
}
}
default: 
{
lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_155; lean_object* x_156; 
x_131 = lean_ctor_get(x_7, 0);
lean_inc(x_131);
x_132 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_133 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_7, 2);
lean_inc(x_134);
lean_dec_ref(x_7);
x_135 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_155 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_131);
if (x_173 == 0)
{
lean_ctor_set_tag(x_131, 3);
x_156 = x_131;
goto block_172;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_131, 0);
lean_inc(x_174);
lean_dec(x_131);
x_175 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_156 = x_175;
goto block_172;
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_131);
if (x_176 == 0)
{
lean_ctor_set_tag(x_131, 2);
x_156 = x_131;
goto block_172;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_131, 0);
lean_inc(x_177);
lean_dec(x_131);
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_156 = x_178;
goto block_172;
}
}
block_154:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
x_142 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_142, 0, x_133);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_148 = l_Lean_Json_opt___redArg(x_135, x_147, x_134);
x_149 = l_List_appendTR___redArg(x_146, x_148);
x_150 = l_Lean_Json_mkObj(x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_136);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_144);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_137);
lean_ctor_set(x_153, 1, x_152);
x_74 = x_153;
goto block_83;
}
block_172:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_159 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
switch (x_132) {
case 0:
{
lean_object* x_160; 
x_160 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_160;
goto block_154;
}
case 1:
{
lean_object* x_161; 
x_161 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_161;
goto block_154;
}
case 2:
{
lean_object* x_162; 
x_162 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_162;
goto block_154;
}
case 3:
{
lean_object* x_163; 
x_163 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_163;
goto block_154;
}
case 4:
{
lean_object* x_164; 
x_164 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_164;
goto block_154;
}
case 5:
{
lean_object* x_165; 
x_165 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_165;
goto block_154;
}
case 6:
{
lean_object* x_166; 
x_166 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_166;
goto block_154;
}
case 7:
{
lean_object* x_167; 
x_167 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_167;
goto block_154;
}
case 8:
{
lean_object* x_168; 
x_168 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_168;
goto block_154;
}
case 9:
{
lean_object* x_169; 
x_169 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_169;
goto block_154;
}
case 10:
{
lean_object* x_170; 
x_170 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_170;
goto block_154;
}
default: 
{
lean_object* x_171; 
x_171 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
x_136 = x_158;
x_137 = x_157;
x_138 = x_159;
x_139 = x_171;
goto block_154;
}
}
}
}
}
block_83:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Json_mkObj(x_75);
x_77 = l_Lean_Json_compress(x_76);
x_78 = lean_string_append(x_71, x_77);
lean_dec_ref(x_77);
x_79 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_mk_io_user_error(x_80);
if (lean_is_scalar(x_8)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_8;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
uint8_t x_179; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_179 = !lean_is_exclusive(x_6);
if (x_179 == 0)
{
return x_6;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_6, 0);
lean_inc(x_180);
lean_dec(x_6);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readRequestAs___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readRequestAs___redArg(x_1, x_2, x_3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readRequestAs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected JSON-RPC notification, got: '", 38, 38);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readMessage(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_8 = x_6;
} else {
 lean_dec_ref(x_6);
 x_8 = lean_box(0);
}
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_string_dec_eq(x_10, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec_ref(x_4);
x_13 = l_IO_FS_Stream_readRequestAs___redArg___closed__0;
x_14 = lean_string_append(x_13, x_3);
lean_dec_ref(x_3);
x_15 = l_IO_FS_Stream_readRequestAs___redArg___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_10);
lean_dec_ref(x_10);
x_18 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_mk_io_user_error(x_19);
if (lean_is_scalar(x_8)) {
 x_21 = lean_alloc_ctor(1, 1, 0);
} else {
 x_21 = x_8;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_10);
x_22 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_23 = l_Option_toJson___redArg(x_22, x_11);
lean_inc(x_23);
x_24 = lean_apply_1(x_4, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_7);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_IO_FS_Stream_readRequestAs___redArg___closed__3;
x_27 = l_Lean_Json_compress(x_23);
x_28 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
x_29 = l_IO_FS_Stream_readRequestAs___redArg___closed__4;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_3);
lean_dec_ref(x_3);
x_32 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_25);
lean_dec(x_25);
x_35 = lean_mk_io_user_error(x_34);
if (lean_is_scalar(x_8)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_8;
 lean_ctor_set_tag(x_36, 1);
}
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_37 = lean_ctor_get(x_24, 0);
lean_inc(x_37);
lean_dec_ref(x_24);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_37);
lean_ctor_set(x_7, 0, x_3);
if (lean_is_scalar(x_8)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_8;
}
lean_ctor_set(x_38, 0, x_7);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_7);
x_41 = lean_string_dec_eq(x_39, x_3);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_40);
lean_dec_ref(x_4);
x_42 = l_IO_FS_Stream_readRequestAs___redArg___closed__0;
x_43 = lean_string_append(x_42, x_3);
lean_dec_ref(x_3);
x_44 = l_IO_FS_Stream_readRequestAs___redArg___closed__1;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_string_append(x_45, x_39);
lean_dec_ref(x_39);
x_47 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_mk_io_user_error(x_48);
if (lean_is_scalar(x_8)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_8;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_39);
x_51 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_52 = l_Option_toJson___redArg(x_51, x_40);
lean_inc(x_52);
x_53 = lean_apply_1(x_4, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_IO_FS_Stream_readRequestAs___redArg___closed__3;
x_56 = l_Lean_Json_compress(x_52);
x_57 = lean_string_append(x_55, x_56);
lean_dec_ref(x_56);
x_58 = l_IO_FS_Stream_readRequestAs___redArg___closed__4;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_string_append(x_59, x_3);
lean_dec_ref(x_3);
x_61 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_54);
lean_dec(x_54);
x_64 = lean_mk_io_user_error(x_63);
if (lean_is_scalar(x_8)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_8;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_52);
x_66 = lean_ctor_get(x_53, 0);
lean_inc(x_66);
lean_dec_ref(x_53);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_3);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_8)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_8;
}
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_69 = l_IO_FS_Stream_readNotificationAs___redArg___closed__0;
x_70 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_71 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_7, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_7, 2);
lean_inc(x_84);
lean_dec_ref(x_7);
x_85 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_82);
if (x_98 == 0)
{
lean_ctor_set_tag(x_82, 3);
x_86 = x_82;
goto block_97;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_82, 0);
lean_inc(x_99);
lean_dec(x_82);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_86 = x_100;
goto block_97;
}
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_82);
if (x_101 == 0)
{
lean_ctor_set_tag(x_82, 2);
x_86 = x_82;
goto block_97;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_82, 0);
lean_inc(x_102);
lean_dec(x_82);
x_103 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_86 = x_103;
goto block_97;
}
}
block_97:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_83);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_95 = l_Lean_Json_opt___redArg(x_70, x_94, x_84);
x_96 = l_List_appendTR___redArg(x_93, x_95);
x_72 = x_96;
goto block_81;
}
}
case 1:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_7, 1);
lean_inc(x_105);
lean_dec_ref(x_7);
x_106 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_104);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_110 = l_Lean_Json_opt___redArg(x_70, x_109, x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
x_72 = x_111;
goto block_81;
}
case 2:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_7, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_7, 1);
lean_inc(x_113);
lean_dec_ref(x_7);
x_114 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_112);
if (x_123 == 0)
{
lean_ctor_set_tag(x_112, 3);
x_115 = x_112;
goto block_122;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_112, 0);
lean_inc(x_124);
lean_dec(x_112);
x_125 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_115 = x_125;
goto block_122;
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_112);
if (x_126 == 0)
{
lean_ctor_set_tag(x_112, 2);
x_115 = x_112;
goto block_122;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_112, 0);
lean_inc(x_127);
lean_dec(x_112);
x_128 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_115 = x_128;
goto block_122;
}
}
block_122:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_113);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_120);
x_72 = x_121;
goto block_81;
}
}
default: 
{
lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_153; lean_object* x_154; 
x_129 = lean_ctor_get(x_7, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_131 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_7, 2);
lean_inc(x_132);
lean_dec_ref(x_7);
x_133 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_153 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_129);
if (x_171 == 0)
{
lean_ctor_set_tag(x_129, 3);
x_154 = x_129;
goto block_170;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_129, 0);
lean_inc(x_172);
lean_dec(x_129);
x_173 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_154 = x_173;
goto block_170;
}
}
else
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_129);
if (x_174 == 0)
{
lean_ctor_set_tag(x_129, 2);
x_154 = x_129;
goto block_170;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_129, 0);
lean_inc(x_175);
lean_dec(x_129);
x_176 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_154 = x_176;
goto block_170;
}
}
block_152:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
x_140 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_140, 0, x_131);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_146 = l_Lean_Json_opt___redArg(x_133, x_145, x_132);
x_147 = l_List_appendTR___redArg(x_144, x_146);
x_148 = l_Lean_Json_mkObj(x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_136);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_142);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_134);
lean_ctor_set(x_151, 1, x_150);
x_72 = x_151;
goto block_81;
}
block_170:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_157 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
switch (x_130) {
case 0:
{
lean_object* x_158; 
x_158 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_158;
goto block_152;
}
case 1:
{
lean_object* x_159; 
x_159 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_159;
goto block_152;
}
case 2:
{
lean_object* x_160; 
x_160 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_160;
goto block_152;
}
case 3:
{
lean_object* x_161; 
x_161 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_161;
goto block_152;
}
case 4:
{
lean_object* x_162; 
x_162 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_162;
goto block_152;
}
case 5:
{
lean_object* x_163; 
x_163 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_163;
goto block_152;
}
case 6:
{
lean_object* x_164; 
x_164 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_164;
goto block_152;
}
case 7:
{
lean_object* x_165; 
x_165 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_165;
goto block_152;
}
case 8:
{
lean_object* x_166; 
x_166 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_166;
goto block_152;
}
case 9:
{
lean_object* x_167; 
x_167 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_167;
goto block_152;
}
case 10:
{
lean_object* x_168; 
x_168 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_168;
goto block_152;
}
default: 
{
lean_object* x_169; 
x_169 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
x_134 = x_155;
x_135 = x_157;
x_136 = x_156;
x_137 = x_169;
goto block_152;
}
}
}
}
}
block_81:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Json_mkObj(x_73);
x_75 = l_Lean_Json_compress(x_74);
x_76 = lean_string_append(x_69, x_75);
lean_dec_ref(x_75);
x_77 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_78 = lean_string_append(x_76, x_77);
x_79 = lean_mk_io_user_error(x_78);
if (lean_is_scalar(x_8)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_8;
 lean_ctor_set_tag(x_80, 1);
}
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
uint8_t x_177; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_177 = !lean_is_exclusive(x_6);
if (x_177 == 0)
{
return x_6;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_6, 0);
lean_inc(x_178);
lean_dec(x_6);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readNotificationAs___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readNotificationAs___redArg(x_1, x_2, x_3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readNotificationAs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected id ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", got id ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unexpected result '", 19, 19);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected JSON-RPC response, got: '", 34, 34);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readMessage(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_8 = x_6;
} else {
 lean_dec_ref(x_6);
 x_8 = lean_box(0);
}
if (lean_obj_tag(x_7) == 2)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
x_18 = l_Lean_JsonRpc_instBEqRequestID_beq(x_16, x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
lean_dec(x_17);
lean_dec_ref(x_4);
x_19 = l_IO_FS_Stream_readResponseAs___redArg___closed__0;
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_31);
lean_dec_ref(x_3);
x_32 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
x_33 = lean_string_append(x_32, x_31);
lean_dec_ref(x_31);
x_34 = lean_string_append(x_33, x_32);
x_20 = x_34;
goto block_30;
}
case 1:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_35);
lean_dec_ref(x_3);
x_36 = l_Lean_JsonNumber_toString(x_35);
x_20 = x_36;
goto block_30;
}
default: 
{
lean_object* x_37; 
x_37 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
x_20 = x_37;
goto block_30;
}
}
block_30:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = l_IO_FS_Stream_readResponseAs___redArg___closed__1;
x_23 = lean_string_append(x_21, x_22);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_16);
x_25 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
x_26 = lean_string_append(x_25, x_24);
lean_dec_ref(x_24);
x_27 = lean_string_append(x_26, x_25);
x_9 = x_23;
x_10 = x_27;
goto block_14;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_16);
x_29 = l_Lean_JsonNumber_toString(x_28);
x_9 = x_23;
x_10 = x_29;
goto block_14;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_16);
lean_dec(x_8);
lean_inc(x_17);
x_38 = lean_apply_1(x_4, x_17);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_free_object(x_7);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l_IO_FS_Stream_readResponseAs___redArg___closed__2;
x_42 = l_Lean_Json_compress(x_17);
x_43 = lean_string_append(x_41, x_42);
lean_dec_ref(x_42);
x_44 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_string_append(x_45, x_40);
lean_dec(x_40);
x_47 = lean_mk_io_user_error(x_46);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = l_IO_FS_Stream_readResponseAs___redArg___closed__2;
x_50 = l_Lean_Json_compress(x_17);
x_51 = lean_string_append(x_49, x_50);
lean_dec_ref(x_50);
x_52 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_string_append(x_53, x_48);
lean_dec(x_48);
x_55 = lean_mk_io_user_error(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_17);
x_57 = !lean_is_exclusive(x_38);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_38, 0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_58);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set_tag(x_38, 0);
lean_ctor_set(x_38, 0, x_7);
return x_38;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_38, 0);
lean_inc(x_59);
lean_dec(x_38);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_59);
lean_ctor_set(x_7, 0, x_3);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_7);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_7, 0);
x_62 = lean_ctor_get(x_7, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_7);
x_63 = l_Lean_JsonRpc_instBEqRequestID_beq(x_61, x_3);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
lean_dec_ref(x_4);
x_64 = l_IO_FS_Stream_readResponseAs___redArg___closed__0;
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_76);
lean_dec_ref(x_3);
x_77 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
x_78 = lean_string_append(x_77, x_76);
lean_dec_ref(x_76);
x_79 = lean_string_append(x_78, x_77);
x_65 = x_79;
goto block_75;
}
case 1:
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_80);
lean_dec_ref(x_3);
x_81 = l_Lean_JsonNumber_toString(x_80);
x_65 = x_81;
goto block_75;
}
default: 
{
lean_object* x_82; 
x_82 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
x_65 = x_82;
goto block_75;
}
}
block_75:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_string_append(x_64, x_65);
lean_dec_ref(x_65);
x_67 = l_IO_FS_Stream_readResponseAs___redArg___closed__1;
x_68 = lean_string_append(x_66, x_67);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_69);
lean_dec_ref(x_61);
x_70 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
x_71 = lean_string_append(x_70, x_69);
lean_dec_ref(x_69);
x_72 = lean_string_append(x_71, x_70);
x_9 = x_68;
x_10 = x_72;
goto block_14;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_73);
lean_dec_ref(x_61);
x_74 = l_Lean_JsonNumber_toString(x_73);
x_9 = x_68;
x_10 = x_74;
goto block_14;
}
}
}
else
{
lean_object* x_83; 
lean_dec(x_61);
lean_dec(x_8);
lean_inc(x_62);
x_83 = lean_apply_1(x_4, x_62);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_3);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = l_IO_FS_Stream_readResponseAs___redArg___closed__2;
x_87 = l_Lean_Json_compress(x_62);
x_88 = lean_string_append(x_86, x_87);
lean_dec_ref(x_87);
x_89 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_string_append(x_90, x_84);
lean_dec(x_84);
x_92 = lean_mk_io_user_error(x_91);
if (lean_is_scalar(x_85)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_85;
 lean_ctor_set_tag(x_93, 1);
}
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_62);
x_94 = lean_ctor_get(x_83, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_95 = x_83;
} else {
 lean_dec_ref(x_83);
 x_95 = lean_box(0);
}
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_3);
lean_ctor_set(x_96, 1, x_94);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 1, 0);
} else {
 x_97 = x_95;
 lean_ctor_set_tag(x_97, 0);
}
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
x_98 = l_IO_FS_Stream_readResponseAs___redArg___closed__3;
x_99 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_100 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_7, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_7, 2);
lean_inc(x_113);
lean_dec_ref(x_7);
x_114 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_111);
if (x_127 == 0)
{
lean_ctor_set_tag(x_111, 3);
x_115 = x_111;
goto block_126;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_111, 0);
lean_inc(x_128);
lean_dec(x_111);
x_129 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_115 = x_129;
goto block_126;
}
}
else
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_111);
if (x_130 == 0)
{
lean_ctor_set_tag(x_111, 2);
x_115 = x_111;
goto block_126;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_111, 0);
lean_inc(x_131);
lean_dec(x_111);
x_132 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_115 = x_132;
goto block_126;
}
}
block_126:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_118 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_118, 0, x_112);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_116);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_124 = l_Lean_Json_opt___redArg(x_99, x_123, x_113);
x_125 = l_List_appendTR___redArg(x_122, x_124);
x_101 = x_125;
goto block_110;
}
}
case 1:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_133 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_7, 1);
lean_inc(x_134);
lean_dec_ref(x_7);
x_135 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_136 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_136, 0, x_133);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_139 = l_Lean_Json_opt___redArg(x_99, x_138, x_134);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
x_101 = x_140;
goto block_110;
}
case 2:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_7, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_7, 1);
lean_inc(x_142);
lean_dec_ref(x_7);
x_143 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_141);
if (x_152 == 0)
{
lean_ctor_set_tag(x_141, 3);
x_144 = x_141;
goto block_151;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_141, 0);
lean_inc(x_153);
lean_dec(x_141);
x_154 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_144 = x_154;
goto block_151;
}
}
else
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_141);
if (x_155 == 0)
{
lean_ctor_set_tag(x_141, 2);
x_144 = x_141;
goto block_151;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_141, 0);
lean_inc(x_156);
lean_dec(x_141);
x_157 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_144 = x_157;
goto block_151;
}
}
block_151:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_142);
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_145);
lean_ctor_set(x_150, 1, x_149);
x_101 = x_150;
goto block_110;
}
}
default: 
{
lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_182; lean_object* x_183; 
x_158 = lean_ctor_get(x_7, 0);
lean_inc(x_158);
x_159 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_160 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_160);
x_161 = lean_ctor_get(x_7, 2);
lean_inc(x_161);
lean_dec_ref(x_7);
x_162 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_182 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_158);
if (x_200 == 0)
{
lean_ctor_set_tag(x_158, 3);
x_183 = x_158;
goto block_199;
}
else
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_158, 0);
lean_inc(x_201);
lean_dec(x_158);
x_202 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_183 = x_202;
goto block_199;
}
}
else
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_158);
if (x_203 == 0)
{
lean_ctor_set_tag(x_158, 2);
x_183 = x_158;
goto block_199;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_158, 0);
lean_inc(x_204);
lean_dec(x_158);
x_205 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_183 = x_205;
goto block_199;
}
}
block_181:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
x_169 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_169, 0, x_160);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_167);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_175 = l_Lean_Json_opt___redArg(x_162, x_174, x_161);
x_176 = l_List_appendTR___redArg(x_173, x_175);
x_177 = l_Lean_Json_mkObj(x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_163);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_171);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_164);
lean_ctor_set(x_180, 1, x_179);
x_101 = x_180;
goto block_110;
}
block_199:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_186 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
switch (x_159) {
case 0:
{
lean_object* x_187; 
x_187 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_187;
goto block_181;
}
case 1:
{
lean_object* x_188; 
x_188 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_188;
goto block_181;
}
case 2:
{
lean_object* x_189; 
x_189 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_189;
goto block_181;
}
case 3:
{
lean_object* x_190; 
x_190 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_190;
goto block_181;
}
case 4:
{
lean_object* x_191; 
x_191 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_191;
goto block_181;
}
case 5:
{
lean_object* x_192; 
x_192 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_192;
goto block_181;
}
case 6:
{
lean_object* x_193; 
x_193 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_193;
goto block_181;
}
case 7:
{
lean_object* x_194; 
x_194 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_194;
goto block_181;
}
case 8:
{
lean_object* x_195; 
x_195 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_195;
goto block_181;
}
case 9:
{
lean_object* x_196; 
x_196 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_196;
goto block_181;
}
case 10:
{
lean_object* x_197; 
x_197 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_197;
goto block_181;
}
default: 
{
lean_object* x_198; 
x_198 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
x_163 = x_185;
x_164 = x_184;
x_165 = x_186;
x_166 = x_198;
goto block_181;
}
}
}
}
}
block_110:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Json_mkObj(x_102);
x_104 = l_Lean_Json_compress(x_103);
x_105 = lean_string_append(x_98, x_104);
lean_dec_ref(x_104);
x_106 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_107 = lean_string_append(x_105, x_106);
x_108 = lean_mk_io_user_error(x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = lean_mk_io_user_error(x_11);
if (lean_is_scalar(x_8)) {
 x_13 = lean_alloc_ctor(1, 1, 0);
} else {
 x_13 = x_8;
 lean_ctor_set_tag(x_13, 1);
}
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_206; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_206 = !lean_is_exclusive(x_6);
if (x_206 == 0)
{
return x_6;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_6, 0);
lean_inc(x_207);
lean_dec(x_6);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
return x_208;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readResponseAs___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readResponseAs___redArg(x_1, x_2, x_3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readResponseAs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Json_Structured_toJson(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
switch (lean_obj_tag(x_10)) {
case 0:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_ctor_set_tag(x_10, 3);
x_14 = x_10;
goto block_25;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_14 = x_28;
goto block_25;
}
}
case 1:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
lean_ctor_set_tag(x_10, 2);
x_14 = x_10;
goto block_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_14 = x_31;
goto block_25;
}
}
default: 
{
lean_object* x_32; 
x_32 = lean_box(0);
x_14 = x_32;
goto block_25;
}
}
block_25:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_23 = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(x_22, x_12);
x_24 = l_List_appendTR___redArg(x_21, x_23);
x_5 = x_24;
goto block_9;
}
}
case 1:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_37);
lean_ctor_set(x_2, 0, x_36);
x_38 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_39 = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(x_38, x_35);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_39);
x_5 = x_40;
goto block_9;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_2);
x_43 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_47 = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(x_46, x_42);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_5 = x_48;
goto block_9;
}
}
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_51 = x_2;
} else {
 lean_dec_ref(x_2);
 x_51 = lean_box(0);
}
x_52 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
switch (lean_obj_tag(x_49)) {
case 0:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_49);
if (x_61 == 0)
{
lean_ctor_set_tag(x_49, 3);
x_53 = x_49;
goto block_60;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_49, 0);
lean_inc(x_62);
lean_dec(x_49);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_53 = x_63;
goto block_60;
}
}
case 1:
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_49);
if (x_64 == 0)
{
lean_ctor_set_tag(x_49, 2);
x_53 = x_49;
goto block_60;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_49, 0);
lean_inc(x_65);
lean_dec(x_49);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_53 = x_66;
goto block_60;
}
}
default: 
{
lean_object* x_67; 
x_67 = lean_box(0);
x_53 = x_67;
goto block_60;
}
}
block_60:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_5 = x_59;
goto block_9;
}
}
default: 
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_91; lean_object* x_92; 
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_70 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_2, 2);
lean_inc(x_71);
lean_dec_ref(x_2);
x_91 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
switch (lean_obj_tag(x_68)) {
case 0:
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_68);
if (x_109 == 0)
{
lean_ctor_set_tag(x_68, 3);
x_92 = x_68;
goto block_108;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_68, 0);
lean_inc(x_110);
lean_dec(x_68);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_92 = x_111;
goto block_108;
}
}
case 1:
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_68);
if (x_112 == 0)
{
lean_ctor_set_tag(x_68, 2);
x_92 = x_68;
goto block_108;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_68, 0);
lean_inc(x_113);
lean_dec(x_68);
x_114 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_92 = x_114;
goto block_108;
}
}
default: 
{
lean_object* x_115; 
x_115 = lean_box(0);
x_92 = x_115;
goto block_108;
}
}
block_90:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_70);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_84 = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(x_83, x_71);
lean_dec(x_71);
x_85 = l_List_appendTR___redArg(x_82, x_84);
x_86 = l_Lean_Json_mkObj(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_73);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_80);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
x_5 = x_89;
goto block_9;
}
block_108:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_95 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
switch (x_69) {
case 0:
{
lean_object* x_96; 
x_96 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_96;
goto block_90;
}
case 1:
{
lean_object* x_97; 
x_97 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_97;
goto block_90;
}
case 2:
{
lean_object* x_98; 
x_98 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_98;
goto block_90;
}
case 3:
{
lean_object* x_99; 
x_99 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_99;
goto block_90;
}
case 4:
{
lean_object* x_100; 
x_100 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_100;
goto block_90;
}
case 5:
{
lean_object* x_101; 
x_101 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_101;
goto block_90;
}
case 6:
{
lean_object* x_102; 
x_102 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_102;
goto block_90;
}
case 7:
{
lean_object* x_103; 
x_103 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_103;
goto block_90;
}
case 8:
{
lean_object* x_104; 
x_104 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_104;
goto block_90;
}
case 9:
{
lean_object* x_105; 
x_105 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_105;
goto block_90;
}
case 10:
{
lean_object* x_106; 
x_106 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_106;
goto block_90;
}
default: 
{
lean_object* x_107; 
x_107 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
x_72 = x_95;
x_73 = x_94;
x_74 = x_93;
x_75 = x_107;
goto block_90;
}
}
}
}
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Json_mkObj(x_6);
x_8 = l_IO_FS_Stream_writeJson(x_1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeMessage(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_8 = x_3;
} else {
 lean_dec_ref(x_3);
 x_8 = lean_box(0);
}
x_13 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec_ref(x_13);
x_14 = lean_box(0);
x_9 = x_14;
goto block_12;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
x_9 = x_13;
goto block_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_9 = x_17;
goto block_12;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
if (lean_is_scalar(x_8)) {
 x_10 = lean_alloc_ctor(0, 3, 0);
} else {
 x_10 = x_8;
}
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_IO_FS_Stream_writeMessage(x_2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeRequest___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeRequest___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeRequest(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_12 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_12);
x_13 = lean_box(0);
x_8 = x_13;
goto block_11;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
x_8 = x_12;
goto block_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_8 = x_16;
goto block_11;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(1, 2, 0);
} else {
 x_9 = x_7;
 lean_ctor_set_tag(x_9, 1);
}
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_IO_FS_Stream_writeMessage(x_2, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeNotification___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeNotification___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeNotification(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_apply_1(x_1, x_6);
lean_ctor_set_tag(x_3, 2);
lean_ctor_set(x_3, 1, x_7);
x_8 = l_IO_FS_Stream_writeMessage(x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_IO_FS_Stream_writeMessage(x_2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeResponse___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeResponse___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeResponse(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 2, x_6);
x_7 = l_IO_FS_Stream_writeMessage(x_1, x_2);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_8);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_9);
x_13 = l_IO_FS_Stream_writeMessage(x_1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeResponseError(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_14; 
lean_dec_ref(x_1);
x_14 = lean_box(0);
x_10 = x_14;
goto block_13;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_apply_1(x_1, x_16);
lean_ctor_set(x_8, 0, x_17);
x_10 = x_8;
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_apply_1(x_1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_10 = x_20;
goto block_13;
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
if (lean_is_scalar(x_9)) {
 x_11 = lean_alloc_ctor(3, 3, 1);
} else {
 x_11 = x_9;
 lean_ctor_set_tag(x_11, 3);
}
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_6);
x_12 = l_IO_FS_Stream_writeMessage(x_2, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeResponseErrorWithData___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeResponseErrorWithData___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeResponseErrorWithData(x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Lean_Data_Json_Stream(uint8_t builtin);
lean_object* initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0 = _init_l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0);
l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1 = _init_l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1);
l_Lean_JsonRpc_instInhabitedRequestID_default = _init_l_Lean_JsonRpc_instInhabitedRequestID_default();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedRequestID_default);
l_Lean_JsonRpc_instInhabitedRequestID = _init_l_Lean_JsonRpc_instInhabitedRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedRequestID);
l_Lean_JsonRpc_instBEqRequestID___closed__0 = _init_l_Lean_JsonRpc_instBEqRequestID___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instBEqRequestID___closed__0);
l_Lean_JsonRpc_instBEqRequestID = _init_l_Lean_JsonRpc_instBEqRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instBEqRequestID);
l_Lean_JsonRpc_instHashableRequestID___closed__0 = _init_l_Lean_JsonRpc_instHashableRequestID___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instHashableRequestID___closed__0);
l_Lean_JsonRpc_instHashableRequestID = _init_l_Lean_JsonRpc_instHashableRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instHashableRequestID);
l_Lean_JsonRpc_instOrdRequestID___closed__0 = _init_l_Lean_JsonRpc_instOrdRequestID___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instOrdRequestID___closed__0);
l_Lean_JsonRpc_instOrdRequestID = _init_l_Lean_JsonRpc_instOrdRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instOrdRequestID);
l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0 = _init_l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0);
l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1 = _init_l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1);
l_Lean_JsonRpc_instToStringRequestID___closed__0 = _init_l_Lean_JsonRpc_instToStringRequestID___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToStringRequestID___closed__0);
l_Lean_JsonRpc_instToStringRequestID = _init_l_Lean_JsonRpc_instToStringRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instToStringRequestID);
l_Lean_JsonRpc_instInhabitedErrorCode_default = _init_l_Lean_JsonRpc_instInhabitedErrorCode_default();
l_Lean_JsonRpc_instInhabitedErrorCode = _init_l_Lean_JsonRpc_instInhabitedErrorCode();
l_Lean_JsonRpc_instBEqErrorCode___closed__0 = _init_l_Lean_JsonRpc_instBEqErrorCode___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instBEqErrorCode___closed__0);
l_Lean_JsonRpc_instBEqErrorCode = _init_l_Lean_JsonRpc_instBEqErrorCode();
lean_mark_persistent(l_Lean_JsonRpc_instBEqErrorCode);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36);
l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__0 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__0);
l_Lean_JsonRpc_instFromJsonErrorCode = _init_l_Lean_JsonRpc_instFromJsonErrorCode();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22);
l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23 = _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
l_Lean_JsonRpc_instToJsonErrorCode___closed__0 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__0);
l_Lean_JsonRpc_instToJsonErrorCode = _init_l_Lean_JsonRpc_instToJsonErrorCode();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode);
l_Lean_JsonRpc_instInhabitedMessage_default___closed__0 = _init_l_Lean_JsonRpc_instInhabitedMessage_default___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedMessage_default___closed__0);
l_Lean_JsonRpc_instInhabitedMessage_default = _init_l_Lean_JsonRpc_instInhabitedMessage_default();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedMessage_default);
l_Lean_JsonRpc_instInhabitedMessage = _init_l_Lean_JsonRpc_instInhabitedMessage();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedMessage);
l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0 = _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
l_Lean_JsonRpc_instInhabitedResponseError___closed__0 = _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedResponseError___closed__0);
l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0 = _init_l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0);
l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage = _init_l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage();
lean_mark_persistent(l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage);
l_Lean_JsonRpc_instCoeStringRequestID___closed__0 = _init_l_Lean_JsonRpc_instCoeStringRequestID___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instCoeStringRequestID___closed__0);
l_Lean_JsonRpc_instCoeStringRequestID = _init_l_Lean_JsonRpc_instCoeStringRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instCoeStringRequestID);
l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0 = _init_l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0);
l_Lean_JsonRpc_instCoeJsonNumberRequestID = _init_l_Lean_JsonRpc_instCoeJsonNumberRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instCoeJsonNumberRequestID);
l_Lean_JsonRpc_RequestID_ltProp = _init_l_Lean_JsonRpc_RequestID_ltProp();
lean_mark_persistent(l_Lean_JsonRpc_RequestID_ltProp);
l_Lean_JsonRpc_instLTRequestID = _init_l_Lean_JsonRpc_instLTRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instLTRequestID);
l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0 = _init_l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0);
l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1 = _init_l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1);
l_Lean_JsonRpc_instFromJsonRequestID___closed__0 = _init_l_Lean_JsonRpc_instFromJsonRequestID___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonRequestID___closed__0);
l_Lean_JsonRpc_instFromJsonRequestID = _init_l_Lean_JsonRpc_instFromJsonRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonRequestID);
l_Lean_JsonRpc_instToJsonRequestID___closed__0 = _init_l_Lean_JsonRpc_instToJsonRequestID___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonRequestID___closed__0);
l_Lean_JsonRpc_instToJsonRequestID = _init_l_Lean_JsonRpc_instToJsonRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonRequestID);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10);
l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11 = _init_l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11);
l_Lean_JsonRpc_instToJsonMessage___closed__0 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__0);
l_Lean_JsonRpc_instToJsonMessage___closed__1 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__1);
l_Lean_JsonRpc_instToJsonMessage___closed__2 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__2);
l_Lean_JsonRpc_instToJsonMessage = _init_l_Lean_JsonRpc_instToJsonMessage();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage);
l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0 = _init_l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0);
l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1 = _init_l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1);
l_Lean_JsonRpc_instFromJsonMessage___closed__0 = _init_l_Lean_JsonRpc_instFromJsonMessage___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessage___closed__0);
l_Lean_JsonRpc_instFromJsonMessage___closed__1 = _init_l_Lean_JsonRpc_instFromJsonMessage___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessage___closed__1);
l_Lean_JsonRpc_instFromJsonMessage___closed__2 = _init_l_Lean_JsonRpc_instFromJsonMessage___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessage___closed__2);
l_Lean_JsonRpc_instFromJsonMessage = _init_l_Lean_JsonRpc_instFromJsonMessage();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessage);
l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0 = _init_l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0);
l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1 = _init_l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1);
l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2 = _init_l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2);
l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0 = _init_l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0);
l_Lean_JsonRpc_instInhabitedMessageMetaData_default = _init_l_Lean_JsonRpc_instInhabitedMessageMetaData_default();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedMessageMetaData_default);
l_Lean_JsonRpc_instInhabitedMessageMetaData = _init_l_Lean_JsonRpc_instInhabitedMessageMetaData();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedMessageMetaData);
l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0 = _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0();
lean_mark_persistent(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0);
l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1 = _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1();
lean_mark_persistent(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1);
l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0 = _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0();
lean_mark_persistent(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0);
l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1 = _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1();
lean_mark_persistent(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1);
l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2 = _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2();
lean_mark_persistent(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2);
l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3 = _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3();
lean_mark_persistent(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3);
l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4 = _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4();
lean_mark_persistent(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4);
l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5 = _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5();
lean_mark_persistent(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5);
l_Lean_JsonRpc_instInhabitedMessageDirection_default = _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default();
l_Lean_JsonRpc_instInhabitedMessageDirection = _init_l_Lean_JsonRpc_instInhabitedMessageDirection();
l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0 = _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0);
l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1 = _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1);
l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2 = _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2);
l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3 = _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3);
l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4 = _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4);
l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5 = _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5);
l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6 = _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6);
l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7 = _init_l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7);
l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0 = _init_l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0);
l_Lean_JsonRpc_instFromJsonMessageDirection = _init_l_Lean_JsonRpc_instFromJsonMessageDirection();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageDirection);
l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0 = _init_l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0);
l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1 = _init_l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1);
l_Lean_JsonRpc_instToJsonMessageDirection___closed__0 = _init_l_Lean_JsonRpc_instToJsonMessageDirection___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessageDirection___closed__0);
l_Lean_JsonRpc_instToJsonMessageDirection = _init_l_Lean_JsonRpc_instToJsonMessageDirection();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessageDirection);
l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0 = _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0);
l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1 = _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1);
l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2 = _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2);
l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3 = _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3);
l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4 = _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4);
l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5 = _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5);
l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6 = _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6);
l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7 = _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7);
l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8 = _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8);
l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9 = _init_l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9);
l_Lean_JsonRpc_instFromJsonMessageKind___closed__0 = _init_l_Lean_JsonRpc_instFromJsonMessageKind___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind___closed__0);
l_Lean_JsonRpc_instFromJsonMessageKind = _init_l_Lean_JsonRpc_instFromJsonMessageKind();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessageKind);
l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0 = _init_l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0);
l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1 = _init_l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1);
l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2 = _init_l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2);
l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3 = _init_l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3);
l_Lean_JsonRpc_instToJsonMessageKind___closed__0 = _init_l_Lean_JsonRpc_instToJsonMessageKind___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessageKind___closed__0);
l_Lean_JsonRpc_instToJsonMessageKind = _init_l_Lean_JsonRpc_instToJsonMessageKind();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessageKind);
l_IO_FS_Stream_readMessage___closed__0 = _init_l_IO_FS_Stream_readMessage___closed__0();
lean_mark_persistent(l_IO_FS_Stream_readMessage___closed__0);
l_IO_FS_Stream_readMessage___closed__1 = _init_l_IO_FS_Stream_readMessage___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readMessage___closed__1);
l_IO_FS_Stream_readRequestAs___redArg___closed__0 = _init_l_IO_FS_Stream_readRequestAs___redArg___closed__0();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___redArg___closed__0);
l_IO_FS_Stream_readRequestAs___redArg___closed__1 = _init_l_IO_FS_Stream_readRequestAs___redArg___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___redArg___closed__1);
l_IO_FS_Stream_readRequestAs___redArg___closed__2 = _init_l_IO_FS_Stream_readRequestAs___redArg___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___redArg___closed__2);
l_IO_FS_Stream_readRequestAs___redArg___closed__3 = _init_l_IO_FS_Stream_readRequestAs___redArg___closed__3();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___redArg___closed__3);
l_IO_FS_Stream_readRequestAs___redArg___closed__4 = _init_l_IO_FS_Stream_readRequestAs___redArg___closed__4();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___redArg___closed__4);
l_IO_FS_Stream_readRequestAs___redArg___closed__5 = _init_l_IO_FS_Stream_readRequestAs___redArg___closed__5();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___redArg___closed__5);
l_IO_FS_Stream_readRequestAs___redArg___closed__6 = _init_l_IO_FS_Stream_readRequestAs___redArg___closed__6();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___redArg___closed__6);
l_IO_FS_Stream_readNotificationAs___redArg___closed__0 = _init_l_IO_FS_Stream_readNotificationAs___redArg___closed__0();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___redArg___closed__0);
l_IO_FS_Stream_readResponseAs___redArg___closed__0 = _init_l_IO_FS_Stream_readResponseAs___redArg___closed__0();
lean_mark_persistent(l_IO_FS_Stream_readResponseAs___redArg___closed__0);
l_IO_FS_Stream_readResponseAs___redArg___closed__1 = _init_l_IO_FS_Stream_readResponseAs___redArg___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readResponseAs___redArg___closed__1);
l_IO_FS_Stream_readResponseAs___redArg___closed__2 = _init_l_IO_FS_Stream_readResponseAs___redArg___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readResponseAs___redArg___closed__2);
l_IO_FS_Stream_readResponseAs___redArg___closed__3 = _init_l_IO_FS_Stream_readResponseAs___redArg___closed__3();
lean_mark_persistent(l_IO_FS_Stream_readResponseAs___redArg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
