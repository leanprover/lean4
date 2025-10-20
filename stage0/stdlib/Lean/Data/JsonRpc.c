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
LEAN_EXPORT uint8_t l_Lean_JsonRpc_RequestID_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22;
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default___redArg(lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage;
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode;
uint8_t l_Lean_instDecidableEqJsonNumber_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_lt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12;
static lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequestID_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedErrorCode;
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__2;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedErrorCode_default;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ctorIdx(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID;
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedMessage_default;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim___redArg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_str_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14;
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4;
static lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__1;
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instLTRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ctorIdx___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12;
static lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__3;
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqErrorCode_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequestID_default;
lean_object* l_IO_FS_Stream_readJson(lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_JsonRpc_instBEqRequestID___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18;
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ltProp;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx(uint8_t);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedMessage;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default___redArg(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19;
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instBEqErrorCode___closed__0;
static lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1;
static lean_object* l_IO_FS_Stream_readNotificationAs___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedMessageMetaData_default;
static lean_object* l_Lean_JsonRpc_instInhabitedMessage_default___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ctorIdx(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(lean_object*);
static lean_object* l_Lean_JsonRpc_instOrdRequestID___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ofMessage_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(lean_object*);
lean_object* l_Option_toJson___redArg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__2;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
static lean_object* l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__5;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_strCore(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ctorIdx___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__3;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_num(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___redArg(lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_IO_FS_Stream_writeJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2;
uint8_t l_Lean_JsonNumber_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg___boxed(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedMessageMetaData;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instOrdRequestID_ord(lean_object* x_1, lean_object* x_2) {
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
else
{
uint8_t x_10; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_10 = 0;
return x_10;
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_11; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = 2;
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
x_14 = l_Lean_JsonNumber_lt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_JsonNumber_lt(x_13, x_12);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = 2;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_18 = 0;
return x_18;
}
}
default: 
{
uint8_t x_19; 
lean_dec_ref(x_1);
x_19 = 0;
return x_19;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = 2;
return x_21;
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
static lean_object* _init_l_Lean_JsonRpc_instToStringRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToStringRequestID___lam__0), 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l_Lean_JsonRpc_ErrorCode_ctorIdx(x_1);
x_4 = l_Lean_JsonRpc_ErrorCode_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_ErrorCode_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_JsonRpc_ErrorCode_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lean_JsonRpc_ErrorCode_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed), 1, 0);
return x_1;
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
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed), 1, 0);
return x_1;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_Request_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
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
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_JsonRpc_instBEqRequest_beq___redArg(x_2, x_3, x_4);
return x_5;
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
x_3 = l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object* x_1) {
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
x_4 = l_Option_toJson___at___Lean_JsonRpc_Request_ofMessage_x3f_spec__0(x_3);
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
x_9 = l_Option_toJson___at___Lean_JsonRpc_Request_ofMessage_x3f_spec__0(x_8);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_Notification_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
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
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_JsonRpc_instBEqNotification_beq___redArg(x_2, x_3, x_4);
return x_5;
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
x_3 = l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(x_2);
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
x_4 = l_Option_toJson___at___Lean_JsonRpc_Request_ofMessage_x3f_spec__0(x_3);
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
x_8 = l_Option_toJson___at___Lean_JsonRpc_Request_ofMessage_x3f_spec__0(x_7);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_Response_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
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
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_JsonRpc_instBEqResponse_beq___redArg(x_2, x_3, x_4);
return x_5;
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
x_3 = l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(x_2);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_ResponseError_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
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
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(x_2, x_3, x_4);
return x_5;
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
x_3 = l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(x_2);
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
static lean_object* _init_l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0), 1, 0);
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
static lean_object* _init_l_Lean_JsonRpc_instCoeStringRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeStringRequestID___lam__0), 1, 0);
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
static lean_object* _init_l_Lean_JsonRpc_instCoeJsonNumberRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0), 1, 0);
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
case 0:
{
uint8_t x_7; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = 1;
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = l_Lean_JsonNumber_lt(x_8, x_9);
return x_10;
}
default: 
{
uint8_t x_11; 
lean_dec_ref(x_1);
x_11 = 0;
return x_11;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = 1;
return x_13;
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
case 2:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_ctor_set_tag(x_1, 1);
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
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
case 3:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_ctor_set_tag(x_1, 0);
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
x_10 = lean_alloc_ctor(0, 1, 0);
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0), 1, 0);
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
static lean_object* _init_l_Lean_JsonRpc_instToJsonRequestID() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonRequestID___lam__0), 1, 0);
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
lean_ctor_set(x_86, 0, x_73);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_71);
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
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
x_74 = x_95;
goto block_89;
}
case 1:
{
lean_object* x_96; 
x_96 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
x_74 = x_96;
goto block_89;
}
case 2:
{
lean_object* x_97; 
x_97 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
x_74 = x_97;
goto block_89;
}
case 3:
{
lean_object* x_98; 
x_98 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
x_74 = x_98;
goto block_89;
}
case 4:
{
lean_object* x_99; 
x_99 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
x_74 = x_99;
goto block_89;
}
case 5:
{
lean_object* x_100; 
x_100 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
x_74 = x_100;
goto block_89;
}
case 6:
{
lean_object* x_101; 
x_101 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
x_74 = x_101;
goto block_89;
}
case 7:
{
lean_object* x_102; 
x_102 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
x_74 = x_102;
goto block_89;
}
case 8:
{
lean_object* x_103; 
x_103 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
x_74 = x_103;
goto block_89;
}
case 9:
{
lean_object* x_104; 
x_104 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
x_74 = x_104;
goto block_89;
}
case 10:
{
lean_object* x_105; 
x_105 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
x_74 = x_105;
goto block_89;
}
default: 
{
lean_object* x_106; 
x_106 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
x_71 = x_92;
x_72 = x_94;
x_73 = x_93;
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
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_2 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonMessage___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
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
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_20; lean_object* x_21; 
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
x_9 = x_56;
x_10 = x_52;
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
x_9 = x_58;
x_10 = x_52;
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
x_9 = x_61;
x_10 = x_52;
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
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_9);
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
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_getStr_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Structured_fromJson_x3f), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_JsonRpc_instFromJsonMessage___closed__0;
x_2 = l_Lean_JsonRpc_instFromJsonMessage___closed__1;
x_3 = l_Lean_JsonRpc_instFromJsonMessage___closed__2;
x_4 = l_Lean_JsonRpc_instFromJsonMessage___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0), 5, 4);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, x_3);
return x_5;
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
x_31 = l_Lean_JsonRpc_instFromJsonMessage___closed__0;
x_32 = l_Lean_JsonRpc_instFromJsonMessage___closed__1;
x_33 = l_Lean_JsonRpc_instFromJsonMessage___closed__2;
x_34 = l_Lean_JsonRpc_instFromJsonMessage___closed__3;
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
lean_object* x_2; lean_object* x_3; lean_object* x_19; uint8_t x_20; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_19 = lean_string_utf8_byte_size(x_2);
x_20 = lean_nat_dec_lt(x_3, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
uint32_t x_23; uint32_t x_24; uint8_t x_25; 
x_23 = lean_string_utf8_get_fast(x_2, x_3);
x_24 = 34;
x_25 = lean_uint32_dec_eq(x_23, x_24);
if (x_25 == 0)
{
if (x_20 == 0)
{
goto block_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
goto block_18;
}
}
block_18:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_inc(x_3);
lean_inc_ref(x_2);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_11);
x_12 = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
x_13 = l_Lean_Json_Parser_strCore(x_12, x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_14 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0;
x_17 = l_Lean_Json_Parser_strCore(x_16, x_15);
return x_17;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 2:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_ctor_set_tag(x_3, 1);
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
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 3:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_ctor_set_tag(x_3, 0);
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
x_12 = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_inc(x_4);
lean_inc_ref(x_3);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
x_12 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_12);
x_13 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_string_utf8_byte_size(x_17);
x_20 = lean_nat_dec_lt(x_18, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec_ref(x_1);
x_21 = lean_box(0);
if (lean_is_scalar(x_16)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_16;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_inc(x_18);
lean_inc_ref(x_17);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_43; uint8_t x_44; 
x_24 = lean_ctor_get(x_14, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_14, 0);
lean_dec(x_25);
x_26 = lean_string_utf8_next_fast(x_17, x_18);
lean_dec(x_18);
lean_ctor_set(x_14, 1, x_26);
x_43 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
x_44 = lean_string_dec_eq(x_15, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
x_46 = lean_string_dec_eq(x_15, x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_48 = lean_string_dec_eq(x_15, x_47);
lean_dec(x_15);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_16);
lean_dec_ref(x_1);
x_49 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_14);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
lean_object* x_51; 
x_51 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_16);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_ctor_set_tag(x_51, 1);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_14);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_14);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec_ref(x_51);
lean_inc(x_57);
x_58 = l_Lean_Json_getObjVal_x3f(x_57, x_45);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_dec(x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_27 = x_59;
goto block_30;
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec_ref(x_58);
if (lean_obj_tag(x_60) == 3)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_61);
lean_dec_ref(x_60);
x_62 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
x_63 = lean_string_dec_eq(x_61, x_62);
lean_dec_ref(x_61);
if (x_63 == 0)
{
lean_dec(x_57);
goto block_32;
}
else
{
lean_object* x_64; 
lean_inc(x_57);
x_64 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(x_57, x_43);
if (lean_obj_tag(x_64) == 0)
{
goto block_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_57);
x_94 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_57, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_dec_ref(x_94);
goto block_92;
}
else
{
lean_dec_ref(x_94);
lean_dec_ref(x_64);
lean_dec(x_57);
lean_dec(x_16);
goto block_42;
}
}
block_87:
{
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec(x_57);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_27 = x_65;
goto block_30;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = l_Lean_Json_getObjVal_x3f(x_57, x_47);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
lean_dec(x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_27 = x_68;
goto block_30;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
lean_inc(x_69);
x_71 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(x_69, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_66);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_27 = x_72;
goto block_30;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
lean_inc(x_69);
x_75 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_69, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_dec(x_73);
lean_dec(x_69);
lean_dec(x_66);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_27 = x_76;
goto block_30;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_16);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_79 = l_Lean_Json_getObjVal_x3f(x_69, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
lean_dec_ref(x_79);
x_80 = lean_box(0);
x_81 = lean_unbox(x_73);
lean_dec(x_73);
x_33 = x_66;
x_34 = x_81;
x_35 = x_77;
x_36 = x_80;
goto block_39;
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = lean_unbox(x_73);
lean_dec(x_73);
x_33 = x_66;
x_34 = x_83;
x_35 = x_77;
x_36 = x_79;
goto block_39;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
lean_dec(x_79);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_unbox(x_73);
lean_dec(x_73);
x_33 = x_66;
x_34 = x_86;
x_35 = x_77;
x_36 = x_85;
goto block_39;
}
}
}
}
}
}
}
block_92:
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_57);
x_89 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_57, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
if (lean_obj_tag(x_64) == 0)
{
goto block_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
lean_inc(x_57);
x_91 = l_Lean_Json_getObjVal_x3f(x_57, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_dec_ref(x_91);
goto block_87;
}
else
{
lean_dec_ref(x_91);
lean_dec_ref(x_64);
lean_dec(x_57);
lean_dec(x_16);
goto block_42;
}
}
}
else
{
lean_dec_ref(x_89);
lean_dec_ref(x_64);
lean_dec(x_57);
lean_dec(x_16);
goto block_42;
}
}
}
}
else
{
lean_dec(x_60);
lean_dec(x_57);
goto block_32;
}
}
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_1);
x_95 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_14);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_101 = lean_string_utf8_byte_size(x_99);
x_102 = lean_nat_dec_lt(x_100, x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_box(0);
lean_ctor_set_tag(x_95, 1);
lean_ctor_set(x_95, 1, x_103);
return x_95;
}
else
{
uint8_t x_104; 
lean_inc(x_100);
lean_inc_ref(x_99);
lean_free_object(x_95);
x_104 = !lean_is_exclusive(x_97);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_97, 1);
lean_dec(x_105);
x_106 = lean_ctor_get(x_97, 0);
lean_dec(x_106);
x_107 = lean_string_utf8_next_fast(x_99, x_100);
lean_dec(x_100);
lean_ctor_set(x_97, 1, x_107);
x_108 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_97);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
lean_dec(x_111);
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_ctor_get(x_110, 1);
x_114 = lean_string_utf8_byte_size(x_112);
x_115 = lean_nat_dec_lt(x_113, x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_box(0);
lean_ctor_set_tag(x_108, 1);
lean_ctor_set(x_108, 1, x_116);
return x_108;
}
else
{
uint8_t x_117; 
lean_inc(x_113);
lean_inc_ref(x_112);
lean_free_object(x_108);
x_117 = !lean_is_exclusive(x_110);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_110, 1);
lean_dec(x_118);
x_119 = lean_ctor_get(x_110, 0);
lean_dec(x_119);
x_120 = lean_string_utf8_next_fast(x_112, x_113);
lean_dec(x_113);
lean_ctor_set(x_110, 1, x_120);
x_121 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_110);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_121, 1);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_121, 1, x_124);
return x_121;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_121, 0);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_121);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_121);
if (x_129 == 0)
{
return x_121;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_121, 0);
x_131 = lean_ctor_get(x_121, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_121);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_110);
x_133 = lean_string_utf8_next_fast(x_112, x_113);
lean_dec(x_113);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_112);
lean_ctor_set(x_134, 1, x_133);
x_135 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_137);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_135, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_143 = x_135;
} else {
 lean_dec_ref(x_135);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_108, 0);
lean_inc(x_145);
lean_dec(x_108);
x_146 = lean_ctor_get(x_145, 0);
x_147 = lean_ctor_get(x_145, 1);
x_148 = lean_string_utf8_byte_size(x_146);
x_149 = lean_nat_dec_lt(x_147, x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_inc(x_147);
lean_inc_ref(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_152 = x_145;
} else {
 lean_dec_ref(x_145);
 x_152 = lean_box(0);
}
x_153 = lean_string_utf8_next_fast(x_146, x_147);
lean_dec(x_147);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_146);
lean_ctor_set(x_154, 1, x_153);
x_155 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_157);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_155, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_155, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_163 = x_155;
} else {
 lean_dec_ref(x_155);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_108);
if (x_165 == 0)
{
return x_108;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_108, 0);
x_167 = lean_ctor_get(x_108, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_108);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_97);
x_169 = lean_string_utf8_next_fast(x_99, x_100);
lean_dec(x_100);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_99);
lean_ctor_set(x_170, 1, x_169);
x_171 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_172, 0);
x_175 = lean_ctor_get(x_172, 1);
x_176 = lean_string_utf8_byte_size(x_174);
x_177 = lean_nat_dec_lt(x_175, x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_box(0);
if (lean_is_scalar(x_173)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_173;
 lean_ctor_set_tag(x_179, 1);
}
lean_ctor_set(x_179, 0, x_172);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_inc(x_175);
lean_inc_ref(x_174);
lean_dec(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_180 = x_172;
} else {
 lean_dec_ref(x_172);
 x_180 = lean_box(0);
}
x_181 = lean_string_utf8_next_fast(x_174, x_175);
lean_dec(x_175);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_174);
lean_ctor_set(x_182, 1, x_181);
x_183 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_185);
if (lean_is_scalar(x_186)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_186;
}
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_183, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_183, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_191 = x_183;
} else {
 lean_dec_ref(x_183);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_171, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_171, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_195 = x_171;
} else {
 lean_dec_ref(x_171);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_197 = lean_ctor_get(x_95, 0);
lean_inc(x_197);
lean_dec(x_95);
x_198 = lean_ctor_get(x_197, 0);
x_199 = lean_ctor_get(x_197, 1);
x_200 = lean_string_utf8_byte_size(x_198);
x_201 = lean_nat_dec_lt(x_199, x_200);
lean_dec(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_box(0);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_197);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_inc(x_199);
lean_inc_ref(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_204 = x_197;
} else {
 lean_dec_ref(x_197);
 x_204 = lean_box(0);
}
x_205 = lean_string_utf8_next_fast(x_198, x_199);
lean_dec(x_199);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_204;
}
lean_ctor_set(x_206, 0, x_198);
lean_ctor_set(x_206, 1, x_205);
x_207 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_208, 0);
x_211 = lean_ctor_get(x_208, 1);
x_212 = lean_string_utf8_byte_size(x_210);
x_213 = lean_nat_dec_lt(x_211, x_212);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_box(0);
if (lean_is_scalar(x_209)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_209;
 lean_ctor_set_tag(x_215, 1);
}
lean_ctor_set(x_215, 0, x_208);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_inc(x_211);
lean_inc_ref(x_210);
lean_dec(x_209);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_216 = x_208;
} else {
 lean_dec_ref(x_208);
 x_216 = lean_box(0);
}
x_217 = lean_string_utf8_next_fast(x_210, x_211);
lean_dec(x_211);
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_216;
}
lean_ctor_set(x_218, 0, x_210);
lean_ctor_set(x_218, 1, x_217);
x_219 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_221);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_220);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_219, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_219, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_227 = x_219;
} else {
 lean_dec_ref(x_219);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_207, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_207, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_231 = x_207;
} else {
 lean_dec_ref(x_207);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
}
}
else
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_95);
if (x_233 == 0)
{
return x_95;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_95, 0);
x_235 = lean_ctor_get(x_95, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_95);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
}
else
{
lean_object* x_237; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_1);
x_237 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(x_14);
if (lean_obj_tag(x_237) == 0)
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = lean_ctor_get(x_237, 1);
x_241 = lean_ctor_get(x_239, 0);
x_242 = lean_ctor_get(x_239, 1);
x_243 = lean_string_utf8_byte_size(x_241);
x_244 = lean_nat_dec_lt(x_242, x_243);
lean_dec(x_243);
if (x_244 == 0)
{
lean_object* x_245; 
lean_dec(x_240);
x_245 = lean_box(0);
lean_ctor_set_tag(x_237, 1);
lean_ctor_set(x_237, 1, x_245);
return x_237;
}
else
{
uint8_t x_246; 
lean_inc(x_242);
lean_inc_ref(x_241);
lean_free_object(x_237);
x_246 = !lean_is_exclusive(x_239);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_247 = lean_ctor_get(x_239, 1);
lean_dec(x_247);
x_248 = lean_ctor_get(x_239, 0);
lean_dec(x_248);
x_249 = lean_string_utf8_next_fast(x_241, x_242);
lean_dec(x_242);
lean_ctor_set(x_239, 1, x_249);
x_250 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_239);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_252 = lean_ctor_get(x_250, 0);
x_253 = lean_ctor_get(x_250, 1);
lean_dec(x_253);
x_254 = lean_ctor_get(x_252, 0);
x_255 = lean_ctor_get(x_252, 1);
x_256 = lean_string_utf8_byte_size(x_254);
x_257 = lean_nat_dec_lt(x_255, x_256);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; 
lean_dec(x_240);
x_258 = lean_box(0);
lean_ctor_set_tag(x_250, 1);
lean_ctor_set(x_250, 1, x_258);
return x_250;
}
else
{
uint8_t x_259; 
lean_inc(x_255);
lean_inc_ref(x_254);
lean_free_object(x_250);
x_259 = !lean_is_exclusive(x_252);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = lean_ctor_get(x_252, 1);
lean_dec(x_260);
x_261 = lean_ctor_get(x_252, 0);
lean_dec(x_261);
x_262 = lean_string_utf8_next_fast(x_254, x_255);
lean_dec(x_255);
lean_ctor_set(x_252, 1, x_262);
x_263 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_252);
if (lean_obj_tag(x_263) == 0)
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_265 = lean_ctor_get(x_263, 0);
x_266 = lean_ctor_get(x_263, 1);
lean_dec(x_266);
x_267 = lean_ctor_get(x_265, 0);
x_268 = lean_ctor_get(x_265, 1);
x_269 = lean_string_utf8_byte_size(x_267);
x_270 = lean_nat_dec_lt(x_268, x_269);
lean_dec(x_269);
if (x_270 == 0)
{
lean_object* x_271; 
lean_dec(x_240);
x_271 = lean_box(0);
lean_ctor_set_tag(x_263, 1);
lean_ctor_set(x_263, 1, x_271);
return x_263;
}
else
{
uint8_t x_272; 
lean_inc(x_268);
lean_inc_ref(x_267);
lean_free_object(x_263);
x_272 = !lean_is_exclusive(x_265);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_265, 1);
lean_dec(x_273);
x_274 = lean_ctor_get(x_265, 0);
lean_dec(x_274);
x_275 = lean_string_utf8_next_fast(x_267, x_268);
lean_dec(x_268);
lean_ctor_set(x_265, 1, x_275);
x_276 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_265);
if (lean_obj_tag(x_276) == 0)
{
uint8_t x_277; 
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = lean_ctor_get(x_276, 1);
x_280 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_281 = lean_string_dec_eq(x_279, x_280);
if (x_281 == 0)
{
lean_object* x_282; uint8_t x_283; 
x_282 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_283 = lean_string_dec_eq(x_279, x_282);
lean_dec(x_279);
if (x_283 == 0)
{
lean_object* x_284; 
lean_dec(x_240);
x_284 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
lean_ctor_set_tag(x_276, 1);
lean_ctor_set(x_276, 1, x_284);
return x_276;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_285, 0, x_240);
lean_ctor_set(x_276, 1, x_285);
return x_276;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
lean_dec(x_279);
x_286 = lean_ctor_get(x_278, 0);
x_287 = lean_ctor_get(x_278, 1);
x_288 = lean_string_utf8_byte_size(x_286);
x_289 = lean_nat_dec_lt(x_287, x_288);
lean_dec(x_288);
if (x_289 == 0)
{
lean_object* x_290; 
lean_dec(x_240);
x_290 = lean_box(0);
lean_ctor_set_tag(x_276, 1);
lean_ctor_set(x_276, 1, x_290);
return x_276;
}
else
{
uint8_t x_291; 
lean_inc(x_287);
lean_inc_ref(x_286);
lean_free_object(x_276);
x_291 = !lean_is_exclusive(x_278);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_278, 1);
lean_dec(x_292);
x_293 = lean_ctor_get(x_278, 0);
lean_dec(x_293);
x_294 = lean_string_utf8_next_fast(x_286, x_287);
lean_dec(x_287);
lean_ctor_set(x_278, 1, x_294);
x_295 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_278);
if (lean_obj_tag(x_295) == 0)
{
uint8_t x_296; 
x_296 = !lean_is_exclusive(x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_295, 1);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_240);
lean_ctor_set(x_298, 1, x_297);
lean_ctor_set(x_295, 1, x_298);
return x_295;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_299 = lean_ctor_get(x_295, 0);
x_300 = lean_ctor_get(x_295, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_295);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_240);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
else
{
uint8_t x_303; 
lean_dec(x_240);
x_303 = !lean_is_exclusive(x_295);
if (x_303 == 0)
{
return x_295;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_295, 0);
x_305 = lean_ctor_get(x_295, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_295);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_278);
x_307 = lean_string_utf8_next_fast(x_286, x_287);
lean_dec(x_287);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_286);
lean_ctor_set(x_308, 1, x_307);
x_309 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_308);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_312 = x_309;
} else {
 lean_dec_ref(x_309);
 x_312 = lean_box(0);
}
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_240);
lean_ctor_set(x_313, 1, x_311);
if (lean_is_scalar(x_312)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_312;
}
lean_ctor_set(x_314, 0, x_310);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_240);
x_315 = lean_ctor_get(x_309, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_309, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_317 = x_309;
} else {
 lean_dec_ref(x_309);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
}
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_319 = lean_ctor_get(x_276, 0);
x_320 = lean_ctor_get(x_276, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_276);
x_321 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_322 = lean_string_dec_eq(x_320, x_321);
if (x_322 == 0)
{
lean_object* x_323; uint8_t x_324; 
x_323 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_324 = lean_string_dec_eq(x_320, x_323);
lean_dec(x_320);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; 
lean_dec(x_240);
x_325 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_319);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_327, 0, x_240);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_319);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
lean_dec(x_320);
x_329 = lean_ctor_get(x_319, 0);
x_330 = lean_ctor_get(x_319, 1);
x_331 = lean_string_utf8_byte_size(x_329);
x_332 = lean_nat_dec_lt(x_330, x_331);
lean_dec(x_331);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_240);
x_333 = lean_box(0);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_319);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_inc(x_330);
lean_inc_ref(x_329);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_335 = x_319;
} else {
 lean_dec_ref(x_319);
 x_335 = lean_box(0);
}
x_336 = lean_string_utf8_next_fast(x_329, x_330);
lean_dec(x_330);
if (lean_is_scalar(x_335)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_335;
}
lean_ctor_set(x_337, 0, x_329);
lean_ctor_set(x_337, 1, x_336);
x_338 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_337);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_341 = x_338;
} else {
 lean_dec_ref(x_338);
 x_341 = lean_box(0);
}
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_240);
lean_ctor_set(x_342, 1, x_340);
if (lean_is_scalar(x_341)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_341;
}
lean_ctor_set(x_343, 0, x_339);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_240);
x_344 = lean_ctor_get(x_338, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_338, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_346 = x_338;
} else {
 lean_dec_ref(x_338);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 2, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_344);
lean_ctor_set(x_347, 1, x_345);
return x_347;
}
}
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_240);
x_348 = !lean_is_exclusive(x_276);
if (x_348 == 0)
{
return x_276;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_276, 0);
x_350 = lean_ctor_get(x_276, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_276);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_265);
x_352 = lean_string_utf8_next_fast(x_267, x_268);
lean_dec(x_268);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_267);
lean_ctor_set(x_353, 1, x_352);
x_354 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_353);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_357 = x_354;
} else {
 lean_dec_ref(x_354);
 x_357 = lean_box(0);
}
x_358 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_359 = lean_string_dec_eq(x_356, x_358);
if (x_359 == 0)
{
lean_object* x_360; uint8_t x_361; 
x_360 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_361 = lean_string_dec_eq(x_356, x_360);
lean_dec(x_356);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_240);
x_362 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_357)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_357;
 lean_ctor_set_tag(x_363, 1);
}
lean_ctor_set(x_363, 0, x_355);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_364, 0, x_240);
if (lean_is_scalar(x_357)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_357;
}
lean_ctor_set(x_365, 0, x_355);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
lean_dec(x_356);
x_366 = lean_ctor_get(x_355, 0);
x_367 = lean_ctor_get(x_355, 1);
x_368 = lean_string_utf8_byte_size(x_366);
x_369 = lean_nat_dec_lt(x_367, x_368);
lean_dec(x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; 
lean_dec(x_240);
x_370 = lean_box(0);
if (lean_is_scalar(x_357)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_357;
 lean_ctor_set_tag(x_371, 1);
}
lean_ctor_set(x_371, 0, x_355);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_inc(x_367);
lean_inc_ref(x_366);
lean_dec(x_357);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_372 = x_355;
} else {
 lean_dec_ref(x_355);
 x_372 = lean_box(0);
}
x_373 = lean_string_utf8_next_fast(x_366, x_367);
lean_dec(x_367);
if (lean_is_scalar(x_372)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_372;
}
lean_ctor_set(x_374, 0, x_366);
lean_ctor_set(x_374, 1, x_373);
x_375 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_374);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_378 = x_375;
} else {
 lean_dec_ref(x_375);
 x_378 = lean_box(0);
}
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_240);
lean_ctor_set(x_379, 1, x_377);
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_376);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_240);
x_381 = lean_ctor_get(x_375, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_375, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_383 = x_375;
} else {
 lean_dec_ref(x_375);
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
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_240);
x_385 = lean_ctor_get(x_354, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_354, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_387 = x_354;
} else {
 lean_dec_ref(x_354);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_389 = lean_ctor_get(x_263, 0);
lean_inc(x_389);
lean_dec(x_263);
x_390 = lean_ctor_get(x_389, 0);
x_391 = lean_ctor_get(x_389, 1);
x_392 = lean_string_utf8_byte_size(x_390);
x_393 = lean_nat_dec_lt(x_391, x_392);
lean_dec(x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; 
lean_dec(x_240);
x_394 = lean_box(0);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_389);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_inc(x_391);
lean_inc_ref(x_390);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_396 = x_389;
} else {
 lean_dec_ref(x_389);
 x_396 = lean_box(0);
}
x_397 = lean_string_utf8_next_fast(x_390, x_391);
lean_dec(x_391);
if (lean_is_scalar(x_396)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_396;
}
lean_ctor_set(x_398, 0, x_390);
lean_ctor_set(x_398, 1, x_397);
x_399 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_398);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_402 = x_399;
} else {
 lean_dec_ref(x_399);
 x_402 = lean_box(0);
}
x_403 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_404 = lean_string_dec_eq(x_401, x_403);
if (x_404 == 0)
{
lean_object* x_405; uint8_t x_406; 
x_405 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_406 = lean_string_dec_eq(x_401, x_405);
lean_dec(x_401);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; 
lean_dec(x_240);
x_407 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_402)) {
 x_408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_408 = x_402;
 lean_ctor_set_tag(x_408, 1);
}
lean_ctor_set(x_408, 0, x_400);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_409, 0, x_240);
if (lean_is_scalar(x_402)) {
 x_410 = lean_alloc_ctor(0, 2, 0);
} else {
 x_410 = x_402;
}
lean_ctor_set(x_410, 0, x_400);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; 
lean_dec(x_401);
x_411 = lean_ctor_get(x_400, 0);
x_412 = lean_ctor_get(x_400, 1);
x_413 = lean_string_utf8_byte_size(x_411);
x_414 = lean_nat_dec_lt(x_412, x_413);
lean_dec(x_413);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; 
lean_dec(x_240);
x_415 = lean_box(0);
if (lean_is_scalar(x_402)) {
 x_416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_416 = x_402;
 lean_ctor_set_tag(x_416, 1);
}
lean_ctor_set(x_416, 0, x_400);
lean_ctor_set(x_416, 1, x_415);
return x_416;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_inc(x_412);
lean_inc_ref(x_411);
lean_dec(x_402);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_417 = x_400;
} else {
 lean_dec_ref(x_400);
 x_417 = lean_box(0);
}
x_418 = lean_string_utf8_next_fast(x_411, x_412);
lean_dec(x_412);
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_411);
lean_ctor_set(x_419, 1, x_418);
x_420 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_419);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_423 = x_420;
} else {
 lean_dec_ref(x_420);
 x_423 = lean_box(0);
}
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_240);
lean_ctor_set(x_424, 1, x_422);
if (lean_is_scalar(x_423)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_423;
}
lean_ctor_set(x_425, 0, x_421);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_240);
x_426 = lean_ctor_get(x_420, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_420, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_428 = x_420;
} else {
 lean_dec_ref(x_420);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_426);
lean_ctor_set(x_429, 1, x_427);
return x_429;
}
}
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_240);
x_430 = lean_ctor_get(x_399, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_399, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_432 = x_399;
} else {
 lean_dec_ref(x_399);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_430);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
}
}
}
else
{
uint8_t x_434; 
lean_dec(x_240);
x_434 = !lean_is_exclusive(x_263);
if (x_434 == 0)
{
return x_263;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_263, 0);
x_436 = lean_ctor_get(x_263, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_263);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_252);
x_438 = lean_string_utf8_next_fast(x_254, x_255);
lean_dec(x_255);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_254);
lean_ctor_set(x_439, 1, x_438);
x_440 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_439);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_442 = x_440;
} else {
 lean_dec_ref(x_440);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_441, 0);
x_444 = lean_ctor_get(x_441, 1);
x_445 = lean_string_utf8_byte_size(x_443);
x_446 = lean_nat_dec_lt(x_444, x_445);
lean_dec(x_445);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_240);
x_447 = lean_box(0);
if (lean_is_scalar(x_442)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_442;
 lean_ctor_set_tag(x_448, 1);
}
lean_ctor_set(x_448, 0, x_441);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_inc(x_444);
lean_inc_ref(x_443);
lean_dec(x_442);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_449 = x_441;
} else {
 lean_dec_ref(x_441);
 x_449 = lean_box(0);
}
x_450 = lean_string_utf8_next_fast(x_443, x_444);
lean_dec(x_444);
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_443);
lean_ctor_set(x_451, 1, x_450);
x_452 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_451);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_455 = x_452;
} else {
 lean_dec_ref(x_452);
 x_455 = lean_box(0);
}
x_456 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_457 = lean_string_dec_eq(x_454, x_456);
if (x_457 == 0)
{
lean_object* x_458; uint8_t x_459; 
x_458 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_459 = lean_string_dec_eq(x_454, x_458);
lean_dec(x_454);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; 
lean_dec(x_240);
x_460 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_455)) {
 x_461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_461 = x_455;
 lean_ctor_set_tag(x_461, 1);
}
lean_ctor_set(x_461, 0, x_453);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
else
{
lean_object* x_462; lean_object* x_463; 
x_462 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_462, 0, x_240);
if (lean_is_scalar(x_455)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_455;
}
lean_ctor_set(x_463, 0, x_453);
lean_ctor_set(x_463, 1, x_462);
return x_463;
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; 
lean_dec(x_454);
x_464 = lean_ctor_get(x_453, 0);
x_465 = lean_ctor_get(x_453, 1);
x_466 = lean_string_utf8_byte_size(x_464);
x_467 = lean_nat_dec_lt(x_465, x_466);
lean_dec(x_466);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; 
lean_dec(x_240);
x_468 = lean_box(0);
if (lean_is_scalar(x_455)) {
 x_469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_469 = x_455;
 lean_ctor_set_tag(x_469, 1);
}
lean_ctor_set(x_469, 0, x_453);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_inc(x_465);
lean_inc_ref(x_464);
lean_dec(x_455);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_470 = x_453;
} else {
 lean_dec_ref(x_453);
 x_470 = lean_box(0);
}
x_471 = lean_string_utf8_next_fast(x_464, x_465);
lean_dec(x_465);
if (lean_is_scalar(x_470)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_470;
}
lean_ctor_set(x_472, 0, x_464);
lean_ctor_set(x_472, 1, x_471);
x_473 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_472);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_476 = x_473;
} else {
 lean_dec_ref(x_473);
 x_476 = lean_box(0);
}
x_477 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_477, 0, x_240);
lean_ctor_set(x_477, 1, x_475);
if (lean_is_scalar(x_476)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_476;
}
lean_ctor_set(x_478, 0, x_474);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_240);
x_479 = lean_ctor_get(x_473, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_473, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_481 = x_473;
} else {
 lean_dec_ref(x_473);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_480);
return x_482;
}
}
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_240);
x_483 = lean_ctor_get(x_452, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_452, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_485 = x_452;
} else {
 lean_dec_ref(x_452);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 2, 0);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_484);
return x_486;
}
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_240);
x_487 = lean_ctor_get(x_440, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_440, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_489 = x_440;
} else {
 lean_dec_ref(x_440);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
}
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; 
x_491 = lean_ctor_get(x_250, 0);
lean_inc(x_491);
lean_dec(x_250);
x_492 = lean_ctor_get(x_491, 0);
x_493 = lean_ctor_get(x_491, 1);
x_494 = lean_string_utf8_byte_size(x_492);
x_495 = lean_nat_dec_lt(x_493, x_494);
lean_dec(x_494);
if (x_495 == 0)
{
lean_object* x_496; lean_object* x_497; 
lean_dec(x_240);
x_496 = lean_box(0);
x_497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_497, 0, x_491);
lean_ctor_set(x_497, 1, x_496);
return x_497;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_inc(x_493);
lean_inc_ref(x_492);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_498 = x_491;
} else {
 lean_dec_ref(x_491);
 x_498 = lean_box(0);
}
x_499 = lean_string_utf8_next_fast(x_492, x_493);
lean_dec(x_493);
if (lean_is_scalar(x_498)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_498;
}
lean_ctor_set(x_500, 0, x_492);
lean_ctor_set(x_500, 1, x_499);
x_501 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_500);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_503 = x_501;
} else {
 lean_dec_ref(x_501);
 x_503 = lean_box(0);
}
x_504 = lean_ctor_get(x_502, 0);
x_505 = lean_ctor_get(x_502, 1);
x_506 = lean_string_utf8_byte_size(x_504);
x_507 = lean_nat_dec_lt(x_505, x_506);
lean_dec(x_506);
if (x_507 == 0)
{
lean_object* x_508; lean_object* x_509; 
lean_dec(x_240);
x_508 = lean_box(0);
if (lean_is_scalar(x_503)) {
 x_509 = lean_alloc_ctor(1, 2, 0);
} else {
 x_509 = x_503;
 lean_ctor_set_tag(x_509, 1);
}
lean_ctor_set(x_509, 0, x_502);
lean_ctor_set(x_509, 1, x_508);
return x_509;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_inc(x_505);
lean_inc_ref(x_504);
lean_dec(x_503);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_510 = x_502;
} else {
 lean_dec_ref(x_502);
 x_510 = lean_box(0);
}
x_511 = lean_string_utf8_next_fast(x_504, x_505);
lean_dec(x_505);
if (lean_is_scalar(x_510)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_510;
}
lean_ctor_set(x_512, 0, x_504);
lean_ctor_set(x_512, 1, x_511);
x_513 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_512);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_516 = x_513;
} else {
 lean_dec_ref(x_513);
 x_516 = lean_box(0);
}
x_517 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_518 = lean_string_dec_eq(x_515, x_517);
if (x_518 == 0)
{
lean_object* x_519; uint8_t x_520; 
x_519 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_520 = lean_string_dec_eq(x_515, x_519);
lean_dec(x_515);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; 
lean_dec(x_240);
x_521 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_516)) {
 x_522 = lean_alloc_ctor(1, 2, 0);
} else {
 x_522 = x_516;
 lean_ctor_set_tag(x_522, 1);
}
lean_ctor_set(x_522, 0, x_514);
lean_ctor_set(x_522, 1, x_521);
return x_522;
}
else
{
lean_object* x_523; lean_object* x_524; 
x_523 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_523, 0, x_240);
if (lean_is_scalar(x_516)) {
 x_524 = lean_alloc_ctor(0, 2, 0);
} else {
 x_524 = x_516;
}
lean_ctor_set(x_524, 0, x_514);
lean_ctor_set(x_524, 1, x_523);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; uint8_t x_528; 
lean_dec(x_515);
x_525 = lean_ctor_get(x_514, 0);
x_526 = lean_ctor_get(x_514, 1);
x_527 = lean_string_utf8_byte_size(x_525);
x_528 = lean_nat_dec_lt(x_526, x_527);
lean_dec(x_527);
if (x_528 == 0)
{
lean_object* x_529; lean_object* x_530; 
lean_dec(x_240);
x_529 = lean_box(0);
if (lean_is_scalar(x_516)) {
 x_530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_530 = x_516;
 lean_ctor_set_tag(x_530, 1);
}
lean_ctor_set(x_530, 0, x_514);
lean_ctor_set(x_530, 1, x_529);
return x_530;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_inc(x_526);
lean_inc_ref(x_525);
lean_dec(x_516);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 x_531 = x_514;
} else {
 lean_dec_ref(x_514);
 x_531 = lean_box(0);
}
x_532 = lean_string_utf8_next_fast(x_525, x_526);
lean_dec(x_526);
if (lean_is_scalar(x_531)) {
 x_533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_533 = x_531;
}
lean_ctor_set(x_533, 0, x_525);
lean_ctor_set(x_533, 1, x_532);
x_534 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_533);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_537 = x_534;
} else {
 lean_dec_ref(x_534);
 x_537 = lean_box(0);
}
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_240);
lean_ctor_set(x_538, 1, x_536);
if (lean_is_scalar(x_537)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_537;
}
lean_ctor_set(x_539, 0, x_535);
lean_ctor_set(x_539, 1, x_538);
return x_539;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_240);
x_540 = lean_ctor_get(x_534, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_534, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_542 = x_534;
} else {
 lean_dec_ref(x_534);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_540);
lean_ctor_set(x_543, 1, x_541);
return x_543;
}
}
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_240);
x_544 = lean_ctor_get(x_513, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_513, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_546 = x_513;
} else {
 lean_dec_ref(x_513);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_240);
x_548 = lean_ctor_get(x_501, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_501, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_550 = x_501;
} else {
 lean_dec_ref(x_501);
 x_550 = lean_box(0);
}
if (lean_is_scalar(x_550)) {
 x_551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_551 = x_550;
}
lean_ctor_set(x_551, 0, x_548);
lean_ctor_set(x_551, 1, x_549);
return x_551;
}
}
}
}
else
{
uint8_t x_552; 
lean_dec(x_240);
x_552 = !lean_is_exclusive(x_250);
if (x_552 == 0)
{
return x_250;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_250, 0);
x_554 = lean_ctor_get(x_250, 1);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_250);
x_555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
return x_555;
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_239);
x_556 = lean_string_utf8_next_fast(x_241, x_242);
lean_dec(x_242);
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_241);
lean_ctor_set(x_557, 1, x_556);
x_558 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_557);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; uint8_t x_564; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_560 = x_558;
} else {
 lean_dec_ref(x_558);
 x_560 = lean_box(0);
}
x_561 = lean_ctor_get(x_559, 0);
x_562 = lean_ctor_get(x_559, 1);
x_563 = lean_string_utf8_byte_size(x_561);
x_564 = lean_nat_dec_lt(x_562, x_563);
lean_dec(x_563);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; 
lean_dec(x_240);
x_565 = lean_box(0);
if (lean_is_scalar(x_560)) {
 x_566 = lean_alloc_ctor(1, 2, 0);
} else {
 x_566 = x_560;
 lean_ctor_set_tag(x_566, 1);
}
lean_ctor_set(x_566, 0, x_559);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_inc(x_562);
lean_inc_ref(x_561);
lean_dec(x_560);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_567 = x_559;
} else {
 lean_dec_ref(x_559);
 x_567 = lean_box(0);
}
x_568 = lean_string_utf8_next_fast(x_561, x_562);
lean_dec(x_562);
if (lean_is_scalar(x_567)) {
 x_569 = lean_alloc_ctor(0, 2, 0);
} else {
 x_569 = x_567;
}
lean_ctor_set(x_569, 0, x_561);
lean_ctor_set(x_569, 1, x_568);
x_570 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_569);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_572 = x_570;
} else {
 lean_dec_ref(x_570);
 x_572 = lean_box(0);
}
x_573 = lean_ctor_get(x_571, 0);
x_574 = lean_ctor_get(x_571, 1);
x_575 = lean_string_utf8_byte_size(x_573);
x_576 = lean_nat_dec_lt(x_574, x_575);
lean_dec(x_575);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; 
lean_dec(x_240);
x_577 = lean_box(0);
if (lean_is_scalar(x_572)) {
 x_578 = lean_alloc_ctor(1, 2, 0);
} else {
 x_578 = x_572;
 lean_ctor_set_tag(x_578, 1);
}
lean_ctor_set(x_578, 0, x_571);
lean_ctor_set(x_578, 1, x_577);
return x_578;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_inc(x_574);
lean_inc_ref(x_573);
lean_dec(x_572);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_579 = x_571;
} else {
 lean_dec_ref(x_571);
 x_579 = lean_box(0);
}
x_580 = lean_string_utf8_next_fast(x_573, x_574);
lean_dec(x_574);
if (lean_is_scalar(x_579)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_579;
}
lean_ctor_set(x_581, 0, x_573);
lean_ctor_set(x_581, 1, x_580);
x_582 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_581);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_585 = x_582;
} else {
 lean_dec_ref(x_582);
 x_585 = lean_box(0);
}
x_586 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_587 = lean_string_dec_eq(x_584, x_586);
if (x_587 == 0)
{
lean_object* x_588; uint8_t x_589; 
x_588 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_589 = lean_string_dec_eq(x_584, x_588);
lean_dec(x_584);
if (x_589 == 0)
{
lean_object* x_590; lean_object* x_591; 
lean_dec(x_240);
x_590 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_585)) {
 x_591 = lean_alloc_ctor(1, 2, 0);
} else {
 x_591 = x_585;
 lean_ctor_set_tag(x_591, 1);
}
lean_ctor_set(x_591, 0, x_583);
lean_ctor_set(x_591, 1, x_590);
return x_591;
}
else
{
lean_object* x_592; lean_object* x_593; 
x_592 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_592, 0, x_240);
if (lean_is_scalar(x_585)) {
 x_593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_593 = x_585;
}
lean_ctor_set(x_593, 0, x_583);
lean_ctor_set(x_593, 1, x_592);
return x_593;
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; 
lean_dec(x_584);
x_594 = lean_ctor_get(x_583, 0);
x_595 = lean_ctor_get(x_583, 1);
x_596 = lean_string_utf8_byte_size(x_594);
x_597 = lean_nat_dec_lt(x_595, x_596);
lean_dec(x_596);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; 
lean_dec(x_240);
x_598 = lean_box(0);
if (lean_is_scalar(x_585)) {
 x_599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_599 = x_585;
 lean_ctor_set_tag(x_599, 1);
}
lean_ctor_set(x_599, 0, x_583);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_inc(x_595);
lean_inc_ref(x_594);
lean_dec(x_585);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_600 = x_583;
} else {
 lean_dec_ref(x_583);
 x_600 = lean_box(0);
}
x_601 = lean_string_utf8_next_fast(x_594, x_595);
lean_dec(x_595);
if (lean_is_scalar(x_600)) {
 x_602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_602 = x_600;
}
lean_ctor_set(x_602, 0, x_594);
lean_ctor_set(x_602, 1, x_601);
x_603 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_602);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 lean_ctor_release(x_603, 1);
 x_606 = x_603;
} else {
 lean_dec_ref(x_603);
 x_606 = lean_box(0);
}
x_607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_607, 0, x_240);
lean_ctor_set(x_607, 1, x_605);
if (lean_is_scalar(x_606)) {
 x_608 = lean_alloc_ctor(0, 2, 0);
} else {
 x_608 = x_606;
}
lean_ctor_set(x_608, 0, x_604);
lean_ctor_set(x_608, 1, x_607);
return x_608;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_240);
x_609 = lean_ctor_get(x_603, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_603, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 lean_ctor_release(x_603, 1);
 x_611 = x_603;
} else {
 lean_dec_ref(x_603);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(1, 2, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_609);
lean_ctor_set(x_612, 1, x_610);
return x_612;
}
}
}
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_240);
x_613 = lean_ctor_get(x_582, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_582, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_615 = x_582;
} else {
 lean_dec_ref(x_582);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(1, 2, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_613);
lean_ctor_set(x_616, 1, x_614);
return x_616;
}
}
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_240);
x_617 = lean_ctor_get(x_570, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_570, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_619 = x_570;
} else {
 lean_dec_ref(x_570);
 x_619 = lean_box(0);
}
if (lean_is_scalar(x_619)) {
 x_620 = lean_alloc_ctor(1, 2, 0);
} else {
 x_620 = x_619;
}
lean_ctor_set(x_620, 0, x_617);
lean_ctor_set(x_620, 1, x_618);
return x_620;
}
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_240);
x_621 = lean_ctor_get(x_558, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_558, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_623 = x_558;
} else {
 lean_dec_ref(x_558);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_621);
lean_ctor_set(x_624, 1, x_622);
return x_624;
}
}
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; 
x_625 = lean_ctor_get(x_237, 0);
x_626 = lean_ctor_get(x_237, 1);
lean_inc(x_626);
lean_inc(x_625);
lean_dec(x_237);
x_627 = lean_ctor_get(x_625, 0);
x_628 = lean_ctor_get(x_625, 1);
x_629 = lean_string_utf8_byte_size(x_627);
x_630 = lean_nat_dec_lt(x_628, x_629);
lean_dec(x_629);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; 
lean_dec(x_626);
x_631 = lean_box(0);
x_632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_632, 0, x_625);
lean_ctor_set(x_632, 1, x_631);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_inc(x_628);
lean_inc_ref(x_627);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_633 = x_625;
} else {
 lean_dec_ref(x_625);
 x_633 = lean_box(0);
}
x_634 = lean_string_utf8_next_fast(x_627, x_628);
lean_dec(x_628);
if (lean_is_scalar(x_633)) {
 x_635 = lean_alloc_ctor(0, 2, 0);
} else {
 x_635 = x_633;
}
lean_ctor_set(x_635, 0, x_627);
lean_ctor_set(x_635, 1, x_634);
x_636 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_635);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; uint8_t x_642; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_638 = x_636;
} else {
 lean_dec_ref(x_636);
 x_638 = lean_box(0);
}
x_639 = lean_ctor_get(x_637, 0);
x_640 = lean_ctor_get(x_637, 1);
x_641 = lean_string_utf8_byte_size(x_639);
x_642 = lean_nat_dec_lt(x_640, x_641);
lean_dec(x_641);
if (x_642 == 0)
{
lean_object* x_643; lean_object* x_644; 
lean_dec(x_626);
x_643 = lean_box(0);
if (lean_is_scalar(x_638)) {
 x_644 = lean_alloc_ctor(1, 2, 0);
} else {
 x_644 = x_638;
 lean_ctor_set_tag(x_644, 1);
}
lean_ctor_set(x_644, 0, x_637);
lean_ctor_set(x_644, 1, x_643);
return x_644;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_inc(x_640);
lean_inc_ref(x_639);
lean_dec(x_638);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_645 = x_637;
} else {
 lean_dec_ref(x_637);
 x_645 = lean_box(0);
}
x_646 = lean_string_utf8_next_fast(x_639, x_640);
lean_dec(x_640);
if (lean_is_scalar(x_645)) {
 x_647 = lean_alloc_ctor(0, 2, 0);
} else {
 x_647 = x_645;
}
lean_ctor_set(x_647, 0, x_639);
lean_ctor_set(x_647, 1, x_646);
x_648 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_647);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; uint8_t x_654; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_650 = x_648;
} else {
 lean_dec_ref(x_648);
 x_650 = lean_box(0);
}
x_651 = lean_ctor_get(x_649, 0);
x_652 = lean_ctor_get(x_649, 1);
x_653 = lean_string_utf8_byte_size(x_651);
x_654 = lean_nat_dec_lt(x_652, x_653);
lean_dec(x_653);
if (x_654 == 0)
{
lean_object* x_655; lean_object* x_656; 
lean_dec(x_626);
x_655 = lean_box(0);
if (lean_is_scalar(x_650)) {
 x_656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_656 = x_650;
 lean_ctor_set_tag(x_656, 1);
}
lean_ctor_set(x_656, 0, x_649);
lean_ctor_set(x_656, 1, x_655);
return x_656;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_inc(x_652);
lean_inc_ref(x_651);
lean_dec(x_650);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 x_657 = x_649;
} else {
 lean_dec_ref(x_649);
 x_657 = lean_box(0);
}
x_658 = lean_string_utf8_next_fast(x_651, x_652);
lean_dec(x_652);
if (lean_is_scalar(x_657)) {
 x_659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_659 = x_657;
}
lean_ctor_set(x_659, 0, x_651);
lean_ctor_set(x_659, 1, x_658);
x_660 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_659);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_663 = x_660;
} else {
 lean_dec_ref(x_660);
 x_663 = lean_box(0);
}
x_664 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_665 = lean_string_dec_eq(x_662, x_664);
if (x_665 == 0)
{
lean_object* x_666; uint8_t x_667; 
x_666 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_667 = lean_string_dec_eq(x_662, x_666);
lean_dec(x_662);
if (x_667 == 0)
{
lean_object* x_668; lean_object* x_669; 
lean_dec(x_626);
x_668 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_663)) {
 x_669 = lean_alloc_ctor(1, 2, 0);
} else {
 x_669 = x_663;
 lean_ctor_set_tag(x_669, 1);
}
lean_ctor_set(x_669, 0, x_661);
lean_ctor_set(x_669, 1, x_668);
return x_669;
}
else
{
lean_object* x_670; lean_object* x_671; 
x_670 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_670, 0, x_626);
if (lean_is_scalar(x_663)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_663;
}
lean_ctor_set(x_671, 0, x_661);
lean_ctor_set(x_671, 1, x_670);
return x_671;
}
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; uint8_t x_675; 
lean_dec(x_662);
x_672 = lean_ctor_get(x_661, 0);
x_673 = lean_ctor_get(x_661, 1);
x_674 = lean_string_utf8_byte_size(x_672);
x_675 = lean_nat_dec_lt(x_673, x_674);
lean_dec(x_674);
if (x_675 == 0)
{
lean_object* x_676; lean_object* x_677; 
lean_dec(x_626);
x_676 = lean_box(0);
if (lean_is_scalar(x_663)) {
 x_677 = lean_alloc_ctor(1, 2, 0);
} else {
 x_677 = x_663;
 lean_ctor_set_tag(x_677, 1);
}
lean_ctor_set(x_677, 0, x_661);
lean_ctor_set(x_677, 1, x_676);
return x_677;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
lean_inc(x_673);
lean_inc_ref(x_672);
lean_dec(x_663);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 x_678 = x_661;
} else {
 lean_dec_ref(x_661);
 x_678 = lean_box(0);
}
x_679 = lean_string_utf8_next_fast(x_672, x_673);
lean_dec(x_673);
if (lean_is_scalar(x_678)) {
 x_680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_680 = x_678;
}
lean_ctor_set(x_680, 0, x_672);
lean_ctor_set(x_680, 1, x_679);
x_681 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_680);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_684 = x_681;
} else {
 lean_dec_ref(x_681);
 x_684 = lean_box(0);
}
x_685 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_685, 0, x_626);
lean_ctor_set(x_685, 1, x_683);
if (lean_is_scalar(x_684)) {
 x_686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_686 = x_684;
}
lean_ctor_set(x_686, 0, x_682);
lean_ctor_set(x_686, 1, x_685);
return x_686;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_626);
x_687 = lean_ctor_get(x_681, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_681, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_689 = x_681;
} else {
 lean_dec_ref(x_681);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(1, 2, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_687);
lean_ctor_set(x_690, 1, x_688);
return x_690;
}
}
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_626);
x_691 = lean_ctor_get(x_660, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_660, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_693 = x_660;
} else {
 lean_dec_ref(x_660);
 x_693 = lean_box(0);
}
if (lean_is_scalar(x_693)) {
 x_694 = lean_alloc_ctor(1, 2, 0);
} else {
 x_694 = x_693;
}
lean_ctor_set(x_694, 0, x_691);
lean_ctor_set(x_694, 1, x_692);
return x_694;
}
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_626);
x_695 = lean_ctor_get(x_648, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_648, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_697 = x_648;
} else {
 lean_dec_ref(x_648);
 x_697 = lean_box(0);
}
if (lean_is_scalar(x_697)) {
 x_698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_698 = x_697;
}
lean_ctor_set(x_698, 0, x_695);
lean_ctor_set(x_698, 1, x_696);
return x_698;
}
}
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
lean_dec(x_626);
x_699 = lean_ctor_get(x_636, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_636, 1);
lean_inc(x_700);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_701 = x_636;
} else {
 lean_dec_ref(x_636);
 x_701 = lean_box(0);
}
if (lean_is_scalar(x_701)) {
 x_702 = lean_alloc_ctor(1, 2, 0);
} else {
 x_702 = x_701;
}
lean_ctor_set(x_702, 0, x_699);
lean_ctor_set(x_702, 1, x_700);
return x_702;
}
}
}
}
else
{
uint8_t x_703; 
x_703 = !lean_is_exclusive(x_237);
if (x_703 == 0)
{
return x_237;
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_704 = lean_ctor_get(x_237, 0);
x_705 = lean_ctor_get(x_237, 1);
lean_inc(x_705);
lean_inc(x_704);
lean_dec(x_237);
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_705);
return x_706;
}
}
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_16)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_16;
 lean_ctor_set_tag(x_29, 1);
}
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
block_32:
{
lean_object* x_31; 
x_31 = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
x_27 = x_31;
goto block_30;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_14);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
x_40 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_715; uint8_t x_716; lean_object* x_717; lean_object* x_718; lean_object* x_725; uint8_t x_726; 
lean_dec(x_14);
x_707 = lean_string_utf8_next_fast(x_17, x_18);
lean_dec(x_18);
x_708 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_708, 0, x_17);
lean_ctor_set(x_708, 1, x_707);
x_725 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
x_726 = lean_string_dec_eq(x_15, x_725);
if (x_726 == 0)
{
lean_object* x_727; uint8_t x_728; 
x_727 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
x_728 = lean_string_dec_eq(x_15, x_727);
if (x_728 == 0)
{
lean_object* x_729; uint8_t x_730; 
x_729 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_730 = lean_string_dec_eq(x_15, x_729);
lean_dec(x_15);
if (x_730 == 0)
{
lean_object* x_731; lean_object* x_732; 
lean_dec(x_16);
lean_dec_ref(x_1);
x_731 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3;
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_708);
lean_ctor_set(x_732, 1, x_731);
return x_732;
}
else
{
lean_object* x_733; 
x_733 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_dec(x_16);
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
if (lean_is_exclusive(x_733)) {
 lean_ctor_release(x_733, 0);
 x_735 = x_733;
} else {
 lean_dec_ref(x_733);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(1, 1, 0);
} else {
 x_736 = x_735;
 lean_ctor_set_tag(x_736, 1);
}
lean_ctor_set(x_736, 0, x_734);
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_708);
lean_ctor_set(x_737, 1, x_736);
return x_737;
}
else
{
lean_object* x_738; lean_object* x_739; 
x_738 = lean_ctor_get(x_733, 0);
lean_inc(x_738);
lean_dec_ref(x_733);
lean_inc(x_738);
x_739 = l_Lean_Json_getObjVal_x3f(x_738, x_727);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; 
lean_dec(x_738);
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
lean_dec_ref(x_739);
x_709 = x_740;
goto block_712;
}
else
{
lean_object* x_741; 
x_741 = lean_ctor_get(x_739, 0);
lean_inc(x_741);
lean_dec_ref(x_739);
if (lean_obj_tag(x_741) == 3)
{
lean_object* x_742; lean_object* x_743; uint8_t x_744; 
x_742 = lean_ctor_get(x_741, 0);
lean_inc_ref(x_742);
lean_dec_ref(x_741);
x_743 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
x_744 = lean_string_dec_eq(x_742, x_743);
lean_dec_ref(x_742);
if (x_744 == 0)
{
lean_dec(x_738);
goto block_714;
}
else
{
lean_object* x_745; 
lean_inc(x_738);
x_745 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(x_738, x_725);
if (lean_obj_tag(x_745) == 0)
{
goto block_772;
}
else
{
lean_object* x_773; lean_object* x_774; 
x_773 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_738);
x_774 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_738, x_773);
if (lean_obj_tag(x_774) == 0)
{
lean_dec_ref(x_774);
goto block_772;
}
else
{
lean_dec_ref(x_774);
lean_dec_ref(x_745);
lean_dec(x_738);
lean_dec(x_16);
goto block_724;
}
}
block_767:
{
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_746; 
lean_dec(x_738);
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
lean_dec_ref(x_745);
x_709 = x_746;
goto block_712;
}
else
{
lean_object* x_747; lean_object* x_748; 
x_747 = lean_ctor_get(x_745, 0);
lean_inc(x_747);
lean_dec_ref(x_745);
x_748 = l_Lean_Json_getObjVal_x3f(x_738, x_729);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; 
lean_dec(x_747);
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
lean_dec_ref(x_748);
x_709 = x_749;
goto block_712;
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_750 = lean_ctor_get(x_748, 0);
lean_inc(x_750);
lean_dec_ref(x_748);
x_751 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
lean_inc(x_750);
x_752 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(x_750, x_751);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; 
lean_dec(x_750);
lean_dec(x_747);
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
lean_dec_ref(x_752);
x_709 = x_753;
goto block_712;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_752, 0);
lean_inc(x_754);
lean_dec_ref(x_752);
x_755 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
lean_inc(x_750);
x_756 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_750, x_755);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; 
lean_dec(x_754);
lean_dec(x_750);
lean_dec(x_747);
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
lean_dec_ref(x_756);
x_709 = x_757;
goto block_712;
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_16);
x_758 = lean_ctor_get(x_756, 0);
lean_inc(x_758);
lean_dec_ref(x_756);
x_759 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_760 = l_Lean_Json_getObjVal_x3f(x_750, x_759);
if (lean_obj_tag(x_760) == 0)
{
lean_object* x_761; uint8_t x_762; 
lean_dec_ref(x_760);
x_761 = lean_box(0);
x_762 = lean_unbox(x_754);
lean_dec(x_754);
x_715 = x_747;
x_716 = x_762;
x_717 = x_758;
x_718 = x_761;
goto block_721;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; 
x_763 = lean_ctor_get(x_760, 0);
lean_inc(x_763);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 x_764 = x_760;
} else {
 lean_dec_ref(x_760);
 x_764 = lean_box(0);
}
if (lean_is_scalar(x_764)) {
 x_765 = lean_alloc_ctor(1, 1, 0);
} else {
 x_765 = x_764;
}
lean_ctor_set(x_765, 0, x_763);
x_766 = lean_unbox(x_754);
lean_dec(x_754);
x_715 = x_747;
x_716 = x_766;
x_717 = x_758;
x_718 = x_765;
goto block_721;
}
}
}
}
}
}
block_772:
{
lean_object* x_768; lean_object* x_769; 
x_768 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_738);
x_769 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_738, x_768);
if (lean_obj_tag(x_769) == 0)
{
lean_dec_ref(x_769);
if (lean_obj_tag(x_745) == 0)
{
goto block_767;
}
else
{
lean_object* x_770; lean_object* x_771; 
x_770 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
lean_inc(x_738);
x_771 = l_Lean_Json_getObjVal_x3f(x_738, x_770);
if (lean_obj_tag(x_771) == 0)
{
lean_dec_ref(x_771);
goto block_767;
}
else
{
lean_dec_ref(x_771);
lean_dec_ref(x_745);
lean_dec(x_738);
lean_dec(x_16);
goto block_724;
}
}
}
else
{
lean_dec_ref(x_769);
lean_dec_ref(x_745);
lean_dec(x_738);
lean_dec(x_16);
goto block_724;
}
}
}
}
else
{
lean_dec(x_741);
lean_dec(x_738);
goto block_714;
}
}
}
}
}
else
{
lean_object* x_775; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_1);
x_775 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_708);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; uint8_t x_781; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_777 = x_775;
} else {
 lean_dec_ref(x_775);
 x_777 = lean_box(0);
}
x_778 = lean_ctor_get(x_776, 0);
x_779 = lean_ctor_get(x_776, 1);
x_780 = lean_string_utf8_byte_size(x_778);
x_781 = lean_nat_dec_lt(x_779, x_780);
lean_dec(x_780);
if (x_781 == 0)
{
lean_object* x_782; lean_object* x_783; 
x_782 = lean_box(0);
if (lean_is_scalar(x_777)) {
 x_783 = lean_alloc_ctor(1, 2, 0);
} else {
 x_783 = x_777;
 lean_ctor_set_tag(x_783, 1);
}
lean_ctor_set(x_783, 0, x_776);
lean_ctor_set(x_783, 1, x_782);
return x_783;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_inc(x_779);
lean_inc_ref(x_778);
lean_dec(x_777);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_784 = x_776;
} else {
 lean_dec_ref(x_776);
 x_784 = lean_box(0);
}
x_785 = lean_string_utf8_next_fast(x_778, x_779);
lean_dec(x_779);
if (lean_is_scalar(x_784)) {
 x_786 = lean_alloc_ctor(0, 2, 0);
} else {
 x_786 = x_784;
}
lean_ctor_set(x_786, 0, x_778);
lean_ctor_set(x_786, 1, x_785);
x_787 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_786);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; uint8_t x_793; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_789 = x_787;
} else {
 lean_dec_ref(x_787);
 x_789 = lean_box(0);
}
x_790 = lean_ctor_get(x_788, 0);
x_791 = lean_ctor_get(x_788, 1);
x_792 = lean_string_utf8_byte_size(x_790);
x_793 = lean_nat_dec_lt(x_791, x_792);
lean_dec(x_792);
if (x_793 == 0)
{
lean_object* x_794; lean_object* x_795; 
x_794 = lean_box(0);
if (lean_is_scalar(x_789)) {
 x_795 = lean_alloc_ctor(1, 2, 0);
} else {
 x_795 = x_789;
 lean_ctor_set_tag(x_795, 1);
}
lean_ctor_set(x_795, 0, x_788);
lean_ctor_set(x_795, 1, x_794);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; 
lean_inc(x_791);
lean_inc_ref(x_790);
lean_dec(x_789);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 lean_ctor_release(x_788, 1);
 x_796 = x_788;
} else {
 lean_dec_ref(x_788);
 x_796 = lean_box(0);
}
x_797 = lean_string_utf8_next_fast(x_790, x_791);
lean_dec(x_791);
if (lean_is_scalar(x_796)) {
 x_798 = lean_alloc_ctor(0, 2, 0);
} else {
 x_798 = x_796;
}
lean_ctor_set(x_798, 0, x_790);
lean_ctor_set(x_798, 1, x_797);
x_799 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_798);
if (lean_obj_tag(x_799) == 0)
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_802 = x_799;
} else {
 lean_dec_ref(x_799);
 x_802 = lean_box(0);
}
x_803 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_803, 0, x_801);
if (lean_is_scalar(x_802)) {
 x_804 = lean_alloc_ctor(0, 2, 0);
} else {
 x_804 = x_802;
}
lean_ctor_set(x_804, 0, x_800);
lean_ctor_set(x_804, 1, x_803);
return x_804;
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_805 = lean_ctor_get(x_799, 0);
lean_inc(x_805);
x_806 = lean_ctor_get(x_799, 1);
lean_inc(x_806);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_807 = x_799;
} else {
 lean_dec_ref(x_799);
 x_807 = lean_box(0);
}
if (lean_is_scalar(x_807)) {
 x_808 = lean_alloc_ctor(1, 2, 0);
} else {
 x_808 = x_807;
}
lean_ctor_set(x_808, 0, x_805);
lean_ctor_set(x_808, 1, x_806);
return x_808;
}
}
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_809 = lean_ctor_get(x_787, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_787, 1);
lean_inc(x_810);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_811 = x_787;
} else {
 lean_dec_ref(x_787);
 x_811 = lean_box(0);
}
if (lean_is_scalar(x_811)) {
 x_812 = lean_alloc_ctor(1, 2, 0);
} else {
 x_812 = x_811;
}
lean_ctor_set(x_812, 0, x_809);
lean_ctor_set(x_812, 1, x_810);
return x_812;
}
}
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_813 = lean_ctor_get(x_775, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_775, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_815 = x_775;
} else {
 lean_dec_ref(x_775);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_815)) {
 x_816 = lean_alloc_ctor(1, 2, 0);
} else {
 x_816 = x_815;
}
lean_ctor_set(x_816, 0, x_813);
lean_ctor_set(x_816, 1, x_814);
return x_816;
}
}
}
else
{
lean_object* x_817; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_1);
x_817 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(x_708);
if (lean_obj_tag(x_817) == 0)
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; uint8_t x_824; 
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_820 = x_817;
} else {
 lean_dec_ref(x_817);
 x_820 = lean_box(0);
}
x_821 = lean_ctor_get(x_818, 0);
x_822 = lean_ctor_get(x_818, 1);
x_823 = lean_string_utf8_byte_size(x_821);
x_824 = lean_nat_dec_lt(x_822, x_823);
lean_dec(x_823);
if (x_824 == 0)
{
lean_object* x_825; lean_object* x_826; 
lean_dec(x_819);
x_825 = lean_box(0);
if (lean_is_scalar(x_820)) {
 x_826 = lean_alloc_ctor(1, 2, 0);
} else {
 x_826 = x_820;
 lean_ctor_set_tag(x_826, 1);
}
lean_ctor_set(x_826, 0, x_818);
lean_ctor_set(x_826, 1, x_825);
return x_826;
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
lean_inc(x_822);
lean_inc_ref(x_821);
lean_dec(x_820);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 x_827 = x_818;
} else {
 lean_dec_ref(x_818);
 x_827 = lean_box(0);
}
x_828 = lean_string_utf8_next_fast(x_821, x_822);
lean_dec(x_822);
if (lean_is_scalar(x_827)) {
 x_829 = lean_alloc_ctor(0, 2, 0);
} else {
 x_829 = x_827;
}
lean_ctor_set(x_829, 0, x_821);
lean_ctor_set(x_829, 1, x_828);
x_830 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_829);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; uint8_t x_836; 
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 lean_ctor_release(x_830, 1);
 x_832 = x_830;
} else {
 lean_dec_ref(x_830);
 x_832 = lean_box(0);
}
x_833 = lean_ctor_get(x_831, 0);
x_834 = lean_ctor_get(x_831, 1);
x_835 = lean_string_utf8_byte_size(x_833);
x_836 = lean_nat_dec_lt(x_834, x_835);
lean_dec(x_835);
if (x_836 == 0)
{
lean_object* x_837; lean_object* x_838; 
lean_dec(x_819);
x_837 = lean_box(0);
if (lean_is_scalar(x_832)) {
 x_838 = lean_alloc_ctor(1, 2, 0);
} else {
 x_838 = x_832;
 lean_ctor_set_tag(x_838, 1);
}
lean_ctor_set(x_838, 0, x_831);
lean_ctor_set(x_838, 1, x_837);
return x_838;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_inc(x_834);
lean_inc_ref(x_833);
lean_dec(x_832);
if (lean_is_exclusive(x_831)) {
 lean_ctor_release(x_831, 0);
 lean_ctor_release(x_831, 1);
 x_839 = x_831;
} else {
 lean_dec_ref(x_831);
 x_839 = lean_box(0);
}
x_840 = lean_string_utf8_next_fast(x_833, x_834);
lean_dec(x_834);
if (lean_is_scalar(x_839)) {
 x_841 = lean_alloc_ctor(0, 2, 0);
} else {
 x_841 = x_839;
}
lean_ctor_set(x_841, 0, x_833);
lean_ctor_set(x_841, 1, x_840);
x_842 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_841);
if (lean_obj_tag(x_842) == 0)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; uint8_t x_848; 
x_843 = lean_ctor_get(x_842, 0);
lean_inc(x_843);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 lean_ctor_release(x_842, 1);
 x_844 = x_842;
} else {
 lean_dec_ref(x_842);
 x_844 = lean_box(0);
}
x_845 = lean_ctor_get(x_843, 0);
x_846 = lean_ctor_get(x_843, 1);
x_847 = lean_string_utf8_byte_size(x_845);
x_848 = lean_nat_dec_lt(x_846, x_847);
lean_dec(x_847);
if (x_848 == 0)
{
lean_object* x_849; lean_object* x_850; 
lean_dec(x_819);
x_849 = lean_box(0);
if (lean_is_scalar(x_844)) {
 x_850 = lean_alloc_ctor(1, 2, 0);
} else {
 x_850 = x_844;
 lean_ctor_set_tag(x_850, 1);
}
lean_ctor_set(x_850, 0, x_843);
lean_ctor_set(x_850, 1, x_849);
return x_850;
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
lean_inc(x_846);
lean_inc_ref(x_845);
lean_dec(x_844);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 x_851 = x_843;
} else {
 lean_dec_ref(x_843);
 x_851 = lean_box(0);
}
x_852 = lean_string_utf8_next_fast(x_845, x_846);
lean_dec(x_846);
if (lean_is_scalar(x_851)) {
 x_853 = lean_alloc_ctor(0, 2, 0);
} else {
 x_853 = x_851;
}
lean_ctor_set(x_853, 0, x_845);
lean_ctor_set(x_853, 1, x_852);
x_854 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_853);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; uint8_t x_859; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_857 = x_854;
} else {
 lean_dec_ref(x_854);
 x_857 = lean_box(0);
}
x_858 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_859 = lean_string_dec_eq(x_856, x_858);
if (x_859 == 0)
{
lean_object* x_860; uint8_t x_861; 
x_860 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_861 = lean_string_dec_eq(x_856, x_860);
lean_dec(x_856);
if (x_861 == 0)
{
lean_object* x_862; lean_object* x_863; 
lean_dec(x_819);
x_862 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_857)) {
 x_863 = lean_alloc_ctor(1, 2, 0);
} else {
 x_863 = x_857;
 lean_ctor_set_tag(x_863, 1);
}
lean_ctor_set(x_863, 0, x_855);
lean_ctor_set(x_863, 1, x_862);
return x_863;
}
else
{
lean_object* x_864; lean_object* x_865; 
x_864 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_864, 0, x_819);
if (lean_is_scalar(x_857)) {
 x_865 = lean_alloc_ctor(0, 2, 0);
} else {
 x_865 = x_857;
}
lean_ctor_set(x_865, 0, x_855);
lean_ctor_set(x_865, 1, x_864);
return x_865;
}
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; uint8_t x_869; 
lean_dec(x_856);
x_866 = lean_ctor_get(x_855, 0);
x_867 = lean_ctor_get(x_855, 1);
x_868 = lean_string_utf8_byte_size(x_866);
x_869 = lean_nat_dec_lt(x_867, x_868);
lean_dec(x_868);
if (x_869 == 0)
{
lean_object* x_870; lean_object* x_871; 
lean_dec(x_819);
x_870 = lean_box(0);
if (lean_is_scalar(x_857)) {
 x_871 = lean_alloc_ctor(1, 2, 0);
} else {
 x_871 = x_857;
 lean_ctor_set_tag(x_871, 1);
}
lean_ctor_set(x_871, 0, x_855);
lean_ctor_set(x_871, 1, x_870);
return x_871;
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_inc(x_867);
lean_inc_ref(x_866);
lean_dec(x_857);
if (lean_is_exclusive(x_855)) {
 lean_ctor_release(x_855, 0);
 lean_ctor_release(x_855, 1);
 x_872 = x_855;
} else {
 lean_dec_ref(x_855);
 x_872 = lean_box(0);
}
x_873 = lean_string_utf8_next_fast(x_866, x_867);
lean_dec(x_867);
if (lean_is_scalar(x_872)) {
 x_874 = lean_alloc_ctor(0, 2, 0);
} else {
 x_874 = x_872;
}
lean_ctor_set(x_874, 0, x_866);
lean_ctor_set(x_874, 1, x_873);
x_875 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_874);
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_878 = x_875;
} else {
 lean_dec_ref(x_875);
 x_878 = lean_box(0);
}
x_879 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_879, 0, x_819);
lean_ctor_set(x_879, 1, x_877);
if (lean_is_scalar(x_878)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_878;
}
lean_ctor_set(x_880, 0, x_876);
lean_ctor_set(x_880, 1, x_879);
return x_880;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
lean_dec(x_819);
x_881 = lean_ctor_get(x_875, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_875, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_883 = x_875;
} else {
 lean_dec_ref(x_875);
 x_883 = lean_box(0);
}
if (lean_is_scalar(x_883)) {
 x_884 = lean_alloc_ctor(1, 2, 0);
} else {
 x_884 = x_883;
}
lean_ctor_set(x_884, 0, x_881);
lean_ctor_set(x_884, 1, x_882);
return x_884;
}
}
}
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
lean_dec(x_819);
x_885 = lean_ctor_get(x_854, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_854, 1);
lean_inc(x_886);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_887 = x_854;
} else {
 lean_dec_ref(x_854);
 x_887 = lean_box(0);
}
if (lean_is_scalar(x_887)) {
 x_888 = lean_alloc_ctor(1, 2, 0);
} else {
 x_888 = x_887;
}
lean_ctor_set(x_888, 0, x_885);
lean_ctor_set(x_888, 1, x_886);
return x_888;
}
}
}
else
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
lean_dec(x_819);
x_889 = lean_ctor_get(x_842, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_842, 1);
lean_inc(x_890);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 lean_ctor_release(x_842, 1);
 x_891 = x_842;
} else {
 lean_dec_ref(x_842);
 x_891 = lean_box(0);
}
if (lean_is_scalar(x_891)) {
 x_892 = lean_alloc_ctor(1, 2, 0);
} else {
 x_892 = x_891;
}
lean_ctor_set(x_892, 0, x_889);
lean_ctor_set(x_892, 1, x_890);
return x_892;
}
}
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
lean_dec(x_819);
x_893 = lean_ctor_get(x_830, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_830, 1);
lean_inc(x_894);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 lean_ctor_release(x_830, 1);
 x_895 = x_830;
} else {
 lean_dec_ref(x_830);
 x_895 = lean_box(0);
}
if (lean_is_scalar(x_895)) {
 x_896 = lean_alloc_ctor(1, 2, 0);
} else {
 x_896 = x_895;
}
lean_ctor_set(x_896, 0, x_893);
lean_ctor_set(x_896, 1, x_894);
return x_896;
}
}
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_897 = lean_ctor_get(x_817, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_817, 1);
lean_inc(x_898);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_899 = x_817;
} else {
 lean_dec_ref(x_817);
 x_899 = lean_box(0);
}
if (lean_is_scalar(x_899)) {
 x_900 = lean_alloc_ctor(1, 2, 0);
} else {
 x_900 = x_899;
}
lean_ctor_set(x_900, 0, x_897);
lean_ctor_set(x_900, 1, x_898);
return x_900;
}
}
block_712:
{
lean_object* x_710; lean_object* x_711; 
x_710 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_710, 0, x_709);
if (lean_is_scalar(x_16)) {
 x_711 = lean_alloc_ctor(1, 2, 0);
} else {
 x_711 = x_16;
 lean_ctor_set_tag(x_711, 1);
}
lean_ctor_set(x_711, 0, x_708);
lean_ctor_set(x_711, 1, x_710);
return x_711;
}
block_714:
{
lean_object* x_713; 
x_713 = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
x_709 = x_713;
goto block_712;
}
block_721:
{
lean_object* x_719; lean_object* x_720; 
x_719 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_719, 0, x_715);
lean_ctor_set(x_719, 1, x_717);
lean_ctor_set(x_719, 2, x_718);
lean_ctor_set_uint8(x_719, sizeof(void*)*3, x_716);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_708);
lean_ctor_set(x_720, 1, x_719);
return x_720;
}
block_724:
{
lean_object* x_722; lean_object* x_723; 
x_722 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1;
x_723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_723, 0, x_708);
lean_ctor_set(x_723, 1, x_722);
return x_723;
}
}
}
}
else
{
uint8_t x_901; 
lean_dec_ref(x_1);
x_901 = !lean_is_exclusive(x_13);
if (x_901 == 0)
{
return x_13;
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_902 = lean_ctor_get(x_13, 0);
x_903 = lean_ctor_get(x_13, 1);
lean_inc(x_903);
lean_inc(x_902);
lean_dec(x_13);
x_904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_904, 0, x_902);
lean_ctor_set(x_904, 1, x_903);
return x_904;
}
}
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; 
lean_dec(x_2);
x_905 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_906 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_906, 0, x_3);
lean_ctor_set(x_906, 1, x_905);
x_907 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_906);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; uint8_t x_914; 
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_907, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 x_910 = x_907;
} else {
 lean_dec_ref(x_907);
 x_910 = lean_box(0);
}
x_911 = lean_ctor_get(x_908, 0);
x_912 = lean_ctor_get(x_908, 1);
x_913 = lean_string_utf8_byte_size(x_911);
x_914 = lean_nat_dec_lt(x_912, x_913);
lean_dec(x_913);
if (x_914 == 0)
{
lean_object* x_915; lean_object* x_916; 
lean_dec(x_909);
lean_dec_ref(x_1);
x_915 = lean_box(0);
if (lean_is_scalar(x_910)) {
 x_916 = lean_alloc_ctor(1, 2, 0);
} else {
 x_916 = x_910;
 lean_ctor_set_tag(x_916, 1);
}
lean_ctor_set(x_916, 0, x_908);
lean_ctor_set(x_916, 1, x_915);
return x_916;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_926; uint8_t x_927; lean_object* x_928; lean_object* x_929; lean_object* x_936; uint8_t x_937; 
lean_inc(x_912);
lean_inc_ref(x_911);
if (lean_is_exclusive(x_908)) {
 lean_ctor_release(x_908, 0);
 lean_ctor_release(x_908, 1);
 x_917 = x_908;
} else {
 lean_dec_ref(x_908);
 x_917 = lean_box(0);
}
x_918 = lean_string_utf8_next_fast(x_911, x_912);
lean_dec(x_912);
if (lean_is_scalar(x_917)) {
 x_919 = lean_alloc_ctor(0, 2, 0);
} else {
 x_919 = x_917;
}
lean_ctor_set(x_919, 0, x_911);
lean_ctor_set(x_919, 1, x_918);
x_936 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
x_937 = lean_string_dec_eq(x_909, x_936);
if (x_937 == 0)
{
lean_object* x_938; uint8_t x_939; 
x_938 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
x_939 = lean_string_dec_eq(x_909, x_938);
if (x_939 == 0)
{
lean_object* x_940; uint8_t x_941; 
x_940 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_941 = lean_string_dec_eq(x_909, x_940);
lean_dec(x_909);
if (x_941 == 0)
{
lean_object* x_942; lean_object* x_943; 
lean_dec(x_910);
lean_dec_ref(x_1);
x_942 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3;
x_943 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_943, 0, x_919);
lean_ctor_set(x_943, 1, x_942);
return x_943;
}
else
{
lean_object* x_944; 
x_944 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
lean_dec(x_910);
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
if (lean_is_exclusive(x_944)) {
 lean_ctor_release(x_944, 0);
 x_946 = x_944;
} else {
 lean_dec_ref(x_944);
 x_946 = lean_box(0);
}
if (lean_is_scalar(x_946)) {
 x_947 = lean_alloc_ctor(1, 1, 0);
} else {
 x_947 = x_946;
 lean_ctor_set_tag(x_947, 1);
}
lean_ctor_set(x_947, 0, x_945);
x_948 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_948, 0, x_919);
lean_ctor_set(x_948, 1, x_947);
return x_948;
}
else
{
lean_object* x_949; lean_object* x_950; 
x_949 = lean_ctor_get(x_944, 0);
lean_inc(x_949);
lean_dec_ref(x_944);
lean_inc(x_949);
x_950 = l_Lean_Json_getObjVal_x3f(x_949, x_938);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; 
lean_dec(x_949);
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
lean_dec_ref(x_950);
x_920 = x_951;
goto block_923;
}
else
{
lean_object* x_952; 
x_952 = lean_ctor_get(x_950, 0);
lean_inc(x_952);
lean_dec_ref(x_950);
if (lean_obj_tag(x_952) == 3)
{
lean_object* x_953; lean_object* x_954; uint8_t x_955; 
x_953 = lean_ctor_get(x_952, 0);
lean_inc_ref(x_953);
lean_dec_ref(x_952);
x_954 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
x_955 = lean_string_dec_eq(x_953, x_954);
lean_dec_ref(x_953);
if (x_955 == 0)
{
lean_dec(x_949);
goto block_925;
}
else
{
lean_object* x_956; 
lean_inc(x_949);
x_956 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(x_949, x_936);
if (lean_obj_tag(x_956) == 0)
{
goto block_983;
}
else
{
lean_object* x_984; lean_object* x_985; 
x_984 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_949);
x_985 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_949, x_984);
if (lean_obj_tag(x_985) == 0)
{
lean_dec_ref(x_985);
goto block_983;
}
else
{
lean_dec_ref(x_985);
lean_dec_ref(x_956);
lean_dec(x_949);
lean_dec(x_910);
goto block_935;
}
}
block_978:
{
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; 
lean_dec(x_949);
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
lean_dec_ref(x_956);
x_920 = x_957;
goto block_923;
}
else
{
lean_object* x_958; lean_object* x_959; 
x_958 = lean_ctor_get(x_956, 0);
lean_inc(x_958);
lean_dec_ref(x_956);
x_959 = l_Lean_Json_getObjVal_x3f(x_949, x_940);
if (lean_obj_tag(x_959) == 0)
{
lean_object* x_960; 
lean_dec(x_958);
x_960 = lean_ctor_get(x_959, 0);
lean_inc(x_960);
lean_dec_ref(x_959);
x_920 = x_960;
goto block_923;
}
else
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_961 = lean_ctor_get(x_959, 0);
lean_inc(x_961);
lean_dec_ref(x_959);
x_962 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
lean_inc(x_961);
x_963 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(x_961, x_962);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; 
lean_dec(x_961);
lean_dec(x_958);
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
lean_dec_ref(x_963);
x_920 = x_964;
goto block_923;
}
else
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; 
x_965 = lean_ctor_get(x_963, 0);
lean_inc(x_965);
lean_dec_ref(x_963);
x_966 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
lean_inc(x_961);
x_967 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_961, x_966);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_968; 
lean_dec(x_965);
lean_dec(x_961);
lean_dec(x_958);
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
lean_dec_ref(x_967);
x_920 = x_968;
goto block_923;
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; 
lean_dec(x_910);
x_969 = lean_ctor_get(x_967, 0);
lean_inc(x_969);
lean_dec_ref(x_967);
x_970 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_971 = l_Lean_Json_getObjVal_x3f(x_961, x_970);
if (lean_obj_tag(x_971) == 0)
{
lean_object* x_972; uint8_t x_973; 
lean_dec_ref(x_971);
x_972 = lean_box(0);
x_973 = lean_unbox(x_965);
lean_dec(x_965);
x_926 = x_958;
x_927 = x_973;
x_928 = x_969;
x_929 = x_972;
goto block_932;
}
else
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; uint8_t x_977; 
x_974 = lean_ctor_get(x_971, 0);
lean_inc(x_974);
if (lean_is_exclusive(x_971)) {
 lean_ctor_release(x_971, 0);
 x_975 = x_971;
} else {
 lean_dec_ref(x_971);
 x_975 = lean_box(0);
}
if (lean_is_scalar(x_975)) {
 x_976 = lean_alloc_ctor(1, 1, 0);
} else {
 x_976 = x_975;
}
lean_ctor_set(x_976, 0, x_974);
x_977 = lean_unbox(x_965);
lean_dec(x_965);
x_926 = x_958;
x_927 = x_977;
x_928 = x_969;
x_929 = x_976;
goto block_932;
}
}
}
}
}
}
block_983:
{
lean_object* x_979; lean_object* x_980; 
x_979 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_949);
x_980 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_949, x_979);
if (lean_obj_tag(x_980) == 0)
{
lean_dec_ref(x_980);
if (lean_obj_tag(x_956) == 0)
{
goto block_978;
}
else
{
lean_object* x_981; lean_object* x_982; 
x_981 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
lean_inc(x_949);
x_982 = l_Lean_Json_getObjVal_x3f(x_949, x_981);
if (lean_obj_tag(x_982) == 0)
{
lean_dec_ref(x_982);
goto block_978;
}
else
{
lean_dec_ref(x_982);
lean_dec_ref(x_956);
lean_dec(x_949);
lean_dec(x_910);
goto block_935;
}
}
}
else
{
lean_dec_ref(x_980);
lean_dec_ref(x_956);
lean_dec(x_949);
lean_dec(x_910);
goto block_935;
}
}
}
}
else
{
lean_dec(x_952);
lean_dec(x_949);
goto block_925;
}
}
}
}
}
else
{
lean_object* x_986; 
lean_dec(x_910);
lean_dec(x_909);
lean_dec_ref(x_1);
x_986 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_919);
if (lean_obj_tag(x_986) == 0)
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; uint8_t x_992; 
x_987 = lean_ctor_get(x_986, 0);
lean_inc(x_987);
if (lean_is_exclusive(x_986)) {
 lean_ctor_release(x_986, 0);
 lean_ctor_release(x_986, 1);
 x_988 = x_986;
} else {
 lean_dec_ref(x_986);
 x_988 = lean_box(0);
}
x_989 = lean_ctor_get(x_987, 0);
x_990 = lean_ctor_get(x_987, 1);
x_991 = lean_string_utf8_byte_size(x_989);
x_992 = lean_nat_dec_lt(x_990, x_991);
lean_dec(x_991);
if (x_992 == 0)
{
lean_object* x_993; lean_object* x_994; 
x_993 = lean_box(0);
if (lean_is_scalar(x_988)) {
 x_994 = lean_alloc_ctor(1, 2, 0);
} else {
 x_994 = x_988;
 lean_ctor_set_tag(x_994, 1);
}
lean_ctor_set(x_994, 0, x_987);
lean_ctor_set(x_994, 1, x_993);
return x_994;
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
lean_inc(x_990);
lean_inc_ref(x_989);
lean_dec(x_988);
if (lean_is_exclusive(x_987)) {
 lean_ctor_release(x_987, 0);
 lean_ctor_release(x_987, 1);
 x_995 = x_987;
} else {
 lean_dec_ref(x_987);
 x_995 = lean_box(0);
}
x_996 = lean_string_utf8_next_fast(x_989, x_990);
lean_dec(x_990);
if (lean_is_scalar(x_995)) {
 x_997 = lean_alloc_ctor(0, 2, 0);
} else {
 x_997 = x_995;
}
lean_ctor_set(x_997, 0, x_989);
lean_ctor_set(x_997, 1, x_996);
x_998 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_997);
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; uint8_t x_1004; 
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 x_1000 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1000 = lean_box(0);
}
x_1001 = lean_ctor_get(x_999, 0);
x_1002 = lean_ctor_get(x_999, 1);
x_1003 = lean_string_utf8_byte_size(x_1001);
x_1004 = lean_nat_dec_lt(x_1002, x_1003);
lean_dec(x_1003);
if (x_1004 == 0)
{
lean_object* x_1005; lean_object* x_1006; 
x_1005 = lean_box(0);
if (lean_is_scalar(x_1000)) {
 x_1006 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1006 = x_1000;
 lean_ctor_set_tag(x_1006, 1);
}
lean_ctor_set(x_1006, 0, x_999);
lean_ctor_set(x_1006, 1, x_1005);
return x_1006;
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_inc(x_1002);
lean_inc_ref(x_1001);
lean_dec(x_1000);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 lean_ctor_release(x_999, 1);
 x_1007 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1007 = lean_box(0);
}
x_1008 = lean_string_utf8_next_fast(x_1001, x_1002);
lean_dec(x_1002);
if (lean_is_scalar(x_1007)) {
 x_1009 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1009 = x_1007;
}
lean_ctor_set(x_1009, 0, x_1001);
lean_ctor_set(x_1009, 1, x_1008);
x_1010 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_1009);
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_1010, 1);
lean_inc(x_1012);
if (lean_is_exclusive(x_1010)) {
 lean_ctor_release(x_1010, 0);
 lean_ctor_release(x_1010, 1);
 x_1013 = x_1010;
} else {
 lean_dec_ref(x_1010);
 x_1013 = lean_box(0);
}
x_1014 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1014, 0, x_1012);
if (lean_is_scalar(x_1013)) {
 x_1015 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1015 = x_1013;
}
lean_ctor_set(x_1015, 0, x_1011);
lean_ctor_set(x_1015, 1, x_1014);
return x_1015;
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1016 = lean_ctor_get(x_1010, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1010, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_1010)) {
 lean_ctor_release(x_1010, 0);
 lean_ctor_release(x_1010, 1);
 x_1018 = x_1010;
} else {
 lean_dec_ref(x_1010);
 x_1018 = lean_box(0);
}
if (lean_is_scalar(x_1018)) {
 x_1019 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1019 = x_1018;
}
lean_ctor_set(x_1019, 0, x_1016);
lean_ctor_set(x_1019, 1, x_1017);
return x_1019;
}
}
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1020 = lean_ctor_get(x_998, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_998, 1);
lean_inc(x_1021);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 x_1022 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1022 = lean_box(0);
}
if (lean_is_scalar(x_1022)) {
 x_1023 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1023 = x_1022;
}
lean_ctor_set(x_1023, 0, x_1020);
lean_ctor_set(x_1023, 1, x_1021);
return x_1023;
}
}
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
x_1024 = lean_ctor_get(x_986, 0);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_986, 1);
lean_inc(x_1025);
if (lean_is_exclusive(x_986)) {
 lean_ctor_release(x_986, 0);
 lean_ctor_release(x_986, 1);
 x_1026 = x_986;
} else {
 lean_dec_ref(x_986);
 x_1026 = lean_box(0);
}
if (lean_is_scalar(x_1026)) {
 x_1027 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1027 = x_1026;
}
lean_ctor_set(x_1027, 0, x_1024);
lean_ctor_set(x_1027, 1, x_1025);
return x_1027;
}
}
}
else
{
lean_object* x_1028; 
lean_dec(x_910);
lean_dec(x_909);
lean_dec_ref(x_1);
x_1028 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(x_919);
if (lean_obj_tag(x_1028) == 0)
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; uint8_t x_1035; 
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1028, 1);
lean_inc(x_1030);
if (lean_is_exclusive(x_1028)) {
 lean_ctor_release(x_1028, 0);
 lean_ctor_release(x_1028, 1);
 x_1031 = x_1028;
} else {
 lean_dec_ref(x_1028);
 x_1031 = lean_box(0);
}
x_1032 = lean_ctor_get(x_1029, 0);
x_1033 = lean_ctor_get(x_1029, 1);
x_1034 = lean_string_utf8_byte_size(x_1032);
x_1035 = lean_nat_dec_lt(x_1033, x_1034);
lean_dec(x_1034);
if (x_1035 == 0)
{
lean_object* x_1036; lean_object* x_1037; 
lean_dec(x_1030);
x_1036 = lean_box(0);
if (lean_is_scalar(x_1031)) {
 x_1037 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1037 = x_1031;
 lean_ctor_set_tag(x_1037, 1);
}
lean_ctor_set(x_1037, 0, x_1029);
lean_ctor_set(x_1037, 1, x_1036);
return x_1037;
}
else
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
lean_inc(x_1033);
lean_inc_ref(x_1032);
lean_dec(x_1031);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 lean_ctor_release(x_1029, 1);
 x_1038 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1038 = lean_box(0);
}
x_1039 = lean_string_utf8_next_fast(x_1032, x_1033);
lean_dec(x_1033);
if (lean_is_scalar(x_1038)) {
 x_1040 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1040 = x_1038;
}
lean_ctor_set(x_1040, 0, x_1032);
lean_ctor_set(x_1040, 1, x_1039);
x_1041 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_1040);
if (lean_obj_tag(x_1041) == 0)
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; uint8_t x_1047; 
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1043 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1043 = lean_box(0);
}
x_1044 = lean_ctor_get(x_1042, 0);
x_1045 = lean_ctor_get(x_1042, 1);
x_1046 = lean_string_utf8_byte_size(x_1044);
x_1047 = lean_nat_dec_lt(x_1045, x_1046);
lean_dec(x_1046);
if (x_1047 == 0)
{
lean_object* x_1048; lean_object* x_1049; 
lean_dec(x_1030);
x_1048 = lean_box(0);
if (lean_is_scalar(x_1043)) {
 x_1049 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1049 = x_1043;
 lean_ctor_set_tag(x_1049, 1);
}
lean_ctor_set(x_1049, 0, x_1042);
lean_ctor_set(x_1049, 1, x_1048);
return x_1049;
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
lean_inc(x_1045);
lean_inc_ref(x_1044);
lean_dec(x_1043);
if (lean_is_exclusive(x_1042)) {
 lean_ctor_release(x_1042, 0);
 lean_ctor_release(x_1042, 1);
 x_1050 = x_1042;
} else {
 lean_dec_ref(x_1042);
 x_1050 = lean_box(0);
}
x_1051 = lean_string_utf8_next_fast(x_1044, x_1045);
lean_dec(x_1045);
if (lean_is_scalar(x_1050)) {
 x_1052 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1052 = x_1050;
}
lean_ctor_set(x_1052, 0, x_1044);
lean_ctor_set(x_1052, 1, x_1051);
x_1053 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_1052);
if (lean_obj_tag(x_1053) == 0)
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; uint8_t x_1059; 
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
if (lean_is_exclusive(x_1053)) {
 lean_ctor_release(x_1053, 0);
 lean_ctor_release(x_1053, 1);
 x_1055 = x_1053;
} else {
 lean_dec_ref(x_1053);
 x_1055 = lean_box(0);
}
x_1056 = lean_ctor_get(x_1054, 0);
x_1057 = lean_ctor_get(x_1054, 1);
x_1058 = lean_string_utf8_byte_size(x_1056);
x_1059 = lean_nat_dec_lt(x_1057, x_1058);
lean_dec(x_1058);
if (x_1059 == 0)
{
lean_object* x_1060; lean_object* x_1061; 
lean_dec(x_1030);
x_1060 = lean_box(0);
if (lean_is_scalar(x_1055)) {
 x_1061 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1061 = x_1055;
 lean_ctor_set_tag(x_1061, 1);
}
lean_ctor_set(x_1061, 0, x_1054);
lean_ctor_set(x_1061, 1, x_1060);
return x_1061;
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_inc(x_1057);
lean_inc_ref(x_1056);
lean_dec(x_1055);
if (lean_is_exclusive(x_1054)) {
 lean_ctor_release(x_1054, 0);
 lean_ctor_release(x_1054, 1);
 x_1062 = x_1054;
} else {
 lean_dec_ref(x_1054);
 x_1062 = lean_box(0);
}
x_1063 = lean_string_utf8_next_fast(x_1056, x_1057);
lean_dec(x_1057);
if (lean_is_scalar(x_1062)) {
 x_1064 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1064 = x_1062;
}
lean_ctor_set(x_1064, 0, x_1056);
lean_ctor_set(x_1064, 1, x_1063);
x_1065 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_1064);
if (lean_obj_tag(x_1065) == 0)
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; uint8_t x_1070; 
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1065, 1);
lean_inc(x_1067);
if (lean_is_exclusive(x_1065)) {
 lean_ctor_release(x_1065, 0);
 lean_ctor_release(x_1065, 1);
 x_1068 = x_1065;
} else {
 lean_dec_ref(x_1065);
 x_1068 = lean_box(0);
}
x_1069 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_1070 = lean_string_dec_eq(x_1067, x_1069);
if (x_1070 == 0)
{
lean_object* x_1071; uint8_t x_1072; 
x_1071 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_1072 = lean_string_dec_eq(x_1067, x_1071);
lean_dec(x_1067);
if (x_1072 == 0)
{
lean_object* x_1073; lean_object* x_1074; 
lean_dec(x_1030);
x_1073 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5;
if (lean_is_scalar(x_1068)) {
 x_1074 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1074 = x_1068;
 lean_ctor_set_tag(x_1074, 1);
}
lean_ctor_set(x_1074, 0, x_1066);
lean_ctor_set(x_1074, 1, x_1073);
return x_1074;
}
else
{
lean_object* x_1075; lean_object* x_1076; 
x_1075 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1075, 0, x_1030);
if (lean_is_scalar(x_1068)) {
 x_1076 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1076 = x_1068;
}
lean_ctor_set(x_1076, 0, x_1066);
lean_ctor_set(x_1076, 1, x_1075);
return x_1076;
}
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; uint8_t x_1080; 
lean_dec(x_1067);
x_1077 = lean_ctor_get(x_1066, 0);
x_1078 = lean_ctor_get(x_1066, 1);
x_1079 = lean_string_utf8_byte_size(x_1077);
x_1080 = lean_nat_dec_lt(x_1078, x_1079);
lean_dec(x_1079);
if (x_1080 == 0)
{
lean_object* x_1081; lean_object* x_1082; 
lean_dec(x_1030);
x_1081 = lean_box(0);
if (lean_is_scalar(x_1068)) {
 x_1082 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1082 = x_1068;
 lean_ctor_set_tag(x_1082, 1);
}
lean_ctor_set(x_1082, 0, x_1066);
lean_ctor_set(x_1082, 1, x_1081);
return x_1082;
}
else
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
lean_inc(x_1078);
lean_inc_ref(x_1077);
lean_dec(x_1068);
if (lean_is_exclusive(x_1066)) {
 lean_ctor_release(x_1066, 0);
 lean_ctor_release(x_1066, 1);
 x_1083 = x_1066;
} else {
 lean_dec_ref(x_1066);
 x_1083 = lean_box(0);
}
x_1084 = lean_string_utf8_next_fast(x_1077, x_1078);
lean_dec(x_1078);
if (lean_is_scalar(x_1083)) {
 x_1085 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1085 = x_1083;
}
lean_ctor_set(x_1085, 0, x_1077);
lean_ctor_set(x_1085, 1, x_1084);
x_1086 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(x_1085);
if (lean_obj_tag(x_1086) == 0)
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
x_1087 = lean_ctor_get(x_1086, 0);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1086, 1);
lean_inc(x_1088);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 lean_ctor_release(x_1086, 1);
 x_1089 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1089 = lean_box(0);
}
x_1090 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1090, 0, x_1030);
lean_ctor_set(x_1090, 1, x_1088);
if (lean_is_scalar(x_1089)) {
 x_1091 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1091 = x_1089;
}
lean_ctor_set(x_1091, 0, x_1087);
lean_ctor_set(x_1091, 1, x_1090);
return x_1091;
}
else
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
lean_dec(x_1030);
x_1092 = lean_ctor_get(x_1086, 0);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_1086, 1);
lean_inc(x_1093);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 lean_ctor_release(x_1086, 1);
 x_1094 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1094 = lean_box(0);
}
if (lean_is_scalar(x_1094)) {
 x_1095 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1095 = x_1094;
}
lean_ctor_set(x_1095, 0, x_1092);
lean_ctor_set(x_1095, 1, x_1093);
return x_1095;
}
}
}
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
lean_dec(x_1030);
x_1096 = lean_ctor_get(x_1065, 0);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1065, 1);
lean_inc(x_1097);
if (lean_is_exclusive(x_1065)) {
 lean_ctor_release(x_1065, 0);
 lean_ctor_release(x_1065, 1);
 x_1098 = x_1065;
} else {
 lean_dec_ref(x_1065);
 x_1098 = lean_box(0);
}
if (lean_is_scalar(x_1098)) {
 x_1099 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1099 = x_1098;
}
lean_ctor_set(x_1099, 0, x_1096);
lean_ctor_set(x_1099, 1, x_1097);
return x_1099;
}
}
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
lean_dec(x_1030);
x_1100 = lean_ctor_get(x_1053, 0);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_1053, 1);
lean_inc(x_1101);
if (lean_is_exclusive(x_1053)) {
 lean_ctor_release(x_1053, 0);
 lean_ctor_release(x_1053, 1);
 x_1102 = x_1053;
} else {
 lean_dec_ref(x_1053);
 x_1102 = lean_box(0);
}
if (lean_is_scalar(x_1102)) {
 x_1103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1103 = x_1102;
}
lean_ctor_set(x_1103, 0, x_1100);
lean_ctor_set(x_1103, 1, x_1101);
return x_1103;
}
}
}
else
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; 
lean_dec(x_1030);
x_1104 = lean_ctor_get(x_1041, 0);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1041, 1);
lean_inc(x_1105);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1106 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1106 = lean_box(0);
}
if (lean_is_scalar(x_1106)) {
 x_1107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1107 = x_1106;
}
lean_ctor_set(x_1107, 0, x_1104);
lean_ctor_set(x_1107, 1, x_1105);
return x_1107;
}
}
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
x_1108 = lean_ctor_get(x_1028, 0);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_1028, 1);
lean_inc(x_1109);
if (lean_is_exclusive(x_1028)) {
 lean_ctor_release(x_1028, 0);
 lean_ctor_release(x_1028, 1);
 x_1110 = x_1028;
} else {
 lean_dec_ref(x_1028);
 x_1110 = lean_box(0);
}
if (lean_is_scalar(x_1110)) {
 x_1111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1111 = x_1110;
}
lean_ctor_set(x_1111, 0, x_1108);
lean_ctor_set(x_1111, 1, x_1109);
return x_1111;
}
}
block_923:
{
lean_object* x_921; lean_object* x_922; 
x_921 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_921, 0, x_920);
if (lean_is_scalar(x_910)) {
 x_922 = lean_alloc_ctor(1, 2, 0);
} else {
 x_922 = x_910;
 lean_ctor_set_tag(x_922, 1);
}
lean_ctor_set(x_922, 0, x_919);
lean_ctor_set(x_922, 1, x_921);
return x_922;
}
block_925:
{
lean_object* x_924; 
x_924 = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
x_920 = x_924;
goto block_923;
}
block_932:
{
lean_object* x_930; lean_object* x_931; 
x_930 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_930, 0, x_926);
lean_ctor_set(x_930, 1, x_928);
lean_ctor_set(x_930, 2, x_929);
lean_ctor_set_uint8(x_930, sizeof(void*)*3, x_927);
x_931 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_931, 0, x_919);
lean_ctor_set(x_931, 1, x_930);
return x_931;
}
block_935:
{
lean_object* x_933; lean_object* x_934; 
x_933 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1;
x_934 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_934, 0, x_919);
lean_ctor_set(x_934, 1, x_933);
return x_934;
}
}
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
lean_dec_ref(x_1);
x_1112 = lean_ctor_get(x_907, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_907, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 x_1114 = x_907;
} else {
 lean_dec_ref(x_907);
 x_1114 = lean_box(0);
}
if (lean_is_scalar(x_1114)) {
 x_1115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1115 = x_1114;
}
lean_ctor_set(x_1115, 0, x_1112);
lean_ctor_set(x_1115, 1, x_1113);
return x_1115;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_Structured_fromJson_x3f(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readJson(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_20; lean_object* x_32; lean_object* x_33; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_32 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0;
lean_inc(x_5);
x_33 = l_Lean_Json_getObjVal_x3f(x_5, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_7);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_20 = x_34;
goto block_29;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec_ref(x_33);
if (lean_obj_tag(x_35) == 3)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc_ref(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1;
x_38 = lean_string_dec_eq(x_36, x_37);
lean_dec_ref(x_36);
if (x_38 == 0)
{
lean_dec(x_7);
goto block_31;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
lean_inc(x_5);
x_40 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(x_5, x_39);
if (lean_obj_tag(x_40) == 0)
{
goto block_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_40, 0);
lean_inc(x_81);
x_82 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_5);
x_83 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_5, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_dec_ref(x_83);
lean_dec(x_81);
goto block_80;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_40);
lean_dec(x_7);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_89 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_90 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(x_5, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
lean_dec_ref(x_90);
x_91 = lean_box(0);
x_85 = x_91;
goto block_88;
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
x_85 = x_90;
goto block_88;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_85 = x_94;
goto block_88;
}
}
block_88:
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_6);
return x_87;
}
}
}
block_64:
{
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_7);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_20 = x_41;
goto block_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
lean_inc(x_5);
x_44 = l_Lean_Json_getObjVal_x3f(x_5, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_7);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_20 = x_45;
goto block_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
lean_inc(x_46);
x_48 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(x_46, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_20 = x_49;
goto block_29;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
lean_inc(x_46);
x_52 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_46, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_7);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_20 = x_53;
goto block_29;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_5);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_56 = l_Lean_Json_getObjVal_x3f(x_46, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
lean_dec_ref(x_56);
x_57 = lean_box(0);
x_58 = lean_unbox(x_50);
lean_dec(x_50);
x_8 = x_54;
x_9 = x_42;
x_10 = x_58;
x_11 = x_57;
goto block_14;
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = lean_unbox(x_50);
lean_dec(x_50);
x_8 = x_54;
x_9 = x_42;
x_10 = x_60;
x_11 = x_56;
goto block_14;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_unbox(x_50);
lean_dec(x_50);
x_8 = x_54;
x_9 = x_42;
x_10 = x_63;
x_11 = x_62;
goto block_14;
}
}
}
}
}
}
}
block_80:
{
lean_object* x_65; lean_object* x_66; 
x_65 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
lean_inc(x_5);
x_66 = l_Lean_Json_getObjValAs_x3f___at_____private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(x_5, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_dec_ref(x_66);
if (lean_obj_tag(x_40) == 0)
{
goto block_64;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_40, 0);
lean_inc(x_67);
x_68 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
lean_inc(x_5);
x_69 = l_Lean_Json_getObjVal_x3f(x_5, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_dec_ref(x_69);
lean_dec(x_67);
goto block_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_40);
lean_dec(x_7);
lean_dec(x_5);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_6);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_40);
lean_dec(x_7);
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
lean_dec_ref(x_66);
x_74 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_75 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(x_5, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_dec_ref(x_75);
x_76 = lean_box(0);
x_15 = x_73;
x_16 = x_76;
goto block_19;
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
x_15 = x_73;
x_16 = x_75;
goto block_19;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_15 = x_73;
x_16 = x_79;
goto block_19;
}
}
}
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_7);
goto block_31;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_10);
if (lean_is_scalar(x_7)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_7;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
block_29:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = l_IO_FS_Stream_readMessage___closed__0;
x_22 = l_Lean_Json_compress(x_5);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = l_IO_FS_Stream_readMessage___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_20);
lean_dec_ref(x_20);
x_27 = lean_mk_io_user_error(x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
block_31:
{
lean_object* x_30; 
x_30 = l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0;
x_20 = x_30;
goto block_29;
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_4);
if (x_95 == 0)
{
return x_4;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_4, 0);
x_97 = lean_ctor_get(x_4, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_4);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___IO_FS_Stream_readMessage_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readMessage(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readMessage(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 2);
x_14 = lean_string_dec_eq(x_12, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_4);
x_15 = l_IO_FS_Stream_readRequestAs___redArg___closed__0;
x_16 = lean_string_append(x_15, x_3);
lean_dec_ref(x_3);
x_17 = l_IO_FS_Stream_readRequestAs___redArg___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_12);
lean_dec_ref(x_12);
x_20 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_mk_io_user_error(x_21);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_12);
x_23 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_24 = l_Option_toJson___redArg(x_23, x_13);
lean_inc(x_24);
x_25 = lean_apply_1(x_4, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_7);
lean_dec(x_11);
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
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_36);
return x_6;
}
else
{
lean_object* x_37; 
lean_dec(x_24);
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_37);
lean_dec_ref(x_25);
lean_ctor_set(x_7, 2, x_37);
lean_ctor_set(x_7, 1, x_3);
return x_6;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get(x_7, 1);
x_40 = lean_ctor_get(x_7, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_7);
x_41 = lean_string_dec_eq(x_39, x_3);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_40);
lean_dec(x_38);
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
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_49);
return x_6;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_39);
x_50 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_51 = l_Option_toJson___redArg(x_50, x_40);
lean_inc(x_51);
x_52 = lean_apply_1(x_4, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_38);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_IO_FS_Stream_readRequestAs___redArg___closed__3;
x_55 = l_Lean_Json_compress(x_51);
x_56 = lean_string_append(x_54, x_55);
lean_dec_ref(x_55);
x_57 = l_IO_FS_Stream_readRequestAs___redArg___closed__4;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_3);
lean_dec_ref(x_3);
x_60 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_53);
lean_dec(x_53);
x_63 = lean_mk_io_user_error(x_62);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_63);
return x_6;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_51);
x_64 = lean_ctor_get(x_52, 0);
lean_inc(x_64);
lean_dec_ref(x_52);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_38);
lean_ctor_set(x_65, 1, x_3);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_6, 0, x_65);
return x_6;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_6, 1);
lean_inc(x_66);
lean_dec(x_6);
x_67 = lean_ctor_get(x_7, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_7, 2);
lean_inc(x_69);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 x_70 = x_7;
} else {
 lean_dec_ref(x_7);
 x_70 = lean_box(0);
}
x_71 = lean_string_dec_eq(x_68, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec_ref(x_4);
x_72 = l_IO_FS_Stream_readRequestAs___redArg___closed__0;
x_73 = lean_string_append(x_72, x_3);
lean_dec_ref(x_3);
x_74 = l_IO_FS_Stream_readRequestAs___redArg___closed__1;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_string_append(x_75, x_68);
lean_dec_ref(x_68);
x_77 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_78 = lean_string_append(x_76, x_77);
x_79 = lean_mk_io_user_error(x_78);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_66);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_68);
x_81 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_82 = l_Option_toJson___redArg(x_81, x_69);
lean_inc(x_82);
x_83 = lean_apply_1(x_4, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_70);
lean_dec(x_67);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l_IO_FS_Stream_readRequestAs___redArg___closed__3;
x_86 = l_Lean_Json_compress(x_82);
x_87 = lean_string_append(x_85, x_86);
lean_dec_ref(x_86);
x_88 = l_IO_FS_Stream_readRequestAs___redArg___closed__4;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_string_append(x_89, x_3);
lean_dec_ref(x_3);
x_91 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_string_append(x_92, x_84);
lean_dec(x_84);
x_94 = lean_mk_io_user_error(x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_66);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_82);
x_96 = lean_ctor_get(x_83, 0);
lean_inc(x_96);
lean_dec_ref(x_83);
if (lean_is_scalar(x_70)) {
 x_97 = lean_alloc_ctor(0, 3, 0);
} else {
 x_97 = x_70;
}
lean_ctor_set(x_97, 0, x_67);
lean_ctor_set(x_97, 1, x_3);
lean_ctor_set(x_97, 2, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_66);
return x_98;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_99 = lean_ctor_get(x_6, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_100 = x_6;
} else {
 lean_dec_ref(x_6);
 x_100 = lean_box(0);
}
x_101 = l_IO_FS_Stream_readRequestAs___redArg___closed__6;
x_102 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_103 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_7, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_7, 2);
lean_inc(x_116);
lean_dec_ref(x_7);
x_117 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_114);
if (x_130 == 0)
{
lean_ctor_set_tag(x_114, 3);
x_118 = x_114;
goto block_129;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_114, 0);
lean_inc(x_131);
lean_dec(x_114);
x_132 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_118 = x_132;
goto block_129;
}
}
else
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_114);
if (x_133 == 0)
{
lean_ctor_set_tag(x_114, 2);
x_118 = x_114;
goto block_129;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_114, 0);
lean_inc(x_134);
lean_dec(x_114);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_118 = x_135;
goto block_129;
}
}
block_129:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_121 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_121, 0, x_115);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_127 = l_Lean_Json_opt___redArg(x_102, x_126, x_116);
x_128 = l_List_appendTR___redArg(x_125, x_127);
x_104 = x_128;
goto block_113;
}
}
case 1:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_7, 1);
lean_inc(x_137);
lean_dec_ref(x_7);
x_138 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_139 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_139, 0, x_136);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_142 = l_Lean_Json_opt___redArg(x_102, x_141, x_137);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
x_104 = x_143;
goto block_113;
}
case 2:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_7, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_7, 1);
lean_inc(x_145);
lean_dec_ref(x_7);
x_146 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_144);
if (x_155 == 0)
{
lean_ctor_set_tag(x_144, 3);
x_147 = x_144;
goto block_154;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_144, 0);
lean_inc(x_156);
lean_dec(x_144);
x_157 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_147 = x_157;
goto block_154;
}
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_144);
if (x_158 == 0)
{
lean_ctor_set_tag(x_144, 2);
x_147 = x_144;
goto block_154;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_144, 0);
lean_inc(x_159);
lean_dec(x_144);
x_160 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_147 = x_160;
goto block_154;
}
}
block_154:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_145);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_148);
lean_ctor_set(x_153, 1, x_152);
x_104 = x_153;
goto block_113;
}
}
default: 
{
lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_185; lean_object* x_186; 
x_161 = lean_ctor_get(x_7, 0);
lean_inc(x_161);
x_162 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_163 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_7, 2);
lean_inc(x_164);
lean_dec_ref(x_7);
x_165 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_185 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_161) == 0)
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_161);
if (x_203 == 0)
{
lean_ctor_set_tag(x_161, 3);
x_186 = x_161;
goto block_202;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_161, 0);
lean_inc(x_204);
lean_dec(x_161);
x_205 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_186 = x_205;
goto block_202;
}
}
else
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_161);
if (x_206 == 0)
{
lean_ctor_set_tag(x_161, 2);
x_186 = x_161;
goto block_202;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_161, 0);
lean_inc(x_207);
lean_dec(x_161);
x_208 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_186 = x_208;
goto block_202;
}
}
block_184:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
x_172 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_172, 0, x_163);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_box(0);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_170);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_178 = l_Lean_Json_opt___redArg(x_165, x_177, x_164);
x_179 = l_List_appendTR___redArg(x_176, x_178);
x_180 = l_Lean_Json_mkObj(x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_166);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_174);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_168);
lean_ctor_set(x_183, 1, x_182);
x_104 = x_183;
goto block_113;
}
block_202:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_189 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
switch (x_162) {
case 0:
{
lean_object* x_190; 
x_190 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_190;
goto block_184;
}
case 1:
{
lean_object* x_191; 
x_191 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_191;
goto block_184;
}
case 2:
{
lean_object* x_192; 
x_192 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_192;
goto block_184;
}
case 3:
{
lean_object* x_193; 
x_193 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_193;
goto block_184;
}
case 4:
{
lean_object* x_194; 
x_194 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_194;
goto block_184;
}
case 5:
{
lean_object* x_195; 
x_195 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_195;
goto block_184;
}
case 6:
{
lean_object* x_196; 
x_196 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_196;
goto block_184;
}
case 7:
{
lean_object* x_197; 
x_197 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_197;
goto block_184;
}
case 8:
{
lean_object* x_198; 
x_198 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_198;
goto block_184;
}
case 9:
{
lean_object* x_199; 
x_199 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_199;
goto block_184;
}
case 10:
{
lean_object* x_200; 
x_200 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_200;
goto block_184;
}
default: 
{
lean_object* x_201; 
x_201 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
x_166 = x_188;
x_167 = x_189;
x_168 = x_187;
x_169 = x_201;
goto block_184;
}
}
}
}
}
block_113:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_Json_mkObj(x_105);
x_107 = l_Lean_Json_compress(x_106);
x_108 = lean_string_append(x_101, x_107);
lean_dec_ref(x_107);
x_109 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_110 = lean_string_append(x_108, x_109);
x_111 = lean_mk_io_user_error(x_110);
if (lean_is_scalar(x_100)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_100;
 lean_ctor_set_tag(x_112, 1);
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_99);
return x_112;
}
}
}
else
{
uint8_t x_209; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_209 = !lean_is_exclusive(x_6);
if (x_209 == 0)
{
return x_6;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_6, 0);
x_211 = lean_ctor_get(x_6, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_6);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readRequestAs___redArg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readRequestAs___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readRequestAs(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readMessage(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_string_dec_eq(x_11, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_7);
lean_dec(x_12);
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
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_11);
x_22 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_23 = l_Option_toJson___redArg(x_22, x_12);
lean_inc(x_23);
x_24 = lean_apply_1(x_4, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_35);
return x_6;
}
else
{
lean_object* x_36; 
lean_dec(x_23);
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
lean_dec_ref(x_24);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_36);
lean_ctor_set(x_7, 0, x_3);
return x_6;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_39 = lean_string_dec_eq(x_37, x_3);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_38);
lean_dec_ref(x_4);
x_40 = l_IO_FS_Stream_readRequestAs___redArg___closed__0;
x_41 = lean_string_append(x_40, x_3);
lean_dec_ref(x_3);
x_42 = l_IO_FS_Stream_readRequestAs___redArg___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_string_append(x_43, x_37);
lean_dec_ref(x_37);
x_45 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_mk_io_user_error(x_46);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_47);
return x_6;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_37);
x_48 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_49 = l_Option_toJson___redArg(x_48, x_38);
lean_inc(x_49);
x_50 = lean_apply_1(x_4, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_IO_FS_Stream_readRequestAs___redArg___closed__3;
x_53 = l_Lean_Json_compress(x_49);
x_54 = lean_string_append(x_52, x_53);
lean_dec_ref(x_53);
x_55 = l_IO_FS_Stream_readRequestAs___redArg___closed__4;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_string_append(x_56, x_3);
lean_dec_ref(x_3);
x_58 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_string_append(x_59, x_51);
lean_dec(x_51);
x_61 = lean_mk_io_user_error(x_60);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_61);
return x_6;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_49);
x_62 = lean_ctor_get(x_50, 0);
lean_inc(x_62);
lean_dec_ref(x_50);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_6, 0, x_63);
return x_6;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_6, 1);
lean_inc(x_64);
lean_dec(x_6);
x_65 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_67 = x_7;
} else {
 lean_dec_ref(x_7);
 x_67 = lean_box(0);
}
x_68 = lean_string_dec_eq(x_65, x_3);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec_ref(x_4);
x_69 = l_IO_FS_Stream_readRequestAs___redArg___closed__0;
x_70 = lean_string_append(x_69, x_3);
lean_dec_ref(x_3);
x_71 = l_IO_FS_Stream_readRequestAs___redArg___closed__1;
x_72 = lean_string_append(x_70, x_71);
x_73 = lean_string_append(x_72, x_65);
lean_dec_ref(x_65);
x_74 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_mk_io_user_error(x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_64);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_65);
x_78 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_79 = l_Option_toJson___redArg(x_78, x_66);
lean_inc(x_79);
x_80 = lean_apply_1(x_4, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_67);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = l_IO_FS_Stream_readRequestAs___redArg___closed__3;
x_83 = l_Lean_Json_compress(x_79);
x_84 = lean_string_append(x_82, x_83);
lean_dec_ref(x_83);
x_85 = l_IO_FS_Stream_readRequestAs___redArg___closed__4;
x_86 = lean_string_append(x_84, x_85);
x_87 = lean_string_append(x_86, x_3);
lean_dec_ref(x_3);
x_88 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_string_append(x_89, x_81);
lean_dec(x_81);
x_91 = lean_mk_io_user_error(x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_64);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_79);
x_93 = lean_ctor_get(x_80, 0);
lean_inc(x_93);
lean_dec_ref(x_80);
if (lean_is_scalar(x_67)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_67;
 lean_ctor_set_tag(x_94, 0);
}
lean_ctor_set(x_94, 0, x_3);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_64);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_96 = lean_ctor_get(x_6, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_97 = x_6;
} else {
 lean_dec_ref(x_6);
 x_97 = lean_box(0);
}
x_98 = l_IO_FS_Stream_readNotificationAs___redArg___closed__0;
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
lean_ctor_set(x_167, 0, x_163);
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
lean_ctor_set(x_178, 0, x_164);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_171);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_165);
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
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
x_166 = x_187;
goto block_181;
}
case 1:
{
lean_object* x_188; 
x_188 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
x_166 = x_188;
goto block_181;
}
case 2:
{
lean_object* x_189; 
x_189 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
x_166 = x_189;
goto block_181;
}
case 3:
{
lean_object* x_190; 
x_190 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
x_166 = x_190;
goto block_181;
}
case 4:
{
lean_object* x_191; 
x_191 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
x_166 = x_191;
goto block_181;
}
case 5:
{
lean_object* x_192; 
x_192 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
x_166 = x_192;
goto block_181;
}
case 6:
{
lean_object* x_193; 
x_193 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
x_166 = x_193;
goto block_181;
}
case 7:
{
lean_object* x_194; 
x_194 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
x_166 = x_194;
goto block_181;
}
case 8:
{
lean_object* x_195; 
x_195 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
x_166 = x_195;
goto block_181;
}
case 9:
{
lean_object* x_196; 
x_196 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
x_166 = x_196;
goto block_181;
}
case 10:
{
lean_object* x_197; 
x_197 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
x_166 = x_197;
goto block_181;
}
default: 
{
lean_object* x_198; 
x_198 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
x_163 = x_186;
x_164 = x_185;
x_165 = x_184;
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
if (lean_is_scalar(x_97)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_97;
 lean_ctor_set_tag(x_109, 1);
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_96);
return x_109;
}
}
}
else
{
uint8_t x_206; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_206 = !lean_is_exclusive(x_6);
if (x_206 == 0)
{
return x_6;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_6, 0);
x_208 = lean_ctor_get(x_6, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_6);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readNotificationAs___redArg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readNotificationAs___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readNotificationAs(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readMessage(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
if (lean_obj_tag(x_7) == 2)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
x_19 = l_Lean_JsonRpc_instBEqRequestID_beq(x_17, x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_7);
lean_dec(x_18);
lean_dec_ref(x_4);
x_20 = l_IO_FS_Stream_readResponseAs___redArg___closed__0;
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_32);
lean_dec_ref(x_3);
x_33 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
x_34 = lean_string_append(x_33, x_32);
lean_dec_ref(x_32);
x_35 = lean_string_append(x_34, x_33);
x_21 = x_35;
goto block_31;
}
case 1:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_36);
lean_dec_ref(x_3);
x_37 = l_Lean_JsonNumber_toString(x_36);
x_21 = x_37;
goto block_31;
}
default: 
{
lean_object* x_38; 
x_38 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
x_21 = x_38;
goto block_31;
}
}
block_31:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = l_IO_FS_Stream_readResponseAs___redArg___closed__1;
x_24 = lean_string_append(x_22, x_23);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_25);
lean_dec_ref(x_17);
x_26 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
x_27 = lean_string_append(x_26, x_25);
lean_dec_ref(x_25);
x_28 = lean_string_append(x_27, x_26);
x_10 = x_24;
x_11 = x_28;
goto block_15;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_29);
lean_dec_ref(x_17);
x_30 = l_Lean_JsonNumber_toString(x_29);
x_10 = x_24;
x_11 = x_30;
goto block_15;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_17);
lean_dec(x_9);
lean_inc(x_18);
x_39 = lean_apply_1(x_4, x_18);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_IO_FS_Stream_readResponseAs___redArg___closed__2;
x_42 = l_Lean_Json_compress(x_18);
x_43 = lean_string_append(x_41, x_42);
lean_dec_ref(x_42);
x_44 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_string_append(x_45, x_40);
lean_dec(x_40);
x_47 = lean_mk_io_user_error(x_46);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_8);
lean_ctor_set(x_7, 0, x_47);
return x_7;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_18);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec_ref(x_39);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_48);
lean_ctor_set(x_7, 0, x_3);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_7);
lean_ctor_set(x_49, 1, x_8);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_7, 0);
x_51 = lean_ctor_get(x_7, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_7);
x_52 = l_Lean_JsonRpc_instBEqRequestID_beq(x_50, x_3);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
lean_dec_ref(x_4);
x_53 = l_IO_FS_Stream_readResponseAs___redArg___closed__0;
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_65);
lean_dec_ref(x_3);
x_66 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
x_67 = lean_string_append(x_66, x_65);
lean_dec_ref(x_65);
x_68 = lean_string_append(x_67, x_66);
x_54 = x_68;
goto block_64;
}
case 1:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_69);
lean_dec_ref(x_3);
x_70 = l_Lean_JsonNumber_toString(x_69);
x_54 = x_70;
goto block_64;
}
default: 
{
lean_object* x_71; 
x_71 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1;
x_54 = x_71;
goto block_64;
}
}
block_64:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_string_append(x_53, x_54);
lean_dec_ref(x_54);
x_56 = l_IO_FS_Stream_readResponseAs___redArg___closed__1;
x_57 = lean_string_append(x_55, x_56);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_58);
lean_dec_ref(x_50);
x_59 = l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0;
x_60 = lean_string_append(x_59, x_58);
lean_dec_ref(x_58);
x_61 = lean_string_append(x_60, x_59);
x_10 = x_57;
x_11 = x_61;
goto block_15;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_62);
lean_dec_ref(x_50);
x_63 = l_Lean_JsonNumber_toString(x_62);
x_10 = x_57;
x_11 = x_63;
goto block_15;
}
}
}
else
{
lean_object* x_72; 
lean_dec(x_50);
lean_dec(x_9);
lean_inc(x_51);
x_72 = lean_apply_1(x_4, x_51);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_3);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l_IO_FS_Stream_readResponseAs___redArg___closed__2;
x_75 = l_Lean_Json_compress(x_51);
x_76 = lean_string_append(x_74, x_75);
lean_dec_ref(x_75);
x_77 = l_IO_FS_Stream_readRequestAs___redArg___closed__5;
x_78 = lean_string_append(x_76, x_77);
x_79 = lean_string_append(x_78, x_73);
lean_dec(x_73);
x_80 = lean_mk_io_user_error(x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_8);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_51);
x_82 = lean_ctor_get(x_72, 0);
lean_inc(x_82);
lean_dec_ref(x_72);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_3);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_8);
return x_84;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_9);
lean_dec_ref(x_4);
lean_dec(x_3);
x_85 = l_IO_FS_Stream_readResponseAs___redArg___closed__3;
x_86 = l_Lean_JsonRpc_instToJsonMessage___closed__0;
x_87 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3;
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_7, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_7, 2);
lean_inc(x_100);
lean_dec_ref(x_7);
x_101 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_98);
if (x_114 == 0)
{
lean_ctor_set_tag(x_98, 3);
x_102 = x_98;
goto block_113;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_98, 0);
lean_inc(x_115);
lean_dec(x_98);
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_102 = x_116;
goto block_113;
}
}
else
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_98);
if (x_117 == 0)
{
lean_ctor_set_tag(x_98, 2);
x_102 = x_98;
goto block_113;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_98, 0);
lean_inc(x_118);
lean_dec(x_98);
x_119 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_102 = x_119;
goto block_113;
}
}
block_113:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_105 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_105, 0, x_99);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_111 = l_Lean_Json_opt___redArg(x_86, x_110, x_100);
x_112 = l_List_appendTR___redArg(x_109, x_111);
x_88 = x_112;
goto block_97;
}
}
case 1:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_7, 1);
lean_inc(x_121);
lean_dec_ref(x_7);
x_122 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5;
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_120);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6;
x_126 = l_Lean_Json_opt___redArg(x_86, x_125, x_121);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_88 = x_127;
goto block_97;
}
case 2:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_7, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_7, 1);
lean_inc(x_129);
lean_dec_ref(x_7);
x_130 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_128);
if (x_139 == 0)
{
lean_ctor_set_tag(x_128, 3);
x_131 = x_128;
goto block_138;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_128, 0);
lean_inc(x_140);
lean_dec(x_128);
x_141 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_131 = x_141;
goto block_138;
}
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_128);
if (x_142 == 0)
{
lean_ctor_set_tag(x_128, 2);
x_131 = x_128;
goto block_138;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_128, 0);
lean_inc(x_143);
lean_dec(x_128);
x_144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_131 = x_144;
goto block_138;
}
}
block_138:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7;
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_136);
x_88 = x_137;
goto block_97;
}
}
default: 
{
lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_169; lean_object* x_170; 
x_145 = lean_ctor_get(x_7, 0);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_147 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_147);
x_148 = lean_ctor_get(x_7, 2);
lean_inc(x_148);
lean_dec_ref(x_7);
x_149 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_169 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4;
if (lean_obj_tag(x_145) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_145);
if (x_187 == 0)
{
lean_ctor_set_tag(x_145, 3);
x_170 = x_145;
goto block_186;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_145, 0);
lean_inc(x_188);
lean_dec(x_145);
x_189 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_170 = x_189;
goto block_186;
}
}
else
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_145);
if (x_190 == 0)
{
lean_ctor_set_tag(x_145, 2);
x_170 = x_145;
goto block_186;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_145, 0);
lean_inc(x_191);
lean_dec(x_145);
x_192 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_170 = x_192;
goto block_186;
}
}
block_168:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8;
x_156 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_156, 0, x_147);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9;
x_162 = l_Lean_Json_opt___redArg(x_149, x_161, x_148);
x_163 = l_List_appendTR___redArg(x_160, x_162);
x_164 = l_Lean_Json_mkObj(x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_152);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_158);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_150);
lean_ctor_set(x_167, 1, x_166);
x_88 = x_167;
goto block_97;
}
block_186:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10;
x_173 = l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11;
switch (x_146) {
case 0:
{
lean_object* x_174; 
x_174 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_174;
goto block_168;
}
case 1:
{
lean_object* x_175; 
x_175 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_175;
goto block_168;
}
case 2:
{
lean_object* x_176; 
x_176 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_176;
goto block_168;
}
case 3:
{
lean_object* x_177; 
x_177 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_177;
goto block_168;
}
case 4:
{
lean_object* x_178; 
x_178 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_178;
goto block_168;
}
case 5:
{
lean_object* x_179; 
x_179 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_179;
goto block_168;
}
case 6:
{
lean_object* x_180; 
x_180 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_180;
goto block_168;
}
case 7:
{
lean_object* x_181; 
x_181 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_181;
goto block_168;
}
case 8:
{
lean_object* x_182; 
x_182 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_182;
goto block_168;
}
case 9:
{
lean_object* x_183; 
x_183 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_183;
goto block_168;
}
case 10:
{
lean_object* x_184; 
x_184 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_184;
goto block_168;
}
default: 
{
lean_object* x_185; 
x_185 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
x_150 = x_171;
x_151 = x_173;
x_152 = x_172;
x_153 = x_185;
goto block_168;
}
}
}
}
}
block_97:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Json_mkObj(x_89);
x_91 = l_Lean_Json_compress(x_90);
x_92 = lean_string_append(x_85, x_91);
lean_dec_ref(x_91);
x_93 = l_IO_FS_Stream_readRequestAs___redArg___closed__2;
x_94 = lean_string_append(x_92, x_93);
x_95 = lean_mk_io_user_error(x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_8);
return x_96;
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_mk_io_user_error(x_12);
if (lean_is_scalar(x_9)) {
 x_14 = lean_alloc_ctor(1, 2, 0);
} else {
 x_14 = x_9;
 lean_ctor_set_tag(x_14, 1);
}
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
else
{
uint8_t x_193; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_193 = !lean_is_exclusive(x_6);
if (x_193 == 0)
{
return x_6;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_6, 0);
x_195 = lean_ctor_get(x_6, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_6);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readResponseAs___redArg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readResponseAs___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readResponseAs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_23 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_22, x_12);
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
x_39 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_38, x_35);
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
x_47 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__0(x_46, x_42);
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
lean_ctor_set(x_76, 0, x_73);
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
x_84 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(x_83, x_71);
lean_dec(x_71);
x_85 = l_List_appendTR___redArg(x_82, x_84);
x_86 = l_Lean_Json_mkObj(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_72);
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
x_72 = x_94;
x_73 = x_95;
x_74 = x_93;
x_75 = x_96;
goto block_90;
}
case 1:
{
lean_object* x_97; 
x_97 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
x_72 = x_94;
x_73 = x_95;
x_74 = x_93;
x_75 = x_97;
goto block_90;
}
case 2:
{
lean_object* x_98; 
x_98 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
x_72 = x_94;
x_73 = x_95;
x_74 = x_93;
x_75 = x_98;
goto block_90;
}
case 3:
{
lean_object* x_99; 
x_99 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
x_72 = x_94;
x_73 = x_95;
x_74 = x_93;
x_75 = x_99;
goto block_90;
}
case 4:
{
lean_object* x_100; 
x_100 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
x_72 = x_94;
x_73 = x_95;
x_74 = x_93;
x_75 = x_100;
goto block_90;
}
case 5:
{
lean_object* x_101; 
x_101 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
x_72 = x_94;
x_73 = x_95;
x_74 = x_93;
x_75 = x_101;
goto block_90;
}
case 6:
{
lean_object* x_102; 
x_102 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
x_72 = x_94;
x_73 = x_95;
x_74 = x_93;
x_75 = x_102;
goto block_90;
}
case 7:
{
lean_object* x_103; 
x_103 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
x_72 = x_94;
x_73 = x_95;
x_74 = x_93;
x_75 = x_103;
goto block_90;
}
case 8:
{
lean_object* x_104; 
x_104 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
x_72 = x_94;
x_73 = x_95;
x_74 = x_93;
x_75 = x_104;
goto block_90;
}
case 9:
{
lean_object* x_105; 
x_105 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
x_72 = x_94;
x_73 = x_95;
x_74 = x_93;
x_75 = x_105;
goto block_90;
}
case 10:
{
lean_object* x_106; 
x_106 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
x_72 = x_94;
x_73 = x_95;
x_74 = x_93;
x_75 = x_106;
goto block_90;
}
default: 
{
lean_object* x_107; 
x_107 = l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
x_72 = x_94;
x_73 = x_95;
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
x_8 = l_IO_FS_Stream_writeJson(x_1, x_7, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___IO_FS_Stream_writeMessage_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = l_IO_FS_Stream_writeMessage(x_2, x_10, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeRequest___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_IO_FS_Stream_writeMessage(x_2, x_9, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeNotification___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_IO_FS_Stream_writeMessage(x_2, x_3, x_4);
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
x_13 = l_IO_FS_Stream_writeMessage(x_2, x_12, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeResponse___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_IO_FS_Stream_writeMessage(x_1, x_2, x_3);
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
x_13 = l_IO_FS_Stream_writeMessage(x_1, x_12, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_IO_FS_Stream_writeMessage(x_2, x_11, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeResponseErrorWithData___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Lean_Data_Json_Stream(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json_Stream(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_FromToJson_Basic(builtin, lean_io_mk_world());
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
l_Lean_JsonRpc_instOrdRequestID___closed__0 = _init_l_Lean_JsonRpc_instOrdRequestID___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instOrdRequestID___closed__0);
l_Lean_JsonRpc_instOrdRequestID = _init_l_Lean_JsonRpc_instOrdRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instOrdRequestID);
l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0 = _init_l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0();
lean_mark_persistent(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0);
l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1 = _init_l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1);
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
l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage = _init_l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage();
lean_mark_persistent(l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage);
l_Lean_JsonRpc_instCoeStringRequestID = _init_l_Lean_JsonRpc_instCoeStringRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instCoeStringRequestID);
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
l_Lean_JsonRpc_instFromJsonRequestID = _init_l_Lean_JsonRpc_instFromJsonRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonRequestID);
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
l_Lean_JsonRpc_instFromJsonMessage___closed__3 = _init_l_Lean_JsonRpc_instFromJsonMessage___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessage___closed__3);
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
