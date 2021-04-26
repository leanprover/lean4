// Lean compiler output
// Module: Lean.Data.JsonRpc
// Imports: Init Init.Control Init.System.IO Std.Data.RBTree Lean.Data.Json
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
lean_object* l_Lean_JsonRpc_instToJsonMessage_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__3;
lean_object* l_Lean_JsonRpc_instToStringRequestID(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__15;
lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___boxed(lean_object*);
lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object*);
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16_(lean_object*, lean_object*);
extern lean_object* l_Char_quote___closed__1;
lean_object* l_Lean_JsonRpc_instCoeStringRequestID(lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___boxed(lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs_match__1(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__10;
lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage___closed__1;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877____rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__18;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631____rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__14;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__30;
lean_object* l_Lean_JsonRpc_instCoeResponseErrorMessage(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753__match__1(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__6;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__5;
lean_object* l_Lean_JsonRpc_instCoeNotificationMessage___rarg(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130____boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instInhabitedRequestID;
lean_object* l_Lean_JsonRpc_instBEqErrorCode___closed__1;
lean_object* l_Lean_Json_toStructured_x3f___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs_match__2(lean_object*);
lean_object* l_Lean_JsonRpc_instBEqResponseError___rarg(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__34;
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1(lean_object*);
lean_object* l_IO_FS_Stream_writeResponse___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__1;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753__match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__2;
lean_object* l_IO_FS_Stream_readResponseAs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16__match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__7;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753____rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494__match__1(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instInhabitedResponse___rarg(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonMessage(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__23;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__11;
lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__10;
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__3;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__5;
lean_object* l_Lean_JsonRpc_instFromJsonNotification_match__1(lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__13;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__41;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__6;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753_(lean_object*);
lean_object* l_Lean_JsonRpc_instToStringRequestID_match__1(lean_object*);
lean_object* l_Lean_JsonRpc_instBEqRequestID;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130__match__1___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instBEqErrorCode;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631__match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__21;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__38;
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instInhabitedNotification___rarg(lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494__match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__7;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__29;
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130_(uint8_t, uint8_t);
lean_object* l_Lean_JsonRpc_instBEqResponse___rarg(lean_object*);
lean_object* l_IO_FS_Stream_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__3;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__25;
lean_object* l_Lean_JsonRpc_instCoeResponseMessage___rarg(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instDecidableLt___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___closed__3;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877__match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494____rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__39;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__35;
lean_object* l_Lean_JsonRpc_instFromJsonMessage___boxed(lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__7;
lean_object* l_IO_FS_Stream_readRequestAs___closed__5;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__1;
lean_object* l_Lean_JsonRpc_instInhabitedResponseError___closed__1;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__31;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__7;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeMessage(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16____boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__11;
lean_object* l_IO_FS_Stream_readJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instLTRequestID;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeResponseErrorWithData___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__8;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__19;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
lean_object* l_IO_FS_Stream_readResponseAs___closed__2;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__4;
lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonMessage_match__1(lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__10;
extern lean_object* l_Lean_nullKind___closed__1;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__2;
lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
uint8_t l___private_Lean_Data_Json_Basic_0__Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_7_(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readResponseAs___closed__1;
lean_object* l_Lean_JsonRpc_instBEqNotification___rarg(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
lean_object* l_Lean_JsonRpc_instToJsonRequestID(lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonMessage_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs___closed__1;
lean_object* l_IO_FS_Stream_readNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494_(lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage_match__1(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instCoeNotificationMessage(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__17;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877__match__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readResponseAs_match__1(lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__9;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__27;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp;
lean_object* l_Lean_JsonRpc_instCoeRequestMessage___rarg(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonMessage_match__1(lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16__match__1(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__12;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__10;
lean_object* l_Lean_JsonRpc_instFromJsonRequestID_match__1(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__43;
lean_object* l_IO_FS_Stream_writeResponseError(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130__match__1(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instCoeResponseMessage(lean_object*);
lean_object* l_Lean_JsonRpc_instToStringRequestID_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__6;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
extern lean_object* l_Int_instInhabitedInt___closed__1;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__11;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt_match__1(lean_object*);
lean_object* l_Lean_JsonRpc_instCoeRequestMessage(lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__6;
lean_object* lean_nat_abs(lean_object*);
uint8_t l_Lean_JsonNumber_lt(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___closed__2;
lean_object* l_IO_FS_Stream_readResponseAs___closed__3;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__3;
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__8;
lean_object* l_Lean_JsonRpc_instInhabitedRequest___rarg(lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonMessage(lean_object*);
lean_object* l_IO_FS_Stream_writeNotification(lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___closed__1;
lean_object* l_Lean_JsonRpc_instToStringRequestID___closed__1;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__33;
lean_object* l_Lean_JsonRpc_ResponseError_data_x3f___default(lean_object*);
lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode(lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___closed__4;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__11;
lean_object* l_Lean_JsonRpc_instCoeResponseErrorMessage___rarg(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877_(lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631_(lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__4;
lean_object* l_Lean_JsonRpc_instFromJsonRequestID_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__1;
lean_object* l_Lean_JsonRpc_instToJsonMessage___boxed(lean_object*);
uint8_t l_Lean_JsonRpc_instInhabitedErrorCode;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__5;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeRequest(lean_object*);
lean_object* l_IO_FS_Stream_writeJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instBEqRequest___rarg(lean_object*);
lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object*);
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631__match__1(lean_object*, lean_object*);
uint8_t l_Lean_JsonRpc_instDecidableLt(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readResponseAs___closed__4;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__1;
lean_object* l_Lean_JsonRpc_instFromJsonRequestID___boxed(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__13;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__26;
lean_object* l_Lean_JsonRpc_instToJsonRequestID___boxed(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
lean_object* l_IO_FS_Stream_writeResponse(lean_object*);
lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__42;
lean_object* l_Lean_JsonRpc_instFromJsonNotification_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__9;
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_object* l_Lean_JsonRpc_instToJsonErrorCode(uint8_t);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__37;
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__8;
lean_object* l_Lean_JsonRpc_instFromJsonRequestID(lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__22;
lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__2;
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instBEqRequestID___closed__1;
lean_object* l_IO_FS_Stream_writeRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__4;
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instToJsonErrorCode_match__1(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__9;
lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object*);
lean_object* l_IO_FS_Stream_readMessage___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_711____rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_JsonRpc_instInhabitedRequestID___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16__match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_6, x_1, x_2);
return x_10;
}
}
case 1:
{
lean_dec(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_apply_2(x_6, x_1, x_2);
return x_14;
}
}
default: 
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_5, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_5);
x_17 = lean_apply_2(x_6, x_1, x_2);
return x_17;
}
}
}
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16__match__1___rarg), 6, 0);
return x_2;
}
}
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16_(lean_object* x_1, lean_object* x_2) {
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
x_9 = l___private_Lean_Data_Json_Basic_0__Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_7_(x_7, x_8);
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
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqRequestID___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instBEqRequestID___closed__1;
return x_1;
}
}
lean_object* l_Lean_JsonRpc_instToStringRequestID_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
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
lean_object* l_Lean_JsonRpc_instToStringRequestID_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToStringRequestID_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToStringRequestID___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"s\"");
return x_1;
}
}
lean_object* l_Lean_JsonRpc_instToStringRequestID(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = l_Lean_JsonRpc_instToStringRequestID___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_JsonNumber_toString(x_3);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l_Lean_nullKind___closed__1;
return x_5;
}
}
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
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130__match__1___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_box(x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_3, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_3);
x_18 = lean_box(x_1);
x_19 = lean_box(x_2);
x_20 = lean_apply_2(x_14, x_18, x_19);
return x_20;
}
}
case 1:
{
lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_21 = lean_box(x_2);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = lean_apply_1(x_4, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_4);
x_24 = lean_box(x_1);
x_25 = lean_box(x_2);
x_26 = lean_apply_2(x_14, x_24, x_25);
return x_26;
}
}
case 2:
{
lean_object* x_27; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_box(x_2);
if (lean_obj_tag(x_27) == 2)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
x_28 = lean_box(0);
x_29 = lean_apply_1(x_5, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_5);
x_30 = lean_box(x_1);
x_31 = lean_box(x_2);
x_32 = lean_apply_2(x_14, x_30, x_31);
return x_32;
}
}
case 3:
{
lean_object* x_33; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_box(x_2);
if (lean_obj_tag(x_33) == 3)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_14);
x_34 = lean_box(0);
x_35 = lean_apply_1(x_6, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_6);
x_36 = lean_box(x_1);
x_37 = lean_box(x_2);
x_38 = lean_apply_2(x_14, x_36, x_37);
return x_38;
}
}
case 4:
{
lean_object* x_39; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = lean_box(x_2);
if (lean_obj_tag(x_39) == 4)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_14);
x_40 = lean_box(0);
x_41 = lean_apply_1(x_7, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_7);
x_42 = lean_box(x_1);
x_43 = lean_box(x_2);
x_44 = lean_apply_2(x_14, x_42, x_43);
return x_44;
}
}
case 5:
{
lean_object* x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = lean_box(x_2);
if (lean_obj_tag(x_45) == 5)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_14);
x_46 = lean_box(0);
x_47 = lean_apply_1(x_8, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
lean_dec(x_8);
x_48 = lean_box(x_1);
x_49 = lean_box(x_2);
x_50 = lean_apply_2(x_14, x_48, x_49);
return x_50;
}
}
case 6:
{
lean_object* x_51; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = lean_box(x_2);
if (lean_obj_tag(x_51) == 6)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_14);
x_52 = lean_box(0);
x_53 = lean_apply_1(x_9, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_9);
x_54 = lean_box(x_1);
x_55 = lean_box(x_2);
x_56 = lean_apply_2(x_14, x_54, x_55);
return x_56;
}
}
case 7:
{
lean_object* x_57; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = lean_box(x_2);
if (lean_obj_tag(x_57) == 7)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_14);
x_58 = lean_box(0);
x_59 = lean_apply_1(x_10, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_57);
lean_dec(x_10);
x_60 = lean_box(x_1);
x_61 = lean_box(x_2);
x_62 = lean_apply_2(x_14, x_60, x_61);
return x_62;
}
}
case 8:
{
lean_object* x_63; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_63 = lean_box(x_2);
if (lean_obj_tag(x_63) == 8)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_14);
x_64 = lean_box(0);
x_65 = lean_apply_1(x_11, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
lean_dec(x_11);
x_66 = lean_box(x_1);
x_67 = lean_box(x_2);
x_68 = lean_apply_2(x_14, x_66, x_67);
return x_68;
}
}
case 9:
{
lean_object* x_69; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = lean_box(x_2);
if (lean_obj_tag(x_69) == 9)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_14);
x_70 = lean_box(0);
x_71 = lean_apply_1(x_12, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_69);
lean_dec(x_12);
x_72 = lean_box(x_1);
x_73 = lean_box(x_2);
x_74 = lean_apply_2(x_14, x_72, x_73);
return x_74;
}
}
default: 
{
lean_object* x_75; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = lean_box(x_2);
if (lean_obj_tag(x_75) == 10)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_14);
x_76 = lean_box(0);
x_77 = lean_apply_1(x_13, x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_75);
lean_dec(x_13);
x_78 = lean_box(x_1);
x_79 = lean_box(x_2);
x_80 = lean_apply_2(x_14, x_78, x_79);
return x_80;
}
}
}
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130__match__1___rarg___boxed), 14, 0);
return x_2;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130__match__1___rarg(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
lean_object* x_6; 
x_6 = lean_box(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
case 2:
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
}
case 3:
{
lean_object* x_12; 
x_12 = lean_box(x_2);
if (lean_obj_tag(x_12) == 3)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_12);
x_14 = 0;
return x_14;
}
}
case 4:
{
lean_object* x_15; 
x_15 = lean_box(x_2);
if (lean_obj_tag(x_15) == 4)
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_15);
x_17 = 0;
return x_17;
}
}
case 5:
{
lean_object* x_18; 
x_18 = lean_box(x_2);
if (lean_obj_tag(x_18) == 5)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_18);
x_20 = 0;
return x_20;
}
}
case 6:
{
lean_object* x_21; 
x_21 = lean_box(x_2);
if (lean_obj_tag(x_21) == 6)
{
uint8_t x_22; 
x_22 = 1;
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_21);
x_23 = 0;
return x_23;
}
}
case 7:
{
lean_object* x_24; 
x_24 = lean_box(x_2);
if (lean_obj_tag(x_24) == 7)
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_24);
x_26 = 0;
return x_26;
}
}
case 8:
{
lean_object* x_27; 
x_27 = lean_box(x_2);
if (lean_obj_tag(x_27) == 8)
{
uint8_t x_28; 
x_28 = 1;
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_27);
x_29 = 0;
return x_29;
}
}
case 9:
{
lean_object* x_30; 
x_30 = lean_box(x_2);
if (lean_obj_tag(x_30) == 9)
{
uint8_t x_31; 
x_31 = 1;
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_30);
x_32 = 0;
return x_32;
}
}
default: 
{
lean_object* x_33; 
x_33 = lean_box(x_2);
if (lean_obj_tag(x_33) == 10)
{
uint8_t x_34; 
x_34 = 1;
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_33);
x_35 = 0;
return x_35;
}
}
}
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqErrorCode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqErrorCode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instBEqErrorCode___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32799u);
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32000u);
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(31999u);
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32098u);
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32599u);
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32699u);
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Int_instInhabitedInt___closed__1;
x_19 = lean_int_dec_lt(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_apply_1(x_13, x_1);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_nat_abs(x_16);
lean_dec(x_16);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(32699u);
x_25 = lean_nat_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_2);
x_26 = lean_unsigned_to_nat(32599u);
x_27 = lean_nat_dec_eq(x_23, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_3);
x_28 = lean_unsigned_to_nat(32600u);
x_29 = lean_nat_dec_eq(x_23, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_4);
x_30 = lean_unsigned_to_nat(32601u);
x_31 = lean_nat_dec_eq(x_23, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_5);
x_32 = lean_unsigned_to_nat(32602u);
x_33 = lean_nat_dec_eq(x_23, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_6);
x_34 = lean_unsigned_to_nat(32098u);
x_35 = lean_nat_dec_eq(x_23, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_7);
x_36 = lean_unsigned_to_nat(31999u);
x_37 = lean_nat_dec_eq(x_23, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
lean_dec(x_8);
x_38 = lean_unsigned_to_nat(32001u);
x_39 = lean_nat_dec_eq(x_23, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_9);
x_40 = lean_unsigned_to_nat(32000u);
x_41 = lean_nat_dec_eq(x_23, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_10);
x_42 = lean_unsigned_to_nat(32799u);
x_43 = lean_nat_dec_eq(x_23, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_11);
x_44 = lean_unsigned_to_nat(32800u);
x_45 = lean_nat_dec_eq(x_23, x_44);
lean_dec(x_23);
if (x_45 == 0)
{
lean_object* x_46; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_12);
x_46 = lean_apply_1(x_13, x_1);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_1);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_1, 0);
lean_dec(x_48);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_eq(x_17, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_12);
x_51 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__1;
lean_ctor_set(x_14, 0, x_51);
x_52 = lean_apply_1(x_13, x_1);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_free_object(x_1);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_53 = lean_box(0);
x_54 = lean_apply_1(x_12, x_53);
return x_54;
}
}
else
{
lean_object* x_55; uint8_t x_56; 
lean_dec(x_1);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_dec_eq(x_17, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_12);
x_57 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__1;
lean_ctor_set(x_14, 0, x_57);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_14);
x_59 = lean_apply_1(x_13, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_60 = lean_box(0);
x_61 = lean_apply_1(x_12, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_23);
lean_dec(x_12);
x_62 = !lean_is_exclusive(x_1);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_1, 0);
lean_dec(x_63);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_nat_dec_eq(x_17, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_11);
x_66 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__2;
lean_ctor_set(x_14, 0, x_66);
x_67 = lean_apply_1(x_13, x_1);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_free_object(x_1);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_68 = lean_box(0);
x_69 = lean_apply_1(x_11, x_68);
return x_69;
}
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_dec(x_1);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_17, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_11);
x_72 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__2;
lean_ctor_set(x_14, 0, x_72);
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_14);
x_74 = lean_apply_1(x_13, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_75 = lean_box(0);
x_76 = lean_apply_1(x_11, x_75);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
x_77 = !lean_is_exclusive(x_1);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_1, 0);
lean_dec(x_78);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_eq(x_17, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_10);
x_81 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__3;
lean_ctor_set(x_14, 0, x_81);
x_82 = lean_apply_1(x_13, x_1);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_free_object(x_1);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_83 = lean_box(0);
x_84 = lean_apply_1(x_10, x_83);
return x_84;
}
}
else
{
lean_object* x_85; uint8_t x_86; 
lean_dec(x_1);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_eq(x_17, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_10);
x_87 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__3;
lean_ctor_set(x_14, 0, x_87);
x_88 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_88, 0, x_14);
x_89 = lean_apply_1(x_13, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_90 = lean_box(0);
x_91 = lean_apply_1(x_10, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_92 = !lean_is_exclusive(x_1);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_1, 0);
lean_dec(x_93);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_dec_eq(x_17, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_9);
x_96 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__4;
lean_ctor_set(x_14, 0, x_96);
x_97 = lean_apply_1(x_13, x_1);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_free_object(x_1);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_98 = lean_box(0);
x_99 = lean_apply_1(x_9, x_98);
return x_99;
}
}
else
{
lean_object* x_100; uint8_t x_101; 
lean_dec(x_1);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_nat_dec_eq(x_17, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_9);
x_102 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__4;
lean_ctor_set(x_14, 0, x_102);
x_103 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_103, 0, x_14);
x_104 = lean_apply_1(x_13, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_105 = lean_box(0);
x_106 = lean_apply_1(x_9, x_105);
return x_106;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_107 = !lean_is_exclusive(x_1);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_1, 0);
lean_dec(x_108);
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_dec_eq(x_17, x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_8);
x_111 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__5;
lean_ctor_set(x_14, 0, x_111);
x_112 = lean_apply_1(x_13, x_1);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_free_object(x_1);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_113 = lean_box(0);
x_114 = lean_apply_1(x_8, x_113);
return x_114;
}
}
else
{
lean_object* x_115; uint8_t x_116; 
lean_dec(x_1);
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_nat_dec_eq(x_17, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_8);
x_117 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__5;
lean_ctor_set(x_14, 0, x_117);
x_118 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_118, 0, x_14);
x_119 = lean_apply_1(x_13, x_118);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_120 = lean_box(0);
x_121 = lean_apply_1(x_8, x_120);
return x_121;
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_122 = !lean_is_exclusive(x_1);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_1, 0);
lean_dec(x_123);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_nat_dec_eq(x_17, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_7);
x_126 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__6;
lean_ctor_set(x_14, 0, x_126);
x_127 = lean_apply_1(x_13, x_1);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_free_object(x_1);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_128 = lean_box(0);
x_129 = lean_apply_1(x_7, x_128);
return x_129;
}
}
else
{
lean_object* x_130; uint8_t x_131; 
lean_dec(x_1);
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_nat_dec_eq(x_17, x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_7);
x_132 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__6;
lean_ctor_set(x_14, 0, x_132);
x_133 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_133, 0, x_14);
x_134 = lean_apply_1(x_13, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_135 = lean_box(0);
x_136 = lean_apply_1(x_7, x_135);
return x_136;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_137 = !lean_is_exclusive(x_1);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_1, 0);
lean_dec(x_138);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_nat_dec_eq(x_17, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_6);
x_141 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__7;
lean_ctor_set(x_14, 0, x_141);
x_142 = lean_apply_1(x_13, x_1);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_free_object(x_1);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_143 = lean_box(0);
x_144 = lean_apply_1(x_6, x_143);
return x_144;
}
}
else
{
lean_object* x_145; uint8_t x_146; 
lean_dec(x_1);
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_nat_dec_eq(x_17, x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_6);
x_147 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__7;
lean_ctor_set(x_14, 0, x_147);
x_148 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_148, 0, x_14);
x_149 = lean_apply_1(x_13, x_148);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_150 = lean_box(0);
x_151 = lean_apply_1(x_6, x_150);
return x_151;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_152 = !lean_is_exclusive(x_1);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_1, 0);
lean_dec(x_153);
x_154 = lean_unsigned_to_nat(0u);
x_155 = lean_nat_dec_eq(x_17, x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_5);
x_156 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__8;
lean_ctor_set(x_14, 0, x_156);
x_157 = lean_apply_1(x_13, x_1);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_free_object(x_1);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_158 = lean_box(0);
x_159 = lean_apply_1(x_5, x_158);
return x_159;
}
}
else
{
lean_object* x_160; uint8_t x_161; 
lean_dec(x_1);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_nat_dec_eq(x_17, x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_5);
x_162 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__8;
lean_ctor_set(x_14, 0, x_162);
x_163 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_163, 0, x_14);
x_164 = lean_apply_1(x_13, x_163);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_165 = lean_box(0);
x_166 = lean_apply_1(x_5, x_165);
return x_166;
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_167 = !lean_is_exclusive(x_1);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_1, 0);
lean_dec(x_168);
x_169 = lean_unsigned_to_nat(0u);
x_170 = lean_nat_dec_eq(x_17, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_4);
x_171 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__9;
lean_ctor_set(x_14, 0, x_171);
x_172 = lean_apply_1(x_13, x_1);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_free_object(x_1);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_173 = lean_box(0);
x_174 = lean_apply_1(x_4, x_173);
return x_174;
}
}
else
{
lean_object* x_175; uint8_t x_176; 
lean_dec(x_1);
x_175 = lean_unsigned_to_nat(0u);
x_176 = lean_nat_dec_eq(x_17, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_4);
x_177 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__9;
lean_ctor_set(x_14, 0, x_177);
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_14);
x_179 = lean_apply_1(x_13, x_178);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_180 = lean_box(0);
x_181 = lean_apply_1(x_4, x_180);
return x_181;
}
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_182 = !lean_is_exclusive(x_1);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_1, 0);
lean_dec(x_183);
x_184 = lean_unsigned_to_nat(0u);
x_185 = lean_nat_dec_eq(x_17, x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_3);
x_186 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__10;
lean_ctor_set(x_14, 0, x_186);
x_187 = lean_apply_1(x_13, x_1);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_free_object(x_1);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_188 = lean_box(0);
x_189 = lean_apply_1(x_3, x_188);
return x_189;
}
}
else
{
lean_object* x_190; uint8_t x_191; 
lean_dec(x_1);
x_190 = lean_unsigned_to_nat(0u);
x_191 = lean_nat_dec_eq(x_17, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_3);
x_192 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__10;
lean_ctor_set(x_14, 0, x_192);
x_193 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_193, 0, x_14);
x_194 = lean_apply_1(x_13, x_193);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_195 = lean_box(0);
x_196 = lean_apply_1(x_3, x_195);
return x_196;
}
}
}
}
else
{
uint8_t x_197; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_197 = !lean_is_exclusive(x_1);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_198 = lean_ctor_get(x_1, 0);
lean_dec(x_198);
x_199 = lean_unsigned_to_nat(0u);
x_200 = lean_nat_dec_eq(x_17, x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_2);
x_201 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__11;
lean_ctor_set(x_14, 0, x_201);
x_202 = lean_apply_1(x_13, x_1);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_free_object(x_1);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_203 = lean_box(0);
x_204 = lean_apply_1(x_2, x_203);
return x_204;
}
}
else
{
lean_object* x_205; uint8_t x_206; 
lean_dec(x_1);
x_205 = lean_unsigned_to_nat(0u);
x_206 = lean_nat_dec_eq(x_17, x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_2);
x_207 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__11;
lean_ctor_set(x_14, 0, x_207);
x_208 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_208, 0, x_14);
x_209 = lean_apply_1(x_13, x_208);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_13);
x_210 = lean_box(0);
x_211 = lean_apply_1(x_2, x_210);
return x_211;
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_212 = lean_ctor_get(x_14, 0);
x_213 = lean_ctor_get(x_14, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_14);
x_214 = l_Int_instInhabitedInt___closed__1;
x_215 = lean_int_dec_lt(x_212, x_214);
if (x_215 == 0)
{
lean_object* x_216; 
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_216 = lean_apply_1(x_13, x_1);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_nat_abs(x_212);
lean_dec(x_212);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_sub(x_217, x_218);
lean_dec(x_217);
x_220 = lean_unsigned_to_nat(32699u);
x_221 = lean_nat_dec_eq(x_219, x_220);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
lean_dec(x_2);
x_222 = lean_unsigned_to_nat(32599u);
x_223 = lean_nat_dec_eq(x_219, x_222);
if (x_223 == 0)
{
lean_object* x_224; uint8_t x_225; 
lean_dec(x_3);
x_224 = lean_unsigned_to_nat(32600u);
x_225 = lean_nat_dec_eq(x_219, x_224);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
lean_dec(x_4);
x_226 = lean_unsigned_to_nat(32601u);
x_227 = lean_nat_dec_eq(x_219, x_226);
if (x_227 == 0)
{
lean_object* x_228; uint8_t x_229; 
lean_dec(x_5);
x_228 = lean_unsigned_to_nat(32602u);
x_229 = lean_nat_dec_eq(x_219, x_228);
if (x_229 == 0)
{
lean_object* x_230; uint8_t x_231; 
lean_dec(x_6);
x_230 = lean_unsigned_to_nat(32098u);
x_231 = lean_nat_dec_eq(x_219, x_230);
if (x_231 == 0)
{
lean_object* x_232; uint8_t x_233; 
lean_dec(x_7);
x_232 = lean_unsigned_to_nat(31999u);
x_233 = lean_nat_dec_eq(x_219, x_232);
if (x_233 == 0)
{
lean_object* x_234; uint8_t x_235; 
lean_dec(x_8);
x_234 = lean_unsigned_to_nat(32001u);
x_235 = lean_nat_dec_eq(x_219, x_234);
if (x_235 == 0)
{
lean_object* x_236; uint8_t x_237; 
lean_dec(x_9);
x_236 = lean_unsigned_to_nat(32000u);
x_237 = lean_nat_dec_eq(x_219, x_236);
if (x_237 == 0)
{
lean_object* x_238; uint8_t x_239; 
lean_dec(x_10);
x_238 = lean_unsigned_to_nat(32799u);
x_239 = lean_nat_dec_eq(x_219, x_238);
if (x_239 == 0)
{
lean_object* x_240; uint8_t x_241; 
lean_dec(x_11);
x_240 = lean_unsigned_to_nat(32800u);
x_241 = lean_nat_dec_eq(x_219, x_240);
lean_dec(x_219);
if (x_241 == 0)
{
lean_object* x_242; 
lean_dec(x_213);
lean_dec(x_12);
x_242 = lean_apply_1(x_13, x_1);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_243 = x_1;
} else {
 lean_dec_ref(x_1);
 x_243 = lean_box(0);
}
x_244 = lean_unsigned_to_nat(0u);
x_245 = lean_nat_dec_eq(x_213, x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_12);
x_246 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__1;
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_213);
if (lean_is_scalar(x_243)) {
 x_248 = lean_alloc_ctor(2, 1, 0);
} else {
 x_248 = x_243;
}
lean_ctor_set(x_248, 0, x_247);
x_249 = lean_apply_1(x_13, x_248);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_243);
lean_dec(x_213);
lean_dec(x_13);
x_250 = lean_box(0);
x_251 = lean_apply_1(x_12, x_250);
return x_251;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; 
lean_dec(x_219);
lean_dec(x_12);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_252 = x_1;
} else {
 lean_dec_ref(x_1);
 x_252 = lean_box(0);
}
x_253 = lean_unsigned_to_nat(0u);
x_254 = lean_nat_dec_eq(x_213, x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_11);
x_255 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__2;
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_213);
if (lean_is_scalar(x_252)) {
 x_257 = lean_alloc_ctor(2, 1, 0);
} else {
 x_257 = x_252;
}
lean_ctor_set(x_257, 0, x_256);
x_258 = lean_apply_1(x_13, x_257);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_252);
lean_dec(x_213);
lean_dec(x_13);
x_259 = lean_box(0);
x_260 = lean_apply_1(x_11, x_259);
return x_260;
}
}
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; 
lean_dec(x_219);
lean_dec(x_12);
lean_dec(x_11);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_261 = x_1;
} else {
 lean_dec_ref(x_1);
 x_261 = lean_box(0);
}
x_262 = lean_unsigned_to_nat(0u);
x_263 = lean_nat_dec_eq(x_213, x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_10);
x_264 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__3;
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_213);
if (lean_is_scalar(x_261)) {
 x_266 = lean_alloc_ctor(2, 1, 0);
} else {
 x_266 = x_261;
}
lean_ctor_set(x_266, 0, x_265);
x_267 = lean_apply_1(x_13, x_266);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_261);
lean_dec(x_213);
lean_dec(x_13);
x_268 = lean_box(0);
x_269 = lean_apply_1(x_10, x_268);
return x_269;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
lean_dec(x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_270 = x_1;
} else {
 lean_dec_ref(x_1);
 x_270 = lean_box(0);
}
x_271 = lean_unsigned_to_nat(0u);
x_272 = lean_nat_dec_eq(x_213, x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_9);
x_273 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__4;
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_213);
if (lean_is_scalar(x_270)) {
 x_275 = lean_alloc_ctor(2, 1, 0);
} else {
 x_275 = x_270;
}
lean_ctor_set(x_275, 0, x_274);
x_276 = lean_apply_1(x_13, x_275);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_270);
lean_dec(x_213);
lean_dec(x_13);
x_277 = lean_box(0);
x_278 = lean_apply_1(x_9, x_277);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; uint8_t x_281; 
lean_dec(x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_279 = x_1;
} else {
 lean_dec_ref(x_1);
 x_279 = lean_box(0);
}
x_280 = lean_unsigned_to_nat(0u);
x_281 = lean_nat_dec_eq(x_213, x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_8);
x_282 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__5;
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_213);
if (lean_is_scalar(x_279)) {
 x_284 = lean_alloc_ctor(2, 1, 0);
} else {
 x_284 = x_279;
}
lean_ctor_set(x_284, 0, x_283);
x_285 = lean_apply_1(x_13, x_284);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_279);
lean_dec(x_213);
lean_dec(x_13);
x_286 = lean_box(0);
x_287 = lean_apply_1(x_8, x_286);
return x_287;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; 
lean_dec(x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_288 = x_1;
} else {
 lean_dec_ref(x_1);
 x_288 = lean_box(0);
}
x_289 = lean_unsigned_to_nat(0u);
x_290 = lean_nat_dec_eq(x_213, x_289);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_7);
x_291 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__6;
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_213);
if (lean_is_scalar(x_288)) {
 x_293 = lean_alloc_ctor(2, 1, 0);
} else {
 x_293 = x_288;
}
lean_ctor_set(x_293, 0, x_292);
x_294 = lean_apply_1(x_13, x_293);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_288);
lean_dec(x_213);
lean_dec(x_13);
x_295 = lean_box(0);
x_296 = lean_apply_1(x_7, x_295);
return x_296;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_dec(x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_297 = x_1;
} else {
 lean_dec_ref(x_1);
 x_297 = lean_box(0);
}
x_298 = lean_unsigned_to_nat(0u);
x_299 = lean_nat_dec_eq(x_213, x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_6);
x_300 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__7;
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_213);
if (lean_is_scalar(x_297)) {
 x_302 = lean_alloc_ctor(2, 1, 0);
} else {
 x_302 = x_297;
}
lean_ctor_set(x_302, 0, x_301);
x_303 = lean_apply_1(x_13, x_302);
return x_303;
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_297);
lean_dec(x_213);
lean_dec(x_13);
x_304 = lean_box(0);
x_305 = lean_apply_1(x_6, x_304);
return x_305;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; 
lean_dec(x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_306 = x_1;
} else {
 lean_dec_ref(x_1);
 x_306 = lean_box(0);
}
x_307 = lean_unsigned_to_nat(0u);
x_308 = lean_nat_dec_eq(x_213, x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_5);
x_309 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__8;
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_213);
if (lean_is_scalar(x_306)) {
 x_311 = lean_alloc_ctor(2, 1, 0);
} else {
 x_311 = x_306;
}
lean_ctor_set(x_311, 0, x_310);
x_312 = lean_apply_1(x_13, x_311);
return x_312;
}
else
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_306);
lean_dec(x_213);
lean_dec(x_13);
x_313 = lean_box(0);
x_314 = lean_apply_1(x_5, x_313);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; 
lean_dec(x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_315 = x_1;
} else {
 lean_dec_ref(x_1);
 x_315 = lean_box(0);
}
x_316 = lean_unsigned_to_nat(0u);
x_317 = lean_nat_dec_eq(x_213, x_316);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_4);
x_318 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__9;
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_213);
if (lean_is_scalar(x_315)) {
 x_320 = lean_alloc_ctor(2, 1, 0);
} else {
 x_320 = x_315;
}
lean_ctor_set(x_320, 0, x_319);
x_321 = lean_apply_1(x_13, x_320);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; 
lean_dec(x_315);
lean_dec(x_213);
lean_dec(x_13);
x_322 = lean_box(0);
x_323 = lean_apply_1(x_4, x_322);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; 
lean_dec(x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_324 = x_1;
} else {
 lean_dec_ref(x_1);
 x_324 = lean_box(0);
}
x_325 = lean_unsigned_to_nat(0u);
x_326 = lean_nat_dec_eq(x_213, x_325);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_3);
x_327 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__10;
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_213);
if (lean_is_scalar(x_324)) {
 x_329 = lean_alloc_ctor(2, 1, 0);
} else {
 x_329 = x_324;
}
lean_ctor_set(x_329, 0, x_328);
x_330 = lean_apply_1(x_13, x_329);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_324);
lean_dec(x_213);
lean_dec(x_13);
x_331 = lean_box(0);
x_332 = lean_apply_1(x_3, x_331);
return x_332;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; 
lean_dec(x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_333 = x_1;
} else {
 lean_dec_ref(x_1);
 x_333 = lean_box(0);
}
x_334 = lean_unsigned_to_nat(0u);
x_335 = lean_nat_dec_eq(x_213, x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_2);
x_336 = l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__11;
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_213);
if (lean_is_scalar(x_333)) {
 x_338 = lean_alloc_ctor(2, 1, 0);
} else {
 x_338 = x_333;
}
lean_ctor_set(x_338, 0, x_337);
x_339 = lean_apply_1(x_13, x_338);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_333);
lean_dec(x_213);
lean_dec(x_13);
x_340 = lean_box(0);
x_341 = lean_apply_1(x_2, x_340);
return x_341;
}
}
}
}
}
else
{
lean_object* x_342; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_342 = lean_apply_1(x_13, x_1);
return x_342;
}
}
}
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg), 13, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__1() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__2() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__3() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__4() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__5() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__6() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__7() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__8() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__9() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__10() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__11() {
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
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Int_instInhabitedInt___closed__1;
x_6 = lean_int_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_nat_abs(x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(32699u);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(32599u);
x_14 = lean_nat_dec_eq(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(32600u);
x_16 = lean_nat_dec_eq(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(32601u);
x_18 = lean_nat_dec_eq(x_10, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(32602u);
x_20 = lean_nat_dec_eq(x_10, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(32098u);
x_22 = lean_nat_dec_eq(x_10, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_unsigned_to_nat(31999u);
x_24 = lean_nat_dec_eq(x_10, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(32001u);
x_26 = lean_nat_dec_eq(x_10, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(32000u);
x_28 = lean_nat_dec_eq(x_10, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(32799u);
x_30 = lean_nat_dec_eq(x_10, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(32800u);
x_32 = lean_nat_dec_eq(x_10, x_31);
lean_dec(x_10);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_4, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_box(0);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__1;
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
lean_dec(x_10);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_4, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_box(0);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_41;
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_10);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_eq(x_4, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_box(0);
return x_44;
}
else
{
lean_object* x_45; 
x_45 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__3;
return x_45;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_10);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_4, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_box(0);
return x_48;
}
else
{
lean_object* x_49; 
x_49 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__4;
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_10);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_eq(x_4, x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__5;
return x_53;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_10);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_4, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
return x_56;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__6;
return x_57;
}
}
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_10);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_4, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_box(0);
return x_60;
}
else
{
lean_object* x_61; 
x_61 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__7;
return x_61;
}
}
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_dec(x_10);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_4, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_box(0);
return x_64;
}
else
{
lean_object* x_65; 
x_65 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__8;
return x_65;
}
}
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_10);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_4, x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_box(0);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__9;
return x_69;
}
}
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_dec(x_10);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_4, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_box(0);
return x_72;
}
else
{
lean_object* x_73; 
x_73 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__10;
return x_73;
}
}
}
else
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_10);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_eq(x_4, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
return x_76;
}
else
{
lean_object* x_77; 
x_77 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__11;
return x_77;
}
}
}
}
else
{
lean_object* x_78; 
x_78 = lean_box(0);
return x_78;
}
}
}
lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instFromJsonErrorCode(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instToJsonErrorCode_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_2, x_13);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_3, x_15);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = lean_apply_1(x_4, x_17);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_apply_1(x_5, x_19);
return x_20;
}
case 4:
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_apply_1(x_6, x_21);
return x_22;
}
case 5:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_apply_1(x_7, x_23);
return x_24;
}
case 6:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_apply_1(x_8, x_25);
return x_26;
}
case 7:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_apply_1(x_9, x_27);
return x_28;
}
case 8:
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_apply_1(x_10, x_29);
return x_30;
}
case 9:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = lean_apply_1(x_11, x_31);
return x_32;
}
default: 
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_apply_1(x_12, x_33);
return x_34;
}
}
}
}
lean_object* l_Lean_JsonRpc_instToJsonErrorCode_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonErrorCode_match__1___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instToJsonErrorCode_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_JsonRpc_instToJsonErrorCode_match__1___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__1;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__5;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__9;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__10;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__13;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__14;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__17;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__18;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32099u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__21;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__22;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__23;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__25;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__26;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__27;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__29;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__30;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__31;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__33;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__34;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__35;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__37;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__38;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__39;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__41;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__42;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__43;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instToJsonErrorCode(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
return x_11;
}
default: 
{
lean_object* x_12; 
x_12 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
return x_12;
}
}
}
}
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_JsonRpc_instToJsonErrorCode(x_2);
return x_3;
}
}
lean_object* l_Lean_JsonRpc_instInhabitedRequest___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_3 = l_Lean_instInhabitedParserDescr___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instInhabitedRequest___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494__match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_6(x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494__match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494__match__1___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494__match__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16_(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = 0;
x_12 = lean_box(x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_string_dec_eq(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_14 = 0;
x_15 = lean_box(x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_apply_2(x_1, x_6, x_9);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494____rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instBEqRequest___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_494____rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instCoeRequestMessage___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_5);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
lean_object* l_Lean_JsonRpc_instCoeRequestMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeRequestMessage___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instInhabitedNotification___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instInhabitedNotification___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631__match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_4(x_3, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631__match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631__match__1___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631__match__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_string_dec_eq(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_apply_2(x_1, x_5, x_7);
return x_11;
}
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631____rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instBEqNotification___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_631____rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instCoeNotificationMessage___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_JsonRpc_instCoeNotificationMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeNotificationMessage___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instInhabitedResponse___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instInhabitedResponse___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753__match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_4(x_3, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753__match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753__match__1___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753__match__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16_(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_apply_2(x_1, x_5, x_7);
return x_11;
}
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753____rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instBEqResponse___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_753____rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instCoeResponseMessage___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_JsonRpc_instCoeResponseMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeResponseMessage___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_ResponseError_data_x3f___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_3 = 0;
x_4 = l_Lean_instInhabitedParserDescr___closed__1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
return x_5;
}
}
lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instInhabitedResponseError___closed__1;
return x_2;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877__match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_box(x_6);
x_14 = lean_box(x_10);
x_15 = lean_apply_8(x_3, x_5, x_13, x_7, x_8, x_9, x_14, x_11, x_12);
return x_15;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877__match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877__match__1___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877__match__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16_(x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = 0;
x_14 = lean_box(x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_130_(x_5, x_9);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = 0;
x_17 = lean_box(x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_string_dec_eq(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_19 = 0;
x_20 = lean_box(x_19);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_711____rarg(x_1, x_7, x_11);
return x_21;
}
}
}
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877____rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instBEqResponseError___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_877____rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instCoeResponseErrorMessage___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_apply_1(x_1, x_13);
lean_ctor_set(x_3, 0, x_14);
x_15 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_apply_1(x_1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_10);
return x_19;
}
}
}
}
lean_object* l_Lean_JsonRpc_instCoeResponseErrorMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeResponseErrorMessage___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instCoeStringRequestID(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_2(x_3, x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_apply_2(x_8, x_1, x_2);
return x_12;
}
}
case 1:
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_apply_2(x_7, x_13, x_14);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_2(x_4, x_16, x_17);
return x_18;
}
default: 
{
lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_4);
x_19 = lean_apply_2(x_8, x_1, x_2);
return x_19;
}
}
}
default: 
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_5);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_apply_1(x_6, x_20);
return x_21;
}
case 1:
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_6);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_apply_1(x_5, x_22);
return x_23;
}
default: 
{
lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_apply_2(x_8, x_2, x_2);
return x_24;
}
}
}
}
}
}
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt_match__1___rarg), 8, 0);
return x_2;
}
}
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_string_dec_lt(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_2);
lean_dec(x_1);
x_7 = 1;
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_JsonNumber_lt(x_8, x_9);
return x_10;
}
default: 
{
uint8_t x_11; 
lean_dec(x_1);
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
lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp() {
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
x_1 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp;
return x_1;
}
}
uint8_t l_Lean_JsonRpc_instDecidableLt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_JsonRpc_instDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonRpc_instDecidableLt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_JsonRpc_instFromJsonRequestID_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_1(x_4, x_1);
return x_9;
}
}
}
}
lean_object* l_Lean_JsonRpc_instFromJsonRequestID_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonRequestID_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instFromJsonRequestID(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 3:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
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
lean_object* l_Lean_JsonRpc_instFromJsonRequestID___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instFromJsonRequestID(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instToJsonRequestID(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
}
lean_object* l_Lean_JsonRpc_instToJsonRequestID___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instToJsonRequestID(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instToJsonMessage_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_2, x_6, x_7, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_3, x_10, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_4, x_13, x_14);
return x_15;
}
default: 
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_box(x_17);
x_21 = lean_apply_4(x_5, x_16, x_20, x_18, x_19);
return x_21;
}
}
}
}
lean_object* l_Lean_JsonRpc_instToJsonMessage_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instToJsonMessage_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
}
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("2.0");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("jsonrpc");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonMessage___closed__3;
x_2 = l_Lean_JsonRpc_instToJsonMessage___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("method");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("params");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("id");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("message");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("data");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("code");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("error");
return x_1;
}
}
lean_object* l_Lean_JsonRpc_instToJsonMessage(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_11 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_10, x_4);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
x_17 = l_List_append___rarg(x_16, x_11);
x_18 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Json_mkObj(x_19);
return x_20;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_9);
x_26 = l_List_append___rarg(x_25, x_11);
x_27 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Json_mkObj(x_28);
return x_29;
}
default: 
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
x_32 = l_List_append___rarg(x_31, x_11);
x_33 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Json_mkObj(x_34);
return x_35;
}
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_42 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_41, x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Json_mkObj(x_45);
return x_46;
}
case 2:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_1, 1);
x_49 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_inc(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
switch (lean_obj_tag(x_47)) {
case 0:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
x_58 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Json_mkObj(x_59);
return x_60;
}
case 1:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_52);
x_66 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Json_mkObj(x_67);
return x_68;
}
default: 
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_52);
x_71 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Json_mkObj(x_72);
return x_73;
}
}
}
default: 
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_74 = lean_ctor_get(x_1, 0);
x_75 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_76 = lean_ctor_get(x_1, 1);
x_77 = lean_ctor_get(x_1, 2);
lean_inc(x_76);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_76);
x_79 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_84 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_83, x_77);
switch (lean_obj_tag(x_74)) {
case 0:
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_74, 0);
lean_inc(x_114);
x_115 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_85 = x_115;
goto block_113;
}
case 1:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_74, 0);
lean_inc(x_116);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_85 = x_117;
goto block_113;
}
default: 
{
lean_object* x_118; 
x_118 = lean_box(0);
x_85 = x_118;
goto block_113;
}
}
block_113:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
switch (x_75) {
case 0:
{
lean_object* x_102; 
x_102 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_88 = x_102;
goto block_101;
}
case 1:
{
lean_object* x_103; 
x_103 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_88 = x_103;
goto block_101;
}
case 2:
{
lean_object* x_104; 
x_104 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_88 = x_104;
goto block_101;
}
case 3:
{
lean_object* x_105; 
x_105 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_88 = x_105;
goto block_101;
}
case 4:
{
lean_object* x_106; 
x_106 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_88 = x_106;
goto block_101;
}
case 5:
{
lean_object* x_107; 
x_107 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_88 = x_107;
goto block_101;
}
case 6:
{
lean_object* x_108; 
x_108 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_88 = x_108;
goto block_101;
}
case 7:
{
lean_object* x_109; 
x_109 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_88 = x_109;
goto block_101;
}
case 8:
{
lean_object* x_110; 
x_110 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_88 = x_110;
goto block_101;
}
case 9:
{
lean_object* x_111; 
x_111 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_88 = x_111;
goto block_101;
}
default: 
{
lean_object* x_112; 
x_112 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_88 = x_112;
goto block_101;
}
}
block_101:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_89 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_82);
x_92 = l_List_append___rarg(x_91, x_84);
x_93 = l_Lean_Json_mkObj(x_92);
x_94 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_81);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Lean_Json_mkObj(x_99);
return x_100;
}
}
}
}
}
}
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_JsonRpc_instToJsonMessage___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instToJsonMessage(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instFromJsonMessage_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_JsonRpc_instFromJsonMessage_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonMessage_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Int_instInhabitedInt___closed__1;
x_8 = lean_int_dec_lt(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_nat_abs(x_5);
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(32699u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(32599u);
x_16 = lean_nat_dec_eq(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(32600u);
x_18 = lean_nat_dec_eq(x_12, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(32601u);
x_20 = lean_nat_dec_eq(x_12, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(32602u);
x_22 = lean_nat_dec_eq(x_12, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_unsigned_to_nat(32098u);
x_24 = lean_nat_dec_eq(x_12, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(31999u);
x_26 = lean_nat_dec_eq(x_12, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(32001u);
x_28 = lean_nat_dec_eq(x_12, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(32000u);
x_30 = lean_nat_dec_eq(x_12, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(32799u);
x_32 = lean_nat_dec_eq(x_12, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(32800u);
x_34 = lean_nat_dec_eq(x_12, x_33);
lean_dec(x_12);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_6);
x_35 = lean_box(0);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_6, x_36);
lean_dec(x_6);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__1;
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_12);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_6, x_40);
lean_dec(x_6);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_43;
}
}
}
else
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_12);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_6, x_44);
lean_dec(x_6);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_box(0);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__3;
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_12);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_6, x_48);
lean_dec(x_6);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
return x_50;
}
else
{
lean_object* x_51; 
x_51 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__4;
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_12);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_eq(x_6, x_52);
lean_dec(x_6);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
return x_54;
}
else
{
lean_object* x_55; 
x_55 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__5;
return x_55;
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_12);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_eq(x_6, x_56);
lean_dec(x_6);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_box(0);
return x_58;
}
else
{
lean_object* x_59; 
x_59 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__6;
return x_59;
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
lean_dec(x_12);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_eq(x_6, x_60);
lean_dec(x_6);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_box(0);
return x_62;
}
else
{
lean_object* x_63; 
x_63 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__7;
return x_63;
}
}
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_12);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_nat_dec_eq(x_6, x_64);
lean_dec(x_6);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_box(0);
return x_66;
}
else
{
lean_object* x_67; 
x_67 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__8;
return x_67;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
lean_dec(x_12);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_eq(x_6, x_68);
lean_dec(x_6);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_box(0);
return x_70;
}
else
{
lean_object* x_71; 
x_71 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__9;
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_12);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_eq(x_6, x_72);
lean_dec(x_6);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_box(0);
return x_74;
}
else
{
lean_object* x_75; 
x_75 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__10;
return x_75;
}
}
}
else
{
lean_object* x_76; uint8_t x_77; 
lean_dec(x_12);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_eq(x_6, x_76);
lean_dec(x_6);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_box(0);
return x_78;
}
else
{
lean_object* x_79; 
x_79 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__11;
return x_79;
}
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_3);
x_80 = lean_box(0);
return x_80;
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 4:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
}
}
}
lean_object* l_Lean_JsonRpc_instFromJsonMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_instToJsonMessage___closed__3;
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
if (lean_obj_tag(x_5) == 3)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_12 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_1, x_11);
x_13 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_14 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_1, x_13);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_94; 
x_94 = lean_box(0);
x_15 = x_94;
goto block_93;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_95; 
x_95 = lean_box(0);
x_15 = x_95;
goto block_93;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_12, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_14, 0);
lean_inc(x_97);
x_98 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_99 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_98);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_97);
lean_ctor_set(x_100, 2, x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_15 = x_101;
goto block_93;
}
}
block_93:
{
lean_object* x_16; 
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
x_16 = x_82;
goto block_81;
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_14);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_14, 0);
x_85 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_86 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_14, 0, x_87);
x_16 = x_14;
goto block_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_14, 0);
lean_inc(x_88);
lean_dec(x_14);
x_89 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_90 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_16 = x_92;
goto block_81;
}
}
block_81:
{
lean_object* x_17; lean_object* x_28; lean_object* x_40; lean_object* x_41; 
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_70; 
lean_dec(x_6);
x_70 = lean_box(0);
x_17 = x_70;
goto block_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_12, 0);
lean_inc(x_71);
lean_dec(x_12);
x_72 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_73 = l_Lean_Json_getObjVal_x3f(x_1, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_box(0);
x_40 = x_74;
x_41 = x_71;
goto block_69;
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_71);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_73, 0, x_77);
x_40 = x_73;
x_41 = x_71;
goto block_69;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec(x_73);
lean_inc(x_71);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_71);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_40 = x_80;
x_41 = x_71;
goto block_69;
}
}
}
block_27:
{
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_15) == 0)
{
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
lean_dec(x_17);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
block_39:
{
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_29; 
if (lean_is_scalar(x_6)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_6;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_28);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_16);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
block_69:
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_43 = l_Lean_Json_getObjVal_x3f(x_1, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_44; 
lean_dec(x_6);
x_44 = lean_box(0);
x_17 = x_44;
goto block_27;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
x_28 = x_45;
goto block_39;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_48 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_46, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_dec(x_46);
lean_dec(x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_49; 
lean_dec(x_6);
x_49 = lean_box(0);
x_17 = x_49;
goto block_27;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec(x_40);
x_28 = x_50;
goto block_39;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_53 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_46, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_54; 
lean_dec(x_6);
x_54 = lean_box(0);
x_17 = x_54;
goto block_27;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_40, 0);
lean_inc(x_55);
lean_dec(x_40);
x_28 = x_55;
goto block_39;
}
}
else
{
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_56; 
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_59 = l_Lean_Json_getObjVal_x3f(x_46, x_58);
lean_dec(x_46);
x_60 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_60, 0, x_41);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_unbox(x_51);
lean_dec(x_51);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_61);
lean_ctor_set(x_53, 0, x_60);
x_17 = x_53;
goto block_27;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_53, 0);
lean_inc(x_62);
lean_dec(x_53);
x_63 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_64 = l_Lean_Json_getObjVal_x3f(x_46, x_63);
lean_dec(x_46);
x_65 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_65, 0, x_41);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_64);
x_66 = lean_unbox(x_51);
lean_dec(x_51);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_66);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_17 = x_67;
goto block_27;
}
}
else
{
lean_object* x_68; 
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_41);
x_68 = lean_ctor_get(x_40, 0);
lean_inc(x_68);
lean_dec(x_40);
x_28 = x_68;
goto block_39;
}
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
lean_object* x_102; 
lean_dec(x_6);
lean_dec(x_5);
x_102 = lean_box(0);
return x_102;
}
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_JsonRpc_instFromJsonMessage___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instFromJsonMessage(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instFromJsonNotification_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_JsonRpc_instFromJsonNotification_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_JsonRpc_instToJsonMessage___closed__3;
x_32 = l_Lean_Json_getObjVal_x3f(x_2, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_1);
x_33 = lean_box(0);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_32, 0);
if (lean_obj_tag(x_35) == 3)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_38 = lean_string_dec_eq(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
lean_free_object(x_32);
lean_dec(x_1);
x_39 = lean_box(0);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_41 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_2, x_40);
x_42 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_43 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_2, x_42);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_112; 
lean_free_object(x_32);
x_112 = lean_box(0);
x_44 = x_112;
goto block_111;
}
else
{
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_113; 
lean_free_object(x_32);
x_113 = lean_box(0);
x_44 = x_113;
goto block_111;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_41, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_43, 0);
lean_inc(x_115);
x_116 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_117 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_2, x_116);
x_118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_115);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_32, 0, x_118);
x_44 = x_32;
goto block_111;
}
}
block_111:
{
lean_object* x_45; 
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_100; 
x_100 = lean_box(0);
x_45 = x_100;
goto block_99;
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_43);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_43, 0);
x_103 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_104 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_2, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_43, 0, x_105);
x_45 = x_43;
goto block_99;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_43, 0);
lean_inc(x_106);
lean_dec(x_43);
x_107 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_108 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_2, x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_45 = x_110;
goto block_99;
}
}
block_99:
{
lean_object* x_46; lean_object* x_53; lean_object* x_58; lean_object* x_59; 
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_88; 
x_88 = lean_box(0);
x_46 = x_88;
goto block_52;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_41, 0);
lean_inc(x_89);
lean_dec(x_41);
x_90 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_91 = l_Lean_Json_getObjVal_x3f(x_2, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_box(0);
x_58 = x_92;
x_59 = x_89;
goto block_87;
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_89);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_91, 0, x_95);
x_58 = x_91;
x_59 = x_89;
goto block_87;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
lean_dec(x_91);
lean_inc(x_89);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_89);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_58 = x_98;
x_59 = x_89;
goto block_87;
}
}
}
block_52:
{
if (lean_obj_tag(x_45) == 0)
{
if (lean_obj_tag(x_44) == 0)
{
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec(x_1);
x_47 = lean_box(0);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_3 = x_48;
goto block_30;
}
}
else
{
lean_object* x_49; 
lean_dec(x_46);
x_49 = lean_ctor_get(x_44, 0);
lean_inc(x_49);
lean_dec(x_44);
x_3 = x_49;
goto block_30;
}
}
else
{
lean_dec(x_46);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
x_3 = x_50;
goto block_30;
}
else
{
lean_object* x_51; 
lean_dec(x_45);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
x_3 = x_51;
goto block_30;
}
}
}
block_57:
{
if (lean_obj_tag(x_45) == 0)
{
if (lean_obj_tag(x_44) == 0)
{
x_3 = x_53;
goto block_30;
}
else
{
lean_object* x_54; 
lean_dec(x_53);
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
lean_dec(x_44);
x_3 = x_54;
goto block_30;
}
}
else
{
lean_dec(x_53);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_3 = x_55;
goto block_30;
}
else
{
lean_object* x_56; 
lean_dec(x_45);
x_56 = lean_ctor_get(x_44, 0);
lean_inc(x_56);
lean_dec(x_44);
x_3 = x_56;
goto block_30;
}
}
}
block_87:
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_61 = l_Lean_Json_getObjVal_x3f(x_2, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_59);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_62; 
x_62 = lean_box(0);
x_46 = x_62;
goto block_52;
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
lean_dec(x_58);
x_53 = x_63;
goto block_57;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_66 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_64, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_dec(x_64);
lean_dec(x_59);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_67; 
x_67 = lean_box(0);
x_46 = x_67;
goto block_52;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_58, 0);
lean_inc(x_68);
lean_dec(x_58);
x_53 = x_68;
goto block_57;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_71 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_64, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_59);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_72; 
x_72 = lean_box(0);
x_46 = x_72;
goto block_52;
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_58, 0);
lean_inc(x_73);
lean_dec(x_58);
x_53 = x_73;
goto block_57;
}
}
else
{
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_77 = l_Lean_Json_getObjVal_x3f(x_64, x_76);
lean_dec(x_64);
x_78 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_78, 0, x_59);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_unbox(x_69);
lean_dec(x_69);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_79);
lean_ctor_set(x_71, 0, x_78);
x_46 = x_71;
goto block_52;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_71, 0);
lean_inc(x_80);
lean_dec(x_71);
x_81 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_82 = l_Lean_Json_getObjVal_x3f(x_64, x_81);
lean_dec(x_64);
x_83 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_83, 0, x_59);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set(x_83, 2, x_82);
x_84 = lean_unbox(x_69);
lean_dec(x_69);
lean_ctor_set_uint8(x_83, sizeof(void*)*3, x_84);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_83);
x_46 = x_85;
goto block_52;
}
}
else
{
lean_object* x_86; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_64);
lean_dec(x_59);
x_86 = lean_ctor_get(x_58, 0);
lean_inc(x_86);
lean_dec(x_58);
x_53 = x_86;
goto block_57;
}
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
lean_object* x_119; 
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_1);
x_119 = lean_box(0);
return x_119;
}
}
else
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_32, 0);
lean_inc(x_120);
lean_dec(x_32);
if (lean_obj_tag(x_120) == 3)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec(x_120);
x_122 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_123 = lean_string_dec_eq(x_121, x_122);
lean_dec(x_121);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_1);
x_124 = lean_box(0);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_126 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_2, x_125);
x_127 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_128 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_2, x_127);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_186; 
x_186 = lean_box(0);
x_129 = x_186;
goto block_185;
}
else
{
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_187; 
x_187 = lean_box(0);
x_129 = x_187;
goto block_185;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_126, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_128, 0);
lean_inc(x_189);
x_190 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_191 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_2, x_190);
x_192 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_192, 0, x_188);
lean_ctor_set(x_192, 1, x_189);
lean_ctor_set(x_192, 2, x_191);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
x_129 = x_193;
goto block_185;
}
}
block_185:
{
lean_object* x_130; 
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_178; 
x_178 = lean_box(0);
x_130 = x_178;
goto block_177;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_179 = lean_ctor_get(x_128, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_180 = x_128;
} else {
 lean_dec_ref(x_128);
 x_180 = lean_box(0);
}
x_181 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_182 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_2, x_181);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_182);
if (lean_is_scalar(x_180)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_180;
}
lean_ctor_set(x_184, 0, x_183);
x_130 = x_184;
goto block_177;
}
block_177:
{
lean_object* x_131; lean_object* x_138; lean_object* x_143; lean_object* x_144; 
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_168; 
x_168 = lean_box(0);
x_131 = x_168;
goto block_137;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_126, 0);
lean_inc(x_169);
lean_dec(x_126);
x_170 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_171 = l_Lean_Json_getObjVal_x3f(x_2, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_box(0);
x_143 = x_172;
x_144 = x_169;
goto block_167;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
lean_inc(x_169);
x_175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_175, 0, x_169);
lean_ctor_set(x_175, 1, x_173);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(1, 1, 0);
} else {
 x_176 = x_174;
}
lean_ctor_set(x_176, 0, x_175);
x_143 = x_176;
x_144 = x_169;
goto block_167;
}
}
block_137:
{
if (lean_obj_tag(x_130) == 0)
{
if (lean_obj_tag(x_129) == 0)
{
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
lean_dec(x_1);
x_132 = lean_box(0);
return x_132;
}
else
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
x_3 = x_133;
goto block_30;
}
}
else
{
lean_object* x_134; 
lean_dec(x_131);
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
lean_dec(x_129);
x_3 = x_134;
goto block_30;
}
}
else
{
lean_dec(x_131);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
lean_dec(x_130);
x_3 = x_135;
goto block_30;
}
else
{
lean_object* x_136; 
lean_dec(x_130);
x_136 = lean_ctor_get(x_129, 0);
lean_inc(x_136);
lean_dec(x_129);
x_3 = x_136;
goto block_30;
}
}
}
block_142:
{
if (lean_obj_tag(x_130) == 0)
{
if (lean_obj_tag(x_129) == 0)
{
x_3 = x_138;
goto block_30;
}
else
{
lean_object* x_139; 
lean_dec(x_138);
x_139 = lean_ctor_get(x_129, 0);
lean_inc(x_139);
lean_dec(x_129);
x_3 = x_139;
goto block_30;
}
}
else
{
lean_dec(x_138);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_130, 0);
lean_inc(x_140);
lean_dec(x_130);
x_3 = x_140;
goto block_30;
}
else
{
lean_object* x_141; 
lean_dec(x_130);
x_141 = lean_ctor_get(x_129, 0);
lean_inc(x_141);
lean_dec(x_129);
x_3 = x_141;
goto block_30;
}
}
}
block_167:
{
lean_object* x_145; lean_object* x_146; 
x_145 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_146 = l_Lean_Json_getObjVal_x3f(x_2, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_dec(x_144);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_147; 
x_147 = lean_box(0);
x_131 = x_147;
goto block_137;
}
else
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_143, 0);
lean_inc(x_148);
lean_dec(x_143);
x_138 = x_148;
goto block_142;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
lean_dec(x_146);
x_150 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_151 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_149, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_dec(x_149);
lean_dec(x_144);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_152; 
x_152 = lean_box(0);
x_131 = x_152;
goto block_137;
}
else
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_143, 0);
lean_inc(x_153);
lean_dec(x_143);
x_138 = x_153;
goto block_142;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
lean_dec(x_151);
x_155 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_156 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_149, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_144);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_157; 
x_157 = lean_box(0);
x_131 = x_157;
goto block_137;
}
else
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_143, 0);
lean_inc(x_158);
lean_dec(x_143);
x_138 = x_158;
goto block_142;
}
}
else
{
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_160 = x_156;
} else {
 lean_dec_ref(x_156);
 x_160 = lean_box(0);
}
x_161 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_162 = l_Lean_Json_getObjVal_x3f(x_149, x_161);
lean_dec(x_149);
x_163 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_163, 0, x_144);
lean_ctor_set(x_163, 1, x_159);
lean_ctor_set(x_163, 2, x_162);
x_164 = lean_unbox(x_154);
lean_dec(x_154);
lean_ctor_set_uint8(x_163, sizeof(void*)*3, x_164);
if (lean_is_scalar(x_160)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_160;
}
lean_ctor_set(x_165, 0, x_163);
x_131 = x_165;
goto block_137;
}
else
{
lean_object* x_166; 
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_144);
x_166 = lean_ctor_get(x_143, 0);
lean_inc(x_166);
lean_dec(x_143);
x_138 = x_166;
goto block_142;
}
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
lean_object* x_194; 
lean_dec(x_120);
lean_dec(x_1);
x_194 = lean_box(0);
return x_194;
}
}
}
block_30:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_apply_1(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = lean_box(0);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_apply_1(x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_18);
x_22 = lean_box(0);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_3);
lean_dec(x_1);
x_29 = lean_box(0);
return x_29;
}
}
}
}
lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Stream_readMessage_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_IO_FS_Stream_readMessage_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_readMessage_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("JSON '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readMessage___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' did not have the format of a JSON-RPC message");
return x_1;
}
}
lean_object* l_IO_FS_Stream_readMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readJson(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_17; lean_object* x_18; 
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
x_17 = l_Lean_JsonRpc_instToJsonMessage___closed__3;
x_18 = l_Lean_Json_getObjVal_x3f(x_5, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
x_8 = x_19;
goto block_16;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_21) == 3)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_24 = lean_string_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_free_object(x_18);
x_25 = lean_box(0);
x_8 = x_25;
goto block_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_27 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_5, x_26);
x_28 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_29 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_5, x_28);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_106; 
lean_free_object(x_18);
x_106 = lean_box(0);
x_30 = x_106;
goto block_105;
}
else
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_107; 
lean_free_object(x_18);
x_107 = lean_box(0);
x_30 = x_107;
goto block_105;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_27, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_29, 0);
lean_inc(x_109);
x_110 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_111 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_5, x_110);
x_112 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set(x_112, 2, x_111);
lean_ctor_set(x_18, 0, x_112);
x_30 = x_18;
goto block_105;
}
}
block_105:
{
lean_object* x_31; 
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_94; 
x_94 = lean_box(0);
x_31 = x_94;
goto block_93;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_29);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_29, 0);
x_97 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_98 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_5, x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_29, 0, x_99);
x_31 = x_29;
goto block_93;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_29, 0);
lean_inc(x_100);
lean_dec(x_29);
x_101 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_102 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_5, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_31 = x_104;
goto block_93;
}
}
block_93:
{
lean_object* x_32; lean_object* x_43; lean_object* x_52; lean_object* x_53; 
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
x_32 = x_82;
goto block_42;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_27, 0);
lean_inc(x_83);
lean_dec(x_27);
x_84 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_85 = l_Lean_Json_getObjVal_x3f(x_5, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_box(0);
x_52 = x_86;
x_53 = x_83;
goto block_81;
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_83);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_85, 0, x_89);
x_52 = x_85;
x_53 = x_83;
goto block_81;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
lean_dec(x_85);
lean_inc(x_83);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_83);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_52 = x_92;
x_53 = x_83;
goto block_81;
}
}
}
block_42:
{
if (lean_obj_tag(x_31) == 0)
{
if (lean_obj_tag(x_30) == 0)
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_8 = x_33;
goto block_16;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_7);
lean_dec(x_5);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_6);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_5);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_6);
return x_37;
}
}
else
{
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
lean_dec(x_31);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_6);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_6);
return x_41;
}
}
}
block_51:
{
if (lean_obj_tag(x_31) == 0)
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_6);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_43);
x_45 = lean_ctor_get(x_30, 0);
lean_inc(x_45);
lean_dec(x_30);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_6);
return x_46;
}
}
else
{
lean_dec(x_43);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_31, 0);
lean_inc(x_47);
lean_dec(x_31);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_6);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_31);
x_49 = lean_ctor_get(x_30, 0);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
return x_50;
}
}
}
block_81:
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_55 = l_Lean_Json_getObjVal_x3f(x_5, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_dec(x_53);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_32 = x_56;
goto block_42;
}
else
{
lean_object* x_57; 
lean_dec(x_7);
lean_dec(x_5);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_43 = x_57;
goto block_51;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_60 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_58, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_dec(x_58);
lean_dec(x_53);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_61; 
x_61 = lean_box(0);
x_32 = x_61;
goto block_42;
}
else
{
lean_object* x_62; 
lean_dec(x_7);
lean_dec(x_5);
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
lean_dec(x_52);
x_43 = x_62;
goto block_51;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_65 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_58, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_63);
lean_dec(x_58);
lean_dec(x_53);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_66; 
x_66 = lean_box(0);
x_32 = x_66;
goto block_42;
}
else
{
lean_object* x_67; 
lean_dec(x_7);
lean_dec(x_5);
x_67 = lean_ctor_get(x_52, 0);
lean_inc(x_67);
lean_dec(x_52);
x_43 = x_67;
goto block_51;
}
}
else
{
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_71 = l_Lean_Json_getObjVal_x3f(x_58, x_70);
lean_dec(x_58);
x_72 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_72, 0, x_53);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_unbox(x_63);
lean_dec(x_63);
lean_ctor_set_uint8(x_72, sizeof(void*)*3, x_73);
lean_ctor_set(x_65, 0, x_72);
x_32 = x_65;
goto block_42;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_65, 0);
lean_inc(x_74);
lean_dec(x_65);
x_75 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_76 = l_Lean_Json_getObjVal_x3f(x_58, x_75);
lean_dec(x_58);
x_77 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_77, 0, x_53);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set(x_77, 2, x_76);
x_78 = lean_unbox(x_63);
lean_dec(x_63);
lean_ctor_set_uint8(x_77, sizeof(void*)*3, x_78);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_77);
x_32 = x_79;
goto block_42;
}
}
else
{
lean_object* x_80; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_58);
lean_dec(x_53);
lean_dec(x_7);
lean_dec(x_5);
x_80 = lean_ctor_get(x_52, 0);
lean_inc(x_80);
lean_dec(x_52);
x_43 = x_80;
goto block_51;
}
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
lean_object* x_113; 
lean_free_object(x_18);
lean_dec(x_21);
x_113 = lean_box(0);
x_8 = x_113;
goto block_16;
}
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_18, 0);
lean_inc(x_114);
lean_dec(x_18);
if (lean_obj_tag(x_114) == 3)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_117 = lean_string_dec_eq(x_115, x_116);
lean_dec(x_115);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_box(0);
x_8 = x_118;
goto block_16;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_120 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_5, x_119);
x_121 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_122 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_5, x_121);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_188; 
x_188 = lean_box(0);
x_123 = x_188;
goto block_187;
}
else
{
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_189; 
x_189 = lean_box(0);
x_123 = x_189;
goto block_187;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_190 = lean_ctor_get(x_120, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_122, 0);
lean_inc(x_191);
x_192 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_193 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_5, x_192);
x_194 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_194, 0, x_190);
lean_ctor_set(x_194, 1, x_191);
lean_ctor_set(x_194, 2, x_193);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_123 = x_195;
goto block_187;
}
}
block_187:
{
lean_object* x_124; 
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_180; 
x_180 = lean_box(0);
x_124 = x_180;
goto block_179;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_181 = lean_ctor_get(x_122, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_182 = x_122;
} else {
 lean_dec_ref(x_122);
 x_182 = lean_box(0);
}
x_183 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_184 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_5, x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_181);
lean_ctor_set(x_185, 1, x_184);
if (lean_is_scalar(x_182)) {
 x_186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_186 = x_182;
}
lean_ctor_set(x_186, 0, x_185);
x_124 = x_186;
goto block_179;
}
block_179:
{
lean_object* x_125; lean_object* x_136; lean_object* x_145; lean_object* x_146; 
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_170; 
x_170 = lean_box(0);
x_125 = x_170;
goto block_135;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_120, 0);
lean_inc(x_171);
lean_dec(x_120);
x_172 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_173 = l_Lean_Json_getObjVal_x3f(x_5, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
x_174 = lean_box(0);
x_145 = x_174;
x_146 = x_171;
goto block_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
lean_inc(x_171);
x_177 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_177, 0, x_171);
lean_ctor_set(x_177, 1, x_175);
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_177);
x_145 = x_178;
x_146 = x_171;
goto block_169;
}
}
block_135:
{
if (lean_obj_tag(x_124) == 0)
{
if (lean_obj_tag(x_123) == 0)
{
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_box(0);
x_8 = x_126;
goto block_16;
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_7);
lean_dec(x_5);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_6);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_125);
lean_dec(x_7);
lean_dec(x_5);
x_129 = lean_ctor_get(x_123, 0);
lean_inc(x_129);
lean_dec(x_123);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_6);
return x_130;
}
}
else
{
lean_dec(x_125);
lean_dec(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_124, 0);
lean_inc(x_131);
lean_dec(x_124);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_6);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_124);
x_133 = lean_ctor_get(x_123, 0);
lean_inc(x_133);
lean_dec(x_123);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_6);
return x_134;
}
}
}
block_144:
{
if (lean_obj_tag(x_124) == 0)
{
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_6);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_136);
x_138 = lean_ctor_get(x_123, 0);
lean_inc(x_138);
lean_dec(x_123);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_6);
return x_139;
}
}
else
{
lean_dec(x_136);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_124, 0);
lean_inc(x_140);
lean_dec(x_124);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_6);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_124);
x_142 = lean_ctor_get(x_123, 0);
lean_inc(x_142);
lean_dec(x_123);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_6);
return x_143;
}
}
}
block_169:
{
lean_object* x_147; lean_object* x_148; 
x_147 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_148 = l_Lean_Json_getObjVal_x3f(x_5, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_dec(x_146);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
x_125 = x_149;
goto block_135;
}
else
{
lean_object* x_150; 
lean_dec(x_7);
lean_dec(x_5);
x_150 = lean_ctor_get(x_145, 0);
lean_inc(x_150);
lean_dec(x_145);
x_136 = x_150;
goto block_144;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
lean_dec(x_148);
x_152 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_153 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_151, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_dec(x_151);
lean_dec(x_146);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_154; 
x_154 = lean_box(0);
x_125 = x_154;
goto block_135;
}
else
{
lean_object* x_155; 
lean_dec(x_7);
lean_dec(x_5);
x_155 = lean_ctor_get(x_145, 0);
lean_inc(x_155);
lean_dec(x_145);
x_136 = x_155;
goto block_144;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
lean_dec(x_153);
x_157 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_158 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_151, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_dec(x_156);
lean_dec(x_151);
lean_dec(x_146);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_159; 
x_159 = lean_box(0);
x_125 = x_159;
goto block_135;
}
else
{
lean_object* x_160; 
lean_dec(x_7);
lean_dec(x_5);
x_160 = lean_ctor_get(x_145, 0);
lean_inc(x_160);
lean_dec(x_145);
x_136 = x_160;
goto block_144;
}
}
else
{
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 x_162 = x_158;
} else {
 lean_dec_ref(x_158);
 x_162 = lean_box(0);
}
x_163 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_164 = l_Lean_Json_getObjVal_x3f(x_151, x_163);
lean_dec(x_151);
x_165 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_165, 0, x_146);
lean_ctor_set(x_165, 1, x_161);
lean_ctor_set(x_165, 2, x_164);
x_166 = lean_unbox(x_156);
lean_dec(x_156);
lean_ctor_set_uint8(x_165, sizeof(void*)*3, x_166);
if (lean_is_scalar(x_162)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_162;
}
lean_ctor_set(x_167, 0, x_165);
x_125 = x_167;
goto block_135;
}
else
{
lean_object* x_168; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_151);
lean_dec(x_146);
lean_dec(x_7);
lean_dec(x_5);
x_168 = lean_ctor_get(x_145, 0);
lean_inc(x_168);
lean_dec(x_145);
x_136 = x_168;
goto block_144;
}
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
lean_object* x_196; 
lean_dec(x_114);
x_196 = lean_box(0);
x_8 = x_196;
goto block_16;
}
}
}
block_16:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
x_9 = l_Lean_Json_compress(x_5);
x_10 = l_IO_FS_Stream_readMessage___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_IO_FS_Stream_readMessage___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
if (lean_is_scalar(x_7)) {
 x_15 = lean_alloc_ctor(1, 2, 0);
} else {
 x_15 = x_7;
 lean_ctor_set_tag(x_15, 1);
}
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
else
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_4);
if (x_197 == 0)
{
return x_4;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_4, 0);
x_199 = lean_ctor_get(x_4, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_4);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_FS_Stream_readRequestAs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_IO_FS_Stream_readRequestAs_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_readRequestAs_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Stream_readRequestAs_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_IO_FS_Stream_readRequestAs_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_readRequestAs_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected method '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', got method '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unexpected param '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' for method '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected JSON-RPC request, got: '");
return x_1;
}
}
lean_object* l_IO_FS_Stream_readRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readMessage(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_string_dec_eq(x_12, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
x_15 = l_IO_FS_Stream_readRequestAs___closed__1;
x_16 = lean_string_append(x_15, x_3);
lean_dec(x_3);
x_17 = l_IO_FS_Stream_readRequestAs___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_12);
lean_dec(x_12);
x_20 = l_Char_quote___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
if (lean_is_scalar(x_10)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_10;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_40; 
x_40 = lean_box(0);
x_24 = x_40;
goto block_39;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
lean_dec(x_13);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_24 = x_43;
goto block_39;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_24 = x_45;
goto block_39;
}
}
block_39:
{
lean_object* x_25; 
lean_inc(x_24);
x_25 = lean_apply_1(x_5, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
x_26 = l_Lean_Json_compress(x_24);
x_27 = l_IO_FS_Stream_readRequestAs___closed__3;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_IO_FS_Stream_readRequestAs___closed__4;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_3);
lean_dec(x_3);
x_32 = l_Char_quote___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_10)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_10;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_24);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_36);
if (lean_is_scalar(x_10)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_10;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_9);
return x_38;
}
}
}
}
case 1:
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_7);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_47 = lean_ctor_get(x_7, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_8, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_dec(x_8);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_48);
x_51 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_54 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_53, x_49);
lean_dec(x_49);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Json_mkObj(x_57);
x_59 = l_Lean_Json_compress(x_58);
x_60 = l_IO_FS_Stream_readRequestAs___closed__5;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = l_Char_quote___closed__1;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_64);
return x_7;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
lean_dec(x_7);
x_66 = lean_ctor_get(x_8, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_8, 1);
lean_inc(x_67);
lean_dec(x_8);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_66);
x_69 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_72 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_71, x_67);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Json_mkObj(x_75);
x_77 = l_Lean_Json_compress(x_76);
x_78 = l_IO_FS_Stream_readRequestAs___closed__5;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Char_quote___closed__1;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_65);
return x_83;
}
}
case 2:
{
uint8_t x_84; 
lean_dec(x_5);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_7);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_7, 0);
lean_dec(x_85);
x_86 = lean_ctor_get(x_8, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_8, 1);
lean_inc(x_87);
lean_dec(x_8);
x_88 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
switch (lean_obj_tag(x_86)) {
case 0:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
lean_dec(x_86);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_91);
x_97 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_Json_mkObj(x_98);
x_100 = l_Lean_Json_compress(x_99);
x_101 = l_IO_FS_Stream_readRequestAs___closed__5;
x_102 = lean_string_append(x_101, x_100);
lean_dec(x_100);
x_103 = l_Char_quote___closed__1;
x_104 = lean_string_append(x_102, x_103);
x_105 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_105);
return x_7;
}
case 1:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_106 = lean_ctor_get(x_86, 0);
lean_inc(x_106);
lean_dec(x_86);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_91);
x_111 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = l_Lean_Json_mkObj(x_112);
x_114 = l_Lean_Json_compress(x_113);
x_115 = l_IO_FS_Stream_readRequestAs___closed__5;
x_116 = lean_string_append(x_115, x_114);
lean_dec(x_114);
x_117 = l_Char_quote___closed__1;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_119);
return x_7;
}
default: 
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_120 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_91);
x_122 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_Json_mkObj(x_123);
x_125 = l_Lean_Json_compress(x_124);
x_126 = l_IO_FS_Stream_readRequestAs___closed__5;
x_127 = lean_string_append(x_126, x_125);
lean_dec(x_125);
x_128 = l_Char_quote___closed__1;
x_129 = lean_string_append(x_127, x_128);
x_130 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_130);
return x_7;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_131 = lean_ctor_get(x_7, 1);
lean_inc(x_131);
lean_dec(x_7);
x_132 = lean_ctor_get(x_8, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_8, 1);
lean_inc(x_133);
lean_dec(x_8);
x_134 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
switch (lean_obj_tag(x_132)) {
case 0:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
lean_dec(x_132);
x_139 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_137);
x_143 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l_Lean_Json_mkObj(x_144);
x_146 = l_Lean_Json_compress(x_145);
x_147 = l_IO_FS_Stream_readRequestAs___closed__5;
x_148 = lean_string_append(x_147, x_146);
lean_dec(x_146);
x_149 = l_Char_quote___closed__1;
x_150 = lean_string_append(x_148, x_149);
x_151 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_131);
return x_152;
}
case 1:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_153 = lean_ctor_get(x_132, 0);
lean_inc(x_153);
lean_dec(x_132);
x_154 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_137);
x_158 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = l_Lean_Json_mkObj(x_159);
x_161 = l_Lean_Json_compress(x_160);
x_162 = l_IO_FS_Stream_readRequestAs___closed__5;
x_163 = lean_string_append(x_162, x_161);
lean_dec(x_161);
x_164 = l_Char_quote___closed__1;
x_165 = lean_string_append(x_163, x_164);
x_166 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_131);
return x_167;
}
default: 
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_168 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_137);
x_170 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = l_Lean_Json_mkObj(x_171);
x_173 = l_Lean_Json_compress(x_172);
x_174 = l_IO_FS_Stream_readRequestAs___closed__5;
x_175 = lean_string_append(x_174, x_173);
lean_dec(x_173);
x_176 = l_Char_quote___closed__1;
x_177 = lean_string_append(x_175, x_176);
x_178 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_131);
return x_179;
}
}
}
}
default: 
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_5);
lean_dec(x_3);
x_180 = lean_ctor_get(x_7, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_181 = x_7;
} else {
 lean_dec_ref(x_7);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_8, 0);
lean_inc(x_182);
x_183 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_184 = lean_ctor_get(x_8, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_8, 2);
lean_inc(x_185);
lean_dec(x_8);
x_186 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_186, 0, x_184);
x_187 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_186);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_192 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_191, x_185);
lean_dec(x_185);
switch (lean_obj_tag(x_182)) {
case 0:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_182, 0);
lean_inc(x_229);
lean_dec(x_182);
x_230 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_193 = x_230;
goto block_228;
}
case 1:
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_182, 0);
lean_inc(x_231);
lean_dec(x_182);
x_232 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_232, 0, x_231);
x_193 = x_232;
goto block_228;
}
default: 
{
lean_object* x_233; 
x_233 = lean_box(0);
x_193 = x_233;
goto block_228;
}
}
block_228:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
switch (x_183) {
case 0:
{
lean_object* x_217; 
x_217 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_196 = x_217;
goto block_216;
}
case 1:
{
lean_object* x_218; 
x_218 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_196 = x_218;
goto block_216;
}
case 2:
{
lean_object* x_219; 
x_219 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_196 = x_219;
goto block_216;
}
case 3:
{
lean_object* x_220; 
x_220 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_196 = x_220;
goto block_216;
}
case 4:
{
lean_object* x_221; 
x_221 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_196 = x_221;
goto block_216;
}
case 5:
{
lean_object* x_222; 
x_222 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_196 = x_222;
goto block_216;
}
case 6:
{
lean_object* x_223; 
x_223 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_196 = x_223;
goto block_216;
}
case 7:
{
lean_object* x_224; 
x_224 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_196 = x_224;
goto block_216;
}
case 8:
{
lean_object* x_225; 
x_225 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_196 = x_225;
goto block_216;
}
case 9:
{
lean_object* x_226; 
x_226 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_196 = x_226;
goto block_216;
}
default: 
{
lean_object* x_227; 
x_227 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_196 = x_227;
goto block_216;
}
}
block_216:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_197 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_190);
x_200 = l_List_append___rarg(x_199, x_192);
x_201 = l_Lean_Json_mkObj(x_200);
x_202 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_189);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = l_Lean_Json_mkObj(x_207);
x_209 = l_Lean_Json_compress(x_208);
x_210 = l_IO_FS_Stream_readRequestAs___closed__5;
x_211 = lean_string_append(x_210, x_209);
lean_dec(x_209);
x_212 = l_Char_quote___closed__1;
x_213 = lean_string_append(x_211, x_212);
x_214 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_214, 0, x_213);
if (lean_is_scalar(x_181)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_181;
 lean_ctor_set_tag(x_215, 1);
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_180);
return x_215;
}
}
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_5);
lean_dec(x_3);
x_234 = !lean_is_exclusive(x_7);
if (x_234 == 0)
{
return x_7;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_7, 0);
x_236 = lean_ctor_get(x_7, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_7);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readRequestAs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected JSON-RPC notification, got: '");
return x_1;
}
}
lean_object* l_IO_FS_Stream_readNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readMessage(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 0:
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_20 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_19, x_13);
lean_dec(x_13);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
x_26 = l_List_append___rarg(x_25, x_20);
x_27 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Json_mkObj(x_28);
x_30 = l_Lean_Json_compress(x_29);
x_31 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Char_quote___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
return x_7;
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
lean_dec(x_11);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_18);
x_41 = l_List_append___rarg(x_40, x_20);
x_42 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Json_mkObj(x_43);
x_45 = l_Lean_Json_compress(x_44);
x_46 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Char_quote___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_50);
return x_7;
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_18);
x_53 = l_List_append___rarg(x_52, x_20);
x_54 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Json_mkObj(x_55);
x_57 = l_Lean_Json_compress(x_56);
x_58 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Char_quote___closed__1;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_62);
return x_7;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_dec(x_7);
x_64 = lean_ctor_get(x_8, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_8, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_8, 2);
lean_inc(x_66);
lean_dec(x_8);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_68 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_73 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_72, x_66);
lean_dec(x_66);
switch (lean_obj_tag(x_64)) {
case 0:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
lean_dec(x_64);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_71);
x_79 = l_List_append___rarg(x_78, x_73);
x_80 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Json_mkObj(x_81);
x_83 = l_Lean_Json_compress(x_82);
x_84 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_85 = lean_string_append(x_84, x_83);
lean_dec(x_83);
x_86 = l_Char_quote___closed__1;
x_87 = lean_string_append(x_85, x_86);
x_88 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_63);
return x_89;
}
case 1:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_90 = lean_ctor_get(x_64, 0);
lean_inc(x_90);
lean_dec(x_64);
x_91 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_71);
x_95 = l_List_append___rarg(x_94, x_73);
x_96 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Json_mkObj(x_97);
x_99 = l_Lean_Json_compress(x_98);
x_100 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
x_102 = l_Char_quote___closed__1;
x_103 = lean_string_append(x_101, x_102);
x_104 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_63);
return x_105;
}
default: 
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_106 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_71);
x_108 = l_List_append___rarg(x_107, x_73);
x_109 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_Json_mkObj(x_110);
x_112 = l_Lean_Json_compress(x_111);
x_113 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_114 = lean_string_append(x_113, x_112);
lean_dec(x_112);
x_115 = l_Char_quote___closed__1;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_63);
return x_118;
}
}
}
}
case 1:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_7, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_120 = x_7;
} else {
 lean_dec_ref(x_7);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_8, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_8, 1);
lean_inc(x_122);
lean_dec(x_8);
x_123 = lean_string_dec_eq(x_121, x_3);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_122);
lean_dec(x_5);
x_124 = l_IO_FS_Stream_readRequestAs___closed__1;
x_125 = lean_string_append(x_124, x_3);
lean_dec(x_3);
x_126 = l_IO_FS_Stream_readRequestAs___closed__2;
x_127 = lean_string_append(x_125, x_126);
x_128 = lean_string_append(x_127, x_121);
lean_dec(x_121);
x_129 = l_Char_quote___closed__1;
x_130 = lean_string_append(x_128, x_129);
x_131 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_131, 0, x_130);
if (lean_is_scalar(x_120)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_120;
 lean_ctor_set_tag(x_132, 1);
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_119);
return x_132;
}
else
{
lean_object* x_133; 
lean_dec(x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
x_133 = x_149;
goto block_148;
}
else
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_122, 0);
lean_inc(x_150);
lean_dec(x_122);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_133 = x_152;
goto block_148;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_133 = x_154;
goto block_148;
}
}
block_148:
{
lean_object* x_134; 
lean_inc(x_133);
x_134 = lean_apply_1(x_5, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_135 = l_Lean_Json_compress(x_133);
x_136 = l_IO_FS_Stream_readRequestAs___closed__3;
x_137 = lean_string_append(x_136, x_135);
lean_dec(x_135);
x_138 = l_IO_FS_Stream_readRequestAs___closed__4;
x_139 = lean_string_append(x_137, x_138);
x_140 = lean_string_append(x_139, x_3);
lean_dec(x_3);
x_141 = l_Char_quote___closed__1;
x_142 = lean_string_append(x_140, x_141);
x_143 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_143, 0, x_142);
if (lean_is_scalar(x_120)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_120;
 lean_ctor_set_tag(x_144, 1);
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_119);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_133);
x_145 = lean_ctor_get(x_134, 0);
lean_inc(x_145);
lean_dec(x_134);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_3);
lean_ctor_set(x_146, 1, x_145);
if (lean_is_scalar(x_120)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_120;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_119);
return x_147;
}
}
}
}
case 2:
{
uint8_t x_155; 
lean_dec(x_5);
lean_dec(x_3);
x_155 = !lean_is_exclusive(x_7);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_ctor_get(x_7, 0);
lean_dec(x_156);
x_157 = lean_ctor_get(x_8, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_8, 1);
lean_inc(x_158);
lean_dec(x_8);
x_159 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
switch (lean_obj_tag(x_157)) {
case 0:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_163 = lean_ctor_get(x_157, 0);
lean_inc(x_163);
lean_dec(x_157);
x_164 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_162);
x_168 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
x_170 = l_Lean_Json_mkObj(x_169);
x_171 = l_Lean_Json_compress(x_170);
x_172 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_173 = lean_string_append(x_172, x_171);
lean_dec(x_171);
x_174 = l_Char_quote___closed__1;
x_175 = lean_string_append(x_173, x_174);
x_176 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_176);
return x_7;
}
case 1:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_177 = lean_ctor_get(x_157, 0);
lean_inc(x_177);
lean_dec(x_157);
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_162);
x_182 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = l_Lean_Json_mkObj(x_183);
x_185 = l_Lean_Json_compress(x_184);
x_186 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_187 = lean_string_append(x_186, x_185);
lean_dec(x_185);
x_188 = l_Char_quote___closed__1;
x_189 = lean_string_append(x_187, x_188);
x_190 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_190);
return x_7;
}
default: 
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_191 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_162);
x_193 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = l_Lean_Json_mkObj(x_194);
x_196 = l_Lean_Json_compress(x_195);
x_197 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_198 = lean_string_append(x_197, x_196);
lean_dec(x_196);
x_199 = l_Char_quote___closed__1;
x_200 = lean_string_append(x_198, x_199);
x_201 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_201);
return x_7;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_7, 1);
lean_inc(x_202);
lean_dec(x_7);
x_203 = lean_ctor_get(x_8, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_8, 1);
lean_inc(x_204);
lean_dec(x_8);
x_205 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
switch (lean_obj_tag(x_203)) {
case 0:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_209 = lean_ctor_get(x_203, 0);
lean_inc(x_209);
lean_dec(x_203);
x_210 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_210);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_208);
x_214 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
x_216 = l_Lean_Json_mkObj(x_215);
x_217 = l_Lean_Json_compress(x_216);
x_218 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_219 = lean_string_append(x_218, x_217);
lean_dec(x_217);
x_220 = l_Char_quote___closed__1;
x_221 = lean_string_append(x_219, x_220);
x_222 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_202);
return x_223;
}
case 1:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_224 = lean_ctor_get(x_203, 0);
lean_inc(x_224);
lean_dec(x_203);
x_225 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_226 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_208);
x_229 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = l_Lean_Json_mkObj(x_230);
x_232 = l_Lean_Json_compress(x_231);
x_233 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_234 = lean_string_append(x_233, x_232);
lean_dec(x_232);
x_235 = l_Char_quote___closed__1;
x_236 = lean_string_append(x_234, x_235);
x_237 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_202);
return x_238;
}
default: 
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_239 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_208);
x_241 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = l_Lean_Json_mkObj(x_242);
x_244 = l_Lean_Json_compress(x_243);
x_245 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_246 = lean_string_append(x_245, x_244);
lean_dec(x_244);
x_247 = l_Char_quote___closed__1;
x_248 = lean_string_append(x_246, x_247);
x_249 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_249, 0, x_248);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_202);
return x_250;
}
}
}
}
default: 
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_5);
lean_dec(x_3);
x_251 = lean_ctor_get(x_7, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_252 = x_7;
} else {
 lean_dec_ref(x_7);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_8, 0);
lean_inc(x_253);
x_254 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_255 = lean_ctor_get(x_8, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_8, 2);
lean_inc(x_256);
lean_dec(x_8);
x_257 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_257, 0, x_255);
x_258 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
x_260 = lean_box(0);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
x_262 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_263 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_262, x_256);
lean_dec(x_256);
switch (lean_obj_tag(x_253)) {
case 0:
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_253, 0);
lean_inc(x_300);
lean_dec(x_253);
x_301 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_301, 0, x_300);
x_264 = x_301;
goto block_299;
}
case 1:
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_253, 0);
lean_inc(x_302);
lean_dec(x_253);
x_303 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_303, 0, x_302);
x_264 = x_303;
goto block_299;
}
default: 
{
lean_object* x_304; 
x_304 = lean_box(0);
x_264 = x_304;
goto block_299;
}
}
block_299:
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_264);
switch (x_254) {
case 0:
{
lean_object* x_288; 
x_288 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_267 = x_288;
goto block_287;
}
case 1:
{
lean_object* x_289; 
x_289 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_267 = x_289;
goto block_287;
}
case 2:
{
lean_object* x_290; 
x_290 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_267 = x_290;
goto block_287;
}
case 3:
{
lean_object* x_291; 
x_291 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_267 = x_291;
goto block_287;
}
case 4:
{
lean_object* x_292; 
x_292 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_267 = x_292;
goto block_287;
}
case 5:
{
lean_object* x_293; 
x_293 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_267 = x_293;
goto block_287;
}
case 6:
{
lean_object* x_294; 
x_294 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_267 = x_294;
goto block_287;
}
case 7:
{
lean_object* x_295; 
x_295 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_267 = x_295;
goto block_287;
}
case 8:
{
lean_object* x_296; 
x_296 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_267 = x_296;
goto block_287;
}
case 9:
{
lean_object* x_297; 
x_297 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_267 = x_297;
goto block_287;
}
default: 
{
lean_object* x_298; 
x_298 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_267 = x_298;
goto block_287;
}
}
block_287:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_268 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_261);
x_271 = l_List_append___rarg(x_270, x_263);
x_272 = l_Lean_Json_mkObj(x_271);
x_273 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_260);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_266);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = l_Lean_Json_mkObj(x_278);
x_280 = l_Lean_Json_compress(x_279);
x_281 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_282 = lean_string_append(x_281, x_280);
lean_dec(x_280);
x_283 = l_Char_quote___closed__1;
x_284 = lean_string_append(x_282, x_283);
x_285 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_285, 0, x_284);
if (lean_is_scalar(x_252)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_252;
 lean_ctor_set_tag(x_286, 1);
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_251);
return x_286;
}
}
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_5);
lean_dec(x_3);
x_305 = !lean_is_exclusive(x_7);
if (x_305 == 0)
{
return x_7;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_7, 0);
x_307 = lean_ctor_get(x_7, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_7);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
}
lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readNotificationAs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_IO_FS_Stream_readResponseAs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_IO_FS_Stream_readResponseAs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_readResponseAs_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected JSON-RPC response, got: '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected id ");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", got id ");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unexpected result '");
return x_1;
}
}
lean_object* l_IO_FS_Stream_readResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readMessage(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 0:
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_20 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_19, x_13);
lean_dec(x_13);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
x_26 = l_List_append___rarg(x_25, x_20);
x_27 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Json_mkObj(x_28);
x_30 = l_Lean_Json_compress(x_29);
x_31 = l_IO_FS_Stream_readResponseAs___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Char_quote___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_35);
return x_7;
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
lean_dec(x_11);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_18);
x_41 = l_List_append___rarg(x_40, x_20);
x_42 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Json_mkObj(x_43);
x_45 = l_Lean_Json_compress(x_44);
x_46 = l_IO_FS_Stream_readResponseAs___closed__1;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Char_quote___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_50);
return x_7;
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_18);
x_53 = l_List_append___rarg(x_52, x_20);
x_54 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Json_mkObj(x_55);
x_57 = l_Lean_Json_compress(x_56);
x_58 = l_IO_FS_Stream_readResponseAs___closed__1;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Char_quote___closed__1;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_62);
return x_7;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_dec(x_7);
x_64 = lean_ctor_get(x_8, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_8, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_8, 2);
lean_inc(x_66);
lean_dec(x_8);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_68 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_73 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_72, x_66);
lean_dec(x_66);
switch (lean_obj_tag(x_64)) {
case 0:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
lean_dec(x_64);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_71);
x_79 = l_List_append___rarg(x_78, x_73);
x_80 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Json_mkObj(x_81);
x_83 = l_Lean_Json_compress(x_82);
x_84 = l_IO_FS_Stream_readResponseAs___closed__1;
x_85 = lean_string_append(x_84, x_83);
lean_dec(x_83);
x_86 = l_Char_quote___closed__1;
x_87 = lean_string_append(x_85, x_86);
x_88 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_63);
return x_89;
}
case 1:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_90 = lean_ctor_get(x_64, 0);
lean_inc(x_90);
lean_dec(x_64);
x_91 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_71);
x_95 = l_List_append___rarg(x_94, x_73);
x_96 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Json_mkObj(x_97);
x_99 = l_Lean_Json_compress(x_98);
x_100 = l_IO_FS_Stream_readResponseAs___closed__1;
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
x_102 = l_Char_quote___closed__1;
x_103 = lean_string_append(x_101, x_102);
x_104 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_63);
return x_105;
}
default: 
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_106 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_71);
x_108 = l_List_append___rarg(x_107, x_73);
x_109 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_Json_mkObj(x_110);
x_112 = l_Lean_Json_compress(x_111);
x_113 = l_IO_FS_Stream_readResponseAs___closed__1;
x_114 = lean_string_append(x_113, x_112);
lean_dec(x_112);
x_115 = l_Char_quote___closed__1;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_63);
return x_118;
}
}
}
}
case 1:
{
uint8_t x_119; 
lean_dec(x_5);
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_7);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_120 = lean_ctor_get(x_7, 0);
lean_dec(x_120);
x_121 = lean_ctor_get(x_8, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_8, 1);
lean_inc(x_122);
lean_dec(x_8);
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_121);
x_124 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_127 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_126, x_122);
lean_dec(x_122);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = l_Lean_Json_mkObj(x_130);
x_132 = l_Lean_Json_compress(x_131);
x_133 = l_IO_FS_Stream_readResponseAs___closed__1;
x_134 = lean_string_append(x_133, x_132);
lean_dec(x_132);
x_135 = l_Char_quote___closed__1;
x_136 = lean_string_append(x_134, x_135);
x_137 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_137);
return x_7;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_138 = lean_ctor_get(x_7, 1);
lean_inc(x_138);
lean_dec(x_7);
x_139 = lean_ctor_get(x_8, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_8, 1);
lean_inc(x_140);
lean_dec(x_8);
x_141 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_141, 0, x_139);
x_142 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_145 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_144, x_140);
lean_dec(x_140);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = l_Lean_Json_mkObj(x_148);
x_150 = l_Lean_Json_compress(x_149);
x_151 = l_IO_FS_Stream_readResponseAs___closed__1;
x_152 = lean_string_append(x_151, x_150);
lean_dec(x_150);
x_153 = l_Char_quote___closed__1;
x_154 = lean_string_append(x_152, x_153);
x_155 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_138);
return x_156;
}
}
case 2:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_186; 
x_157 = lean_ctor_get(x_7, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_158 = x_7;
} else {
 lean_dec_ref(x_7);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_8, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_8, 1);
lean_inc(x_160);
lean_dec(x_8);
x_186 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16_(x_159, x_3);
if (x_186 == 0)
{
lean_dec(x_160);
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_187; 
lean_dec(x_3);
x_187 = l_Lean_JsonRpc_instToStringRequestID___closed__1;
x_161 = x_187;
goto block_185;
}
case 1:
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_3, 0);
lean_inc(x_188);
lean_dec(x_3);
x_189 = l_Lean_JsonNumber_toString(x_188);
x_161 = x_189;
goto block_185;
}
default: 
{
lean_object* x_190; 
x_190 = l_Lean_nullKind___closed__1;
x_161 = x_190;
goto block_185;
}
}
}
else
{
lean_object* x_191; 
lean_dec(x_159);
lean_dec(x_158);
lean_inc(x_160);
x_191 = lean_apply_1(x_5, x_160);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_3);
x_192 = l_Lean_Json_compress(x_160);
x_193 = l_IO_FS_Stream_readResponseAs___closed__4;
x_194 = lean_string_append(x_193, x_192);
lean_dec(x_192);
x_195 = l_Char_quote___closed__1;
x_196 = lean_string_append(x_194, x_195);
x_197 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_157);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_160);
x_199 = lean_ctor_get(x_191, 0);
lean_inc(x_199);
lean_dec(x_191);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_3);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_157);
return x_201;
}
}
block_185:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = l_IO_FS_Stream_readResponseAs___closed__2;
x_163 = lean_string_append(x_162, x_161);
lean_dec(x_161);
x_164 = l_IO_FS_Stream_readResponseAs___closed__3;
x_165 = lean_string_append(x_163, x_164);
switch (lean_obj_tag(x_159)) {
case 0:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_159);
x_166 = l_Lean_JsonRpc_instToStringRequestID___closed__1;
x_167 = lean_string_append(x_165, x_166);
x_168 = l_Lean_instInhabitedParserDescr___closed__1;
x_169 = lean_string_append(x_167, x_168);
x_170 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_170, 0, x_169);
if (lean_is_scalar(x_158)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_158;
 lean_ctor_set_tag(x_171, 1);
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_157);
return x_171;
}
case 1:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_159, 0);
lean_inc(x_172);
lean_dec(x_159);
x_173 = l_Lean_JsonNumber_toString(x_172);
x_174 = lean_string_append(x_165, x_173);
lean_dec(x_173);
x_175 = l_Lean_instInhabitedParserDescr___closed__1;
x_176 = lean_string_append(x_174, x_175);
x_177 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_177, 0, x_176);
if (lean_is_scalar(x_158)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_158;
 lean_ctor_set_tag(x_178, 1);
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_157);
return x_178;
}
default: 
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_179 = l_Lean_nullKind___closed__1;
x_180 = lean_string_append(x_165, x_179);
x_181 = l_Lean_instInhabitedParserDescr___closed__1;
x_182 = lean_string_append(x_180, x_181);
x_183 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_183, 0, x_182);
if (lean_is_scalar(x_158)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_158;
 lean_ctor_set_tag(x_184, 1);
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_157);
return x_184;
}
}
}
}
default: 
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_5);
lean_dec(x_3);
x_202 = lean_ctor_get(x_7, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_203 = x_7;
} else {
 lean_dec_ref(x_7);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_8, 0);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_206 = lean_ctor_get(x_8, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_8, 2);
lean_inc(x_207);
lean_dec(x_8);
x_208 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_208, 0, x_206);
x_209 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_box(0);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_214 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_213, x_207);
lean_dec(x_207);
switch (lean_obj_tag(x_204)) {
case 0:
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_204, 0);
lean_inc(x_251);
lean_dec(x_204);
x_252 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_252, 0, x_251);
x_215 = x_252;
goto block_250;
}
case 1:
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_204, 0);
lean_inc(x_253);
lean_dec(x_204);
x_254 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_254, 0, x_253);
x_215 = x_254;
goto block_250;
}
default: 
{
lean_object* x_255; 
x_255 = lean_box(0);
x_215 = x_255;
goto block_250;
}
}
block_250:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
switch (x_205) {
case 0:
{
lean_object* x_239; 
x_239 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_218 = x_239;
goto block_238;
}
case 1:
{
lean_object* x_240; 
x_240 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_218 = x_240;
goto block_238;
}
case 2:
{
lean_object* x_241; 
x_241 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_218 = x_241;
goto block_238;
}
case 3:
{
lean_object* x_242; 
x_242 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_218 = x_242;
goto block_238;
}
case 4:
{
lean_object* x_243; 
x_243 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_218 = x_243;
goto block_238;
}
case 5:
{
lean_object* x_244; 
x_244 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_218 = x_244;
goto block_238;
}
case 6:
{
lean_object* x_245; 
x_245 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_218 = x_245;
goto block_238;
}
case 7:
{
lean_object* x_246; 
x_246 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_218 = x_246;
goto block_238;
}
case 8:
{
lean_object* x_247; 
x_247 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_218 = x_247;
goto block_238;
}
case 9:
{
lean_object* x_248; 
x_248 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_218 = x_248;
goto block_238;
}
default: 
{
lean_object* x_249; 
x_249 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_218 = x_249;
goto block_238;
}
}
block_238:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_219 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_212);
x_222 = l_List_append___rarg(x_221, x_214);
x_223 = l_Lean_Json_mkObj(x_222);
x_224 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_223);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_211);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_217);
lean_ctor_set(x_227, 1, x_226);
x_228 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = l_Lean_Json_mkObj(x_229);
x_231 = l_Lean_Json_compress(x_230);
x_232 = l_IO_FS_Stream_readResponseAs___closed__1;
x_233 = lean_string_append(x_232, x_231);
lean_dec(x_231);
x_234 = l_Char_quote___closed__1;
x_235 = lean_string_append(x_233, x_234);
x_236 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_236, 0, x_235);
if (lean_is_scalar(x_203)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_203;
 lean_ctor_set_tag(x_237, 1);
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_202);
return x_237;
}
}
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_5);
lean_dec(x_3);
x_256 = !lean_is_exclusive(x_7);
if (x_256 == 0)
{
return x_7;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_7, 0);
x_258 = lean_ctor_get(x_7, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_7);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
}
lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readResponseAs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_IO_FS_Stream_writeMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_13 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_12, x_6);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
x_19 = l_List_append___rarg(x_18, x_13);
x_20 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Json_mkObj(x_21);
x_23 = l_IO_FS_Stream_writeJson(x_1, x_22, x_3);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_11);
x_29 = l_List_append___rarg(x_28, x_13);
x_30 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Json_mkObj(x_31);
x_33 = l_IO_FS_Stream_writeJson(x_1, x_32, x_3);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
x_36 = l_List_append___rarg(x_35, x_13);
x_37 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Json_mkObj(x_38);
x_40 = l_IO_FS_Stream_writeJson(x_1, x_39, x_3);
return x_40;
}
}
}
case 1:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_47 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_46, x_42);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Json_mkObj(x_50);
x_52 = l_IO_FS_Stream_writeJson(x_1, x_51, x_3);
return x_52;
}
case 2:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
x_55 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_inc(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
switch (lean_obj_tag(x_53)) {
case 0:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
x_64 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Json_mkObj(x_65);
x_67 = l_IO_FS_Stream_writeJson(x_1, x_66, x_3);
return x_67;
}
case 1:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_53, 0);
lean_inc(x_68);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_58);
x_73 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_Json_mkObj(x_74);
x_76 = l_IO_FS_Stream_writeJson(x_1, x_75, x_3);
return x_76;
}
default: 
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_58);
x_79 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Json_mkObj(x_80);
x_82 = l_IO_FS_Stream_writeJson(x_1, x_81, x_3);
return x_82;
}
}
}
default: 
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_83 = lean_ctor_get(x_2, 0);
x_84 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_85 = lean_ctor_get(x_2, 1);
x_86 = lean_ctor_get(x_2, 2);
lean_inc(x_85);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_85);
x_88 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_93 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_92, x_86);
switch (lean_obj_tag(x_83)) {
case 0:
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_83, 0);
lean_inc(x_124);
x_125 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_94 = x_125;
goto block_123;
}
case 1:
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_83, 0);
lean_inc(x_126);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_94 = x_127;
goto block_123;
}
default: 
{
lean_object* x_128; 
x_128 = lean_box(0);
x_94 = x_128;
goto block_123;
}
}
block_123:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
switch (x_84) {
case 0:
{
lean_object* x_112; 
x_112 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_97 = x_112;
goto block_111;
}
case 1:
{
lean_object* x_113; 
x_113 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_97 = x_113;
goto block_111;
}
case 2:
{
lean_object* x_114; 
x_114 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_97 = x_114;
goto block_111;
}
case 3:
{
lean_object* x_115; 
x_115 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_97 = x_115;
goto block_111;
}
case 4:
{
lean_object* x_116; 
x_116 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_97 = x_116;
goto block_111;
}
case 5:
{
lean_object* x_117; 
x_117 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_97 = x_117;
goto block_111;
}
case 6:
{
lean_object* x_118; 
x_118 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_97 = x_118;
goto block_111;
}
case 7:
{
lean_object* x_119; 
x_119 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_97 = x_119;
goto block_111;
}
case 8:
{
lean_object* x_120; 
x_120 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_97 = x_120;
goto block_111;
}
case 9:
{
lean_object* x_121; 
x_121 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_97 = x_121;
goto block_111;
}
default: 
{
lean_object* x_122; 
x_122 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_97 = x_122;
goto block_111;
}
}
block_111:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_98 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_91);
x_101 = l_List_append___rarg(x_100, x_93);
x_102 = l_Lean_Json_mkObj(x_101);
x_103 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_90);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Json_mkObj(x_108);
x_110 = l_IO_FS_Stream_writeJson(x_1, x_109, x_3);
return x_110;
}
}
}
}
}
}
lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_FS_Stream_writeRequest___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_7);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_IO_FS_Stream_writeMessage(x_2, x_9, x_4);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_IO_FS_Stream_writeRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeRequest___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_writeNotification___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_IO_FS_Stream_writeMessage(x_2, x_8, x_4);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_IO_FS_Stream_writeNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeNotification___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_writeResponse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_IO_FS_Stream_writeMessage(x_2, x_8, x_4);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_IO_FS_Stream_writeResponse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeResponse___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_writeResponseError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_8 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_5);
x_9 = l_IO_FS_Stream_writeMessage(x_1, x_8, x_3);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeResponseError(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_FS_Stream_writeResponseErrorWithData___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_7);
x_11 = l_IO_FS_Stream_writeMessage(x_2, x_10, x_4);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_apply_1(x_1, x_16);
lean_ctor_set(x_5, 0, x_17);
x_18 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_13);
x_19 = l_IO_FS_Stream_writeMessage(x_2, x_18, x_4);
lean_dec(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_apply_1(x_1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_13);
x_24 = l_IO_FS_Stream_writeMessage(x_2, x_23, x_4);
lean_dec(x_23);
return x_24;
}
}
}
}
lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeResponseErrorWithData___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_Control(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Std_Data_RBTree(lean_object*);
lean_object* initialize_Lean_Data_Json(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_JsonRpc(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_RBTree(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_JsonRpc_instInhabitedRequestID___closed__1 = _init_l_Lean_JsonRpc_instInhabitedRequestID___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedRequestID___closed__1);
l_Lean_JsonRpc_instInhabitedRequestID = _init_l_Lean_JsonRpc_instInhabitedRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedRequestID);
l_Lean_JsonRpc_instBEqRequestID___closed__1 = _init_l_Lean_JsonRpc_instBEqRequestID___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instBEqRequestID___closed__1);
l_Lean_JsonRpc_instBEqRequestID = _init_l_Lean_JsonRpc_instBEqRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instBEqRequestID);
l_Lean_JsonRpc_instToStringRequestID___closed__1 = _init_l_Lean_JsonRpc_instToStringRequestID___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instToStringRequestID___closed__1);
l_Lean_JsonRpc_instInhabitedErrorCode = _init_l_Lean_JsonRpc_instInhabitedErrorCode();
l_Lean_JsonRpc_instBEqErrorCode___closed__1 = _init_l_Lean_JsonRpc_instBEqErrorCode___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instBEqErrorCode___closed__1);
l_Lean_JsonRpc_instBEqErrorCode = _init_l_Lean_JsonRpc_instBEqErrorCode();
lean_mark_persistent(l_Lean_JsonRpc_instBEqErrorCode);
l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__1 = _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__1);
l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__2 = _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__2);
l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__3 = _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__3);
l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__4 = _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__4);
l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__5 = _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__5);
l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__6 = _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__6);
l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__7 = _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__7);
l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__8 = _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__8();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__8);
l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__9 = _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__9();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__9);
l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__10 = _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__10();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__10);
l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__11 = _init_l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__11();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode_match__1___rarg___closed__11);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__1 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__1);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__2 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__2);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__3 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__3);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__4 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__4);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__5 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__5);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__6 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__6);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__7 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__7);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__8 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__8();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__8);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__9 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__9();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__9);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__10 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__10();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__10);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__11 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__11();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__11);
l_Lean_JsonRpc_instToJsonErrorCode___closed__1 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__1);
l_Lean_JsonRpc_instToJsonErrorCode___closed__2 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__2);
l_Lean_JsonRpc_instToJsonErrorCode___closed__3 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__3);
l_Lean_JsonRpc_instToJsonErrorCode___closed__4 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__4);
l_Lean_JsonRpc_instToJsonErrorCode___closed__5 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__5);
l_Lean_JsonRpc_instToJsonErrorCode___closed__6 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__6);
l_Lean_JsonRpc_instToJsonErrorCode___closed__7 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__7);
l_Lean_JsonRpc_instToJsonErrorCode___closed__8 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__8();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__8);
l_Lean_JsonRpc_instToJsonErrorCode___closed__9 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__9();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__9);
l_Lean_JsonRpc_instToJsonErrorCode___closed__10 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__10();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__10);
l_Lean_JsonRpc_instToJsonErrorCode___closed__11 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__11();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__11);
l_Lean_JsonRpc_instToJsonErrorCode___closed__12 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__12();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__12);
l_Lean_JsonRpc_instToJsonErrorCode___closed__13 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__13();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__13);
l_Lean_JsonRpc_instToJsonErrorCode___closed__14 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__14();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__14);
l_Lean_JsonRpc_instToJsonErrorCode___closed__15 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__15();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__15);
l_Lean_JsonRpc_instToJsonErrorCode___closed__16 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__16();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__16);
l_Lean_JsonRpc_instToJsonErrorCode___closed__17 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__17();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__17);
l_Lean_JsonRpc_instToJsonErrorCode___closed__18 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__18();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__18);
l_Lean_JsonRpc_instToJsonErrorCode___closed__19 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__19();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__19);
l_Lean_JsonRpc_instToJsonErrorCode___closed__20 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__20();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__20);
l_Lean_JsonRpc_instToJsonErrorCode___closed__21 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__21();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__21);
l_Lean_JsonRpc_instToJsonErrorCode___closed__22 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__22();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__22);
l_Lean_JsonRpc_instToJsonErrorCode___closed__23 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__23();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__23);
l_Lean_JsonRpc_instToJsonErrorCode___closed__24 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__24();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__24);
l_Lean_JsonRpc_instToJsonErrorCode___closed__25 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__25();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__25);
l_Lean_JsonRpc_instToJsonErrorCode___closed__26 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__26();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__26);
l_Lean_JsonRpc_instToJsonErrorCode___closed__27 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__27();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__27);
l_Lean_JsonRpc_instToJsonErrorCode___closed__28 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__28();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__28);
l_Lean_JsonRpc_instToJsonErrorCode___closed__29 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__29();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__29);
l_Lean_JsonRpc_instToJsonErrorCode___closed__30 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__30();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__30);
l_Lean_JsonRpc_instToJsonErrorCode___closed__31 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__31();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__31);
l_Lean_JsonRpc_instToJsonErrorCode___closed__32 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__32();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__32);
l_Lean_JsonRpc_instToJsonErrorCode___closed__33 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__33();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__33);
l_Lean_JsonRpc_instToJsonErrorCode___closed__34 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__34();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__34);
l_Lean_JsonRpc_instToJsonErrorCode___closed__35 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__35();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__35);
l_Lean_JsonRpc_instToJsonErrorCode___closed__36 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__36();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__36);
l_Lean_JsonRpc_instToJsonErrorCode___closed__37 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__37();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__37);
l_Lean_JsonRpc_instToJsonErrorCode___closed__38 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__38();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__38);
l_Lean_JsonRpc_instToJsonErrorCode___closed__39 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__39();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__39);
l_Lean_JsonRpc_instToJsonErrorCode___closed__40 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__40();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__40);
l_Lean_JsonRpc_instToJsonErrorCode___closed__41 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__41();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__41);
l_Lean_JsonRpc_instToJsonErrorCode___closed__42 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__42();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__42);
l_Lean_JsonRpc_instToJsonErrorCode___closed__43 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__43();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__43);
l_Lean_JsonRpc_instToJsonErrorCode___closed__44 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__44();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__44);
l_Lean_JsonRpc_instInhabitedResponseError___closed__1 = _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedResponseError___closed__1);
l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp = _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp();
lean_mark_persistent(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp);
l_Lean_JsonRpc_instLTRequestID = _init_l_Lean_JsonRpc_instLTRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instLTRequestID);
l_Lean_JsonRpc_instToJsonMessage___closed__1 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__1);
l_Lean_JsonRpc_instToJsonMessage___closed__2 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__2);
l_Lean_JsonRpc_instToJsonMessage___closed__3 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__3);
l_Lean_JsonRpc_instToJsonMessage___closed__4 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__4);
l_Lean_JsonRpc_instToJsonMessage___closed__5 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__5);
l_Lean_JsonRpc_instToJsonMessage___closed__6 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__6);
l_Lean_JsonRpc_instToJsonMessage___closed__7 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__7);
l_Lean_JsonRpc_instToJsonMessage___closed__8 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__8();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__8);
l_Lean_JsonRpc_instToJsonMessage___closed__9 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__9();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__9);
l_Lean_JsonRpc_instToJsonMessage___closed__10 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__10();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__10);
l_Lean_JsonRpc_instToJsonMessage___closed__11 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__11();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__11);
l_Lean_JsonRpc_instToJsonMessage___closed__12 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__12();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__12);
l_Lean_JsonRpc_instToJsonMessage___closed__13 = _init_l_Lean_JsonRpc_instToJsonMessage___closed__13();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonMessage___closed__13);
l_IO_FS_Stream_readMessage___closed__1 = _init_l_IO_FS_Stream_readMessage___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readMessage___closed__1);
l_IO_FS_Stream_readMessage___closed__2 = _init_l_IO_FS_Stream_readMessage___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readMessage___closed__2);
l_IO_FS_Stream_readRequestAs___closed__1 = _init_l_IO_FS_Stream_readRequestAs___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__1);
l_IO_FS_Stream_readRequestAs___closed__2 = _init_l_IO_FS_Stream_readRequestAs___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__2);
l_IO_FS_Stream_readRequestAs___closed__3 = _init_l_IO_FS_Stream_readRequestAs___closed__3();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__3);
l_IO_FS_Stream_readRequestAs___closed__4 = _init_l_IO_FS_Stream_readRequestAs___closed__4();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__4);
l_IO_FS_Stream_readRequestAs___closed__5 = _init_l_IO_FS_Stream_readRequestAs___closed__5();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__5);
l_IO_FS_Stream_readNotificationAs___closed__1 = _init_l_IO_FS_Stream_readNotificationAs___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___closed__1);
l_IO_FS_Stream_readResponseAs___closed__1 = _init_l_IO_FS_Stream_readResponseAs___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readResponseAs___closed__1);
l_IO_FS_Stream_readResponseAs___closed__2 = _init_l_IO_FS_Stream_readResponseAs___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readResponseAs___closed__2);
l_IO_FS_Stream_readResponseAs___closed__3 = _init_l_IO_FS_Stream_readResponseAs___closed__3();
lean_mark_persistent(l_IO_FS_Stream_readResponseAs___closed__3);
l_IO_FS_Stream_readResponseAs___closed__4 = _init_l_IO_FS_Stream_readResponseAs___closed__4();
lean_mark_persistent(l_IO_FS_Stream_readResponseAs___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
