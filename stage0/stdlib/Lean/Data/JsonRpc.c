// Lean compiler output
// Module: Lean.Data.JsonRpc
// Imports: Init.System.IO Lean.Data.RBTree Lean.Data.Json
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
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequestID;
static lean_object* l_Lean_JsonRpc_instFromJsonRequestID___closed__1;
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__13;
lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1295____rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__7;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__16;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__34;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object*);
static lean_object* l_IO_FS_Stream_readMessage___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__6;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOfNatRequestID(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__7;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__5;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__33;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__37;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__28;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__20;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedErrorCode;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__26;
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__2;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__30;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__5;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__12;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__2;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object*);
static lean_object* l_Lean_JsonRpc_instToStringRequestID___closed__1;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__21;
static lean_object* l_IO_FS_Stream_readResponseAs___closed__2;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__17;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__36;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__10;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__1;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__21;
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___closed__2;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1137_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_IO_FS_Stream_readResponseAs___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instLTRequestID;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__9;
static lean_object* l_Lean_JsonRpc_instFromJsonRequestID___closed__2;
static lean_object* l_Lean_JsonRpc_instBEqErrorCode___closed__1;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__3;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__6;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__14;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__13;
lean_object* l_IO_FS_Stream_readJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__10;
static lean_object* l_IO_FS_Stream_readNotificationAs___closed__1;
static lean_object* l_Lean_JsonRpc_instToStringRequestID___closed__2;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__9;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequestID;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__11;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__25;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__31;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1468_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__11;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__24;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx(uint8_t);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__22;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1295_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___closed__6;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__19;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__22;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__35;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__17;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1468____rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readResponseAs___closed__4;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__9;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___rarg(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__18;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__4;
static lean_object* l_Lean_JsonRpc_instInhabitedRequestID___closed__2;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__8;
static lean_object* l_IO_FS_Stream_readResponseAs___closed__3;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___boxed(lean_object*);
lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__15;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__6;
static lean_object* l_IO_FS_Stream_readRequestAs___closed__5;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___closed__4;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__7;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object*);
static lean_object* l_Lean_JsonRpc_instInhabitedResponseError___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___closed__3;
static lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__12;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__23;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__15;
static lean_object* l_IO_FS_Stream_readRequestAs___closed__1;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
static lean_object* l_Lean_JsonRpc_instBEqRequestID___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__2;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_962____rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__3;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__14;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__2;
static lean_object* l_Lean_JsonRpc_instOrdRequestID___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__27;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__1;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__4;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage(lean_object*);
lean_object* l_IO_FS_Stream_writeJson(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__23;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__10;
static lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
static lean_object* l_IO_FS_Stream_readMessage___closed__2;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___rarg(lean_object*);
uint8_t l_Lean_JsonNumber_lt(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Json_Basic_0__Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_23_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__19;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__5;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1137____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__8;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__38;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_962_(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__13;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__1;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__29;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__32;
static lean_object* _init_l_Lean_JsonRpc_instInhabitedRequestID___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedRequestID___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instInhabitedRequestID___closed__2;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(lean_object* x_1, lean_object* x_2) {
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
x_9 = l___private_Lean_Data_Json_Basic_0__Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_23_(x_7, x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36____boxed), 2, 0);
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
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(lean_object* x_1, lean_object* x_2) {
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
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_string_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_4);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_2);
lean_dec(x_1);
x_11 = 2;
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_13);
lean_inc(x_12);
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
lean_dec(x_13);
lean_dec(x_12);
x_18 = 0;
return x_18;
}
}
default: 
{
uint8_t x_19; 
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126_(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonRpc_instOrdRequestID___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_126____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instOrdRequestID() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_JsonRpc_instOrdRequestID___closed__1;
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
static lean_object* _init_l_Lean_JsonRpc_instToStringRequestID___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToStringRequestID___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_JsonRpc_instToStringRequestID___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_string_append(x_4, x_3);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_JsonNumber_toString(x_6);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = l_Lean_JsonRpc_instToStringRequestID___closed__2;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_JsonRpc_ErrorCode_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_JsonRpc_ErrorCode_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
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
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_JsonRpc_ErrorCode_toCtorIdx(x_1);
x_4 = l_Lean_JsonRpc_ErrorCode_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqErrorCode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331____boxed), 2, 0);
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected error code", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__3;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__5;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__7;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__9;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__11;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__13;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__15;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__17;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__19;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32900u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__21;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32901u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__23;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__25;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__27() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__28() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__29() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__30() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__31() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__32() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__33() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__34() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__35() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__36() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__37() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__38() {
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__4;
x_6 = lean_int_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__6;
x_8 = lean_int_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__8;
x_10 = lean_int_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__10;
x_12 = lean_int_dec_eq(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__12;
x_14 = lean_int_dec_eq(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__14;
x_16 = lean_int_dec_eq(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__16;
x_18 = lean_int_dec_eq(x_3, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__18;
x_20 = lean_int_dec_eq(x_3, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__20;
x_22 = lean_int_dec_eq(x_3, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__22;
x_24 = lean_int_dec_eq(x_3, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__24;
x_26 = lean_int_dec_eq(x_3, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__26;
x_28 = lean_int_dec_eq(x_3, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_4, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_32;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__27;
return x_33;
}
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_4, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__28;
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_4, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__29;
return x_41;
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_eq(x_4, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_44;
}
else
{
lean_object* x_45; 
x_45 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__30;
return x_45;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_4, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_48;
}
else
{
lean_object* x_49; 
x_49 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__31;
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_eq(x_4, x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_52;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__32;
return x_53;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_4, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_56;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__33;
return x_57;
}
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_4, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_60;
}
else
{
lean_object* x_61; 
x_61 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__34;
return x_61;
}
}
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_4, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_64;
}
else
{
lean_object* x_65; 
x_65 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__35;
return x_65;
}
}
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_4, x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_68;
}
else
{
lean_object* x_69; 
x_69 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__36;
return x_69;
}
}
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_4, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_72;
}
else
{
lean_object* x_73; 
x_73 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__37;
return x_73;
}
}
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_eq(x_4, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_76;
}
else
{
lean_object* x_77; 
x_77 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__38;
return x_77;
}
}
}
else
{
lean_object* x_78; 
x_78 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_78;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instFromJsonErrorCode(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__6;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__10;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__14;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__16;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__18;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__20;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__22;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__24;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__26;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instToJsonErrorCode___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lean_JsonRpc_instToJsonErrorCode___closed__6;
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = l_Lean_JsonRpc_instToJsonErrorCode___closed__10;
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = l_Lean_JsonRpc_instToJsonErrorCode___closed__14;
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = l_Lean_JsonRpc_instToJsonErrorCode___closed__18;
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = l_Lean_JsonRpc_instToJsonErrorCode___closed__22;
return x_12;
}
default: 
{
lean_object* x_13; 
x_13 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_JsonRpc_instToJsonErrorCode(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_JsonRpc_instInhabitedRequestID___closed__2;
x_3 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instInhabitedRequest___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_962____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_4, x_7);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_962_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_962____rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_962____rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
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
x_13 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_13);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instInhabitedNotification___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1137____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1137_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1137____rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1137____rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
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
x_12 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_instInhabitedRequestID___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instInhabitedResponse___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1295____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_4, x_6);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1295_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1295____rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1295____rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_JsonRpc_instInhabitedRequestID___closed__2;
x_3 = 0;
x_4 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instInhabitedResponseError___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1468____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_4, x_8);
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
x_15 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_331_(x_5, x_9);
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
x_21 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____rarg(x_1, x_7, x_11);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1468_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1468____rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1468____rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_1, x_2);
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonRequestID___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a request id needs to be a number or a string", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonRequestID___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonRequestID___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID(lean_object* x_1) {
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
x_12 = l_Lean_JsonRpc_instFromJsonRequestID___closed__2;
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_ctor_set_tag(x_4, 4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_ctor_set_tag(x_4, 5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_1 = lean_mk_string_unchecked("2.0", 3, 3);
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
x_1 = lean_mk_string_unchecked("jsonrpc", 7, 7);
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
x_1 = lean_mk_string_unchecked("method", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("params", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("id", 2, 2);
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
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("message", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("data", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_ctor_set_tag(x_2, 3);
x_13 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = l_List_appendTR___rarg(x_15, x_11);
x_17 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Json_mkObj(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
x_25 = l_List_appendTR___rarg(x_24, x_11);
x_26 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Json_mkObj(x_27);
return x_28;
}
}
case 1:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_ctor_set_tag(x_2, 2);
x_30 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_2);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_9);
x_33 = l_List_appendTR___rarg(x_32, x_11);
x_34 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Json_mkObj(x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_9);
x_42 = l_List_appendTR___rarg(x_41, x_11);
x_43 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_Json_mkObj(x_44);
return x_45;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_9);
x_48 = l_List_appendTR___rarg(x_47, x_11);
x_49 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Json_mkObj(x_50);
return x_51;
}
}
}
case 1:
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_1);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_1, 0);
x_54 = lean_ctor_get(x_1, 1);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_53);
x_56 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_55);
lean_ctor_set(x_1, 0, x_56);
x_57 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_58 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_57, x_54);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Json_mkObj(x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_1);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_69 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_68, x_64);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Json_mkObj(x_72);
return x_73;
}
}
case 2:
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_1);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_1, 0);
x_76 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_76);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_77);
switch (lean_obj_tag(x_75)) {
case 0:
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_75);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_ctor_set_tag(x_75, 3);
x_80 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_75);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
x_83 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_Json_mkObj(x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
lean_dec(x_75);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_78);
x_91 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_Json_mkObj(x_92);
return x_93;
}
}
case 1:
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_75);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_ctor_set_tag(x_75, 2);
x_95 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_75);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_78);
x_98 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Lean_Json_mkObj(x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_75, 0);
lean_inc(x_101);
lean_dec(x_75);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_78);
x_106 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l_Lean_Json_mkObj(x_107);
return x_108;
}
}
default: 
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_78);
x_111 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = l_Lean_Json_mkObj(x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_1, 0);
x_115 = lean_ctor_get(x_1, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_1);
x_116 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
switch (lean_obj_tag(x_114)) {
case 0:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_114, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_121 = x_114;
} else {
 lean_dec_ref(x_114);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(3, 1, 0);
} else {
 x_122 = x_121;
 lean_ctor_set_tag(x_122, 3);
}
lean_ctor_set(x_122, 0, x_120);
x_123 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_119);
x_126 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = l_Lean_Json_mkObj(x_127);
return x_128;
}
case 1:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_129 = lean_ctor_get(x_114, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_130 = x_114;
} else {
 lean_dec_ref(x_114);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(2, 1, 0);
} else {
 x_131 = x_130;
 lean_ctor_set_tag(x_131, 2);
}
lean_ctor_set(x_131, 0, x_129);
x_132 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_119);
x_135 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = l_Lean_Json_mkObj(x_136);
return x_137;
}
default: 
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_119);
x_140 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_Json_mkObj(x_141);
return x_142;
}
}
}
}
default: 
{
lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_143 = lean_ctor_get(x_1, 0);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_145 = lean_ctor_get(x_1, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_1, 2);
lean_inc(x_146);
lean_dec(x_1);
x_147 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_147, 0, x_145);
x_148 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_153 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_152, x_146);
lean_dec(x_146);
switch (lean_obj_tag(x_143)) {
case 0:
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_143);
if (x_184 == 0)
{
lean_ctor_set_tag(x_143, 3);
x_154 = x_143;
goto block_183;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_143, 0);
lean_inc(x_185);
lean_dec(x_143);
x_186 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_186, 0, x_185);
x_154 = x_186;
goto block_183;
}
}
case 1:
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_143);
if (x_187 == 0)
{
lean_ctor_set_tag(x_143, 2);
x_154 = x_143;
goto block_183;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_143, 0);
lean_inc(x_188);
lean_dec(x_143);
x_189 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_154 = x_189;
goto block_183;
}
}
default: 
{
lean_object* x_190; 
x_190 = lean_box(0);
x_154 = x_190;
goto block_183;
}
}
block_183:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
switch (x_144) {
case 0:
{
lean_object* x_171; 
x_171 = l_Lean_JsonRpc_instToJsonErrorCode___closed__2;
x_157 = x_171;
goto block_170;
}
case 1:
{
lean_object* x_172; 
x_172 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_157 = x_172;
goto block_170;
}
case 2:
{
lean_object* x_173; 
x_173 = l_Lean_JsonRpc_instToJsonErrorCode___closed__6;
x_157 = x_173;
goto block_170;
}
case 3:
{
lean_object* x_174; 
x_174 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_157 = x_174;
goto block_170;
}
case 4:
{
lean_object* x_175; 
x_175 = l_Lean_JsonRpc_instToJsonErrorCode___closed__10;
x_157 = x_175;
goto block_170;
}
case 5:
{
lean_object* x_176; 
x_176 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_157 = x_176;
goto block_170;
}
case 6:
{
lean_object* x_177; 
x_177 = l_Lean_JsonRpc_instToJsonErrorCode___closed__14;
x_157 = x_177;
goto block_170;
}
case 7:
{
lean_object* x_178; 
x_178 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_157 = x_178;
goto block_170;
}
case 8:
{
lean_object* x_179; 
x_179 = l_Lean_JsonRpc_instToJsonErrorCode___closed__18;
x_157 = x_179;
goto block_170;
}
case 9:
{
lean_object* x_180; 
x_180 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_157 = x_180;
goto block_170;
}
case 10:
{
lean_object* x_181; 
x_181 = l_Lean_JsonRpc_instToJsonErrorCode___closed__22;
x_157 = x_181;
goto block_170;
}
default: 
{
lean_object* x_182; 
x_182 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_157 = x_182;
goto block_170;
}
}
block_170:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_158 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_151);
x_161 = l_List_appendTR___rarg(x_160, x_153);
x_162 = l_Lean_Json_mkObj(x_161);
x_163 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_150);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_156);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = l_Lean_Json_mkObj(x_168);
return x_169;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_14 = l_Lean_JsonRpc_instFromJsonRequestID___closed__2;
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__4;
x_8 = lean_int_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__6;
x_10 = lean_int_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__8;
x_12 = lean_int_dec_eq(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__10;
x_14 = lean_int_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__12;
x_16 = lean_int_dec_eq(x_5, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__14;
x_18 = lean_int_dec_eq(x_5, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__16;
x_20 = lean_int_dec_eq(x_5, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__18;
x_22 = lean_int_dec_eq(x_5, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__20;
x_24 = lean_int_dec_eq(x_5, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__22;
x_26 = lean_int_dec_eq(x_5, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__24;
x_28 = lean_int_dec_eq(x_5, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__26;
x_30 = lean_int_dec_eq(x_5, x_29);
lean_dec(x_5);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_6);
x_31 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_6, x_32);
lean_dec(x_6);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_34;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__27;
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_5);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_6, x_36);
lean_dec(x_6);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_38;
}
else
{
lean_object* x_39; 
x_39 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__28;
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_5);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_6, x_40);
lean_dec(x_6);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_42;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__29;
return x_43;
}
}
}
else
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_5);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_6, x_44);
lean_dec(x_6);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_46;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__30;
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_5);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_6, x_48);
lean_dec(x_6);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_50;
}
else
{
lean_object* x_51; 
x_51 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__31;
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_5);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_eq(x_6, x_52);
lean_dec(x_6);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_54;
}
else
{
lean_object* x_55; 
x_55 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__32;
return x_55;
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_5);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_eq(x_6, x_56);
lean_dec(x_6);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_58;
}
else
{
lean_object* x_59; 
x_59 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__33;
return x_59;
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
lean_dec(x_5);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_eq(x_6, x_60);
lean_dec(x_6);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_62;
}
else
{
lean_object* x_63; 
x_63 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__34;
return x_63;
}
}
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_5);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_nat_dec_eq(x_6, x_64);
lean_dec(x_6);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_66;
}
else
{
lean_object* x_67; 
x_67 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__35;
return x_67;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
lean_dec(x_5);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_eq(x_6, x_68);
lean_dec(x_6);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_70;
}
else
{
lean_object* x_71; 
x_71 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__36;
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_5);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_eq(x_6, x_72);
lean_dec(x_6);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_74;
}
else
{
lean_object* x_75; 
x_75 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__37;
return x_75;
}
}
}
else
{
lean_object* x_76; uint8_t x_77; 
lean_dec(x_5);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_eq(x_6, x_76);
lean_dec(x_6);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_78;
}
else
{
lean_object* x_79; 
x_79 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__38;
return x_79;
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_3);
x_80 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected structured object, got '", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(80u);
lean_inc(x_3);
x_5 = l_Lean_Json_pretty(x_3, x_4);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1;
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
x_10 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_11 = lean_string_append(x_9, x_10);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_12 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1;
x_13 = lean_string_append(x_12, x_5);
lean_dec(x_5);
x_14 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
case 3:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(80u);
lean_inc(x_3);
x_18 = l_Lean_Json_pretty(x_3, x_17);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_3, 0);
lean_dec(x_20);
x_21 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1;
x_22 = lean_string_append(x_21, x_18);
lean_dec(x_18);
x_23 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_24 = lean_string_append(x_22, x_23);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_24);
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_25 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1;
x_26 = lean_string_append(x_25, x_18);
lean_dec(x_18);
x_27 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
case 4:
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
lean_object* x_31; 
lean_ctor_set_tag(x_3, 0);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_3);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
lean_dec(x_3);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
case 5:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
lean_object* x_36; 
lean_ctor_set_tag(x_3, 1);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_3);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_3, 0);
lean_inc(x_37);
lean_dec(x_3);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
default: 
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_unsigned_to_nat(80u);
x_41 = l_Lean_Json_pretty(x_3, x_40);
x_42 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only version 2.0 of JSON RPC is supported", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonMessage___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_instToJsonMessage___closed__3;
lean_inc(x_1);
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_9 = x_7;
} else {
 lean_dec_ref(x_7);
 x_9 = lean_box(0);
}
x_10 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_11 = lean_string_dec_eq(x_8, x_10);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = l_Lean_JsonRpc_instFromJsonMessage___closed__2;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_60; 
x_13 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
lean_inc(x_1);
x_14 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_104; 
x_104 = lean_box(0);
x_60 = x_104;
goto block_103;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_14, 0);
lean_inc(x_105);
x_106 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_inc(x_1);
x_107 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_107);
lean_dec(x_105);
x_108 = lean_box(0);
x_60 = x_108;
goto block_103;
}
else
{
uint8_t x_109; 
lean_dec(x_14);
lean_dec(x_9);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_107, 0);
x_111 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_112 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_111);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
lean_free_object(x_107);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_112, 0);
lean_dec(x_114);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_105);
lean_ctor_set(x_116, 1, x_110);
lean_ctor_set(x_116, 2, x_115);
lean_ctor_set_tag(x_112, 1);
lean_ctor_set(x_112, 0, x_116);
return x_112;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_112);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_118, 0, x_105);
lean_ctor_set(x_118, 1, x_110);
lean_ctor_set(x_118, 2, x_117);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_112);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_112, 0);
lean_ctor_set(x_107, 0, x_121);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_105);
lean_ctor_set(x_122, 1, x_110);
lean_ctor_set(x_122, 2, x_107);
lean_ctor_set(x_112, 0, x_122);
return x_112;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_112, 0);
lean_inc(x_123);
lean_dec(x_112);
lean_ctor_set(x_107, 0, x_123);
x_124 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_124, 0, x_105);
lean_ctor_set(x_124, 1, x_110);
lean_ctor_set(x_124, 2, x_107);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_107, 0);
lean_inc(x_126);
lean_dec(x_107);
x_127 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_128 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_129 = x_128;
} else {
 lean_dec_ref(x_128);
 x_129 = lean_box(0);
}
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_131, 0, x_105);
lean_ctor_set(x_131, 1, x_126);
lean_ctor_set(x_131, 2, x_130);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_129;
 lean_ctor_set_tag(x_132, 1);
}
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_128, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_134 = x_128;
} else {
 lean_dec_ref(x_128);
 x_134 = lean_box(0);
}
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_133);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_105);
lean_ctor_set(x_136, 1, x_126);
lean_ctor_set(x_136, 2, x_135);
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_137 = x_134;
}
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
}
block_59:
{
lean_dec(x_15);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_21 = l_Lean_Json_getObjVal_x3f(x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_9);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
lean_inc(x_25);
x_27 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_25, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
lean_inc(x_25);
x_33 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_25, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_9);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_39 = l_Lean_Json_getObjVal_x3f(x_25, x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_9);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_43, 0, x_19);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_unbox(x_31);
lean_dec(x_31);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_44);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
lean_dec(x_39);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_46, 0, x_19);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_unbox(x_31);
lean_dec(x_31);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_47);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_39, 0);
if (lean_is_scalar(x_9)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_9;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_52, 0, x_19);
lean_ctor_set(x_52, 1, x_37);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_unbox(x_31);
lean_dec(x_31);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_53);
lean_ctor_set(x_39, 0, x_52);
return x_39;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
lean_dec(x_39);
if (lean_is_scalar(x_9)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_9;
 lean_ctor_set_tag(x_55, 1);
}
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_56, 0, x_19);
lean_ctor_set(x_56, 1, x_37);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_unbox(x_31);
lean_dec(x_31);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_57);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
}
}
}
}
}
block_103:
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_60);
x_61 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_inc(x_1);
x_62 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_dec(x_62);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_63; 
x_63 = lean_box(0);
x_15 = x_63;
goto block_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_14, 0);
lean_inc(x_64);
x_65 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_inc(x_1);
x_66 = l_Lean_Json_getObjVal_x3f(x_1, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
lean_dec(x_66);
lean_dec(x_64);
x_67 = lean_box(0);
x_15 = x_67;
goto block_59;
}
else
{
uint8_t x_68; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 0);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_66, 0, x_70);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_64);
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
uint8_t x_74; 
lean_dec(x_14);
lean_dec(x_9);
x_74 = !lean_is_exclusive(x_62);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_62, 0);
x_76 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_77 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_76);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
lean_free_object(x_62);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set_tag(x_77, 1);
lean_ctor_set(x_77, 0, x_81);
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_77);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_77, 0);
lean_ctor_set(x_62, 0, x_86);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_75);
lean_ctor_set(x_87, 1, x_62);
lean_ctor_set(x_77, 0, x_87);
return x_77;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_77, 0);
lean_inc(x_88);
lean_dec(x_77);
lean_ctor_set(x_62, 0, x_88);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_75);
lean_ctor_set(x_89, 1, x_62);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_62, 0);
lean_inc(x_91);
lean_dec(x_62);
x_92 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_93 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_94 = x_93;
} else {
 lean_dec_ref(x_93);
 x_94 = lean_box(0);
}
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_95);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_94;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_99 = x_93;
} else {
 lean_dec_ref(x_93);
 x_99 = lean_box(0);
}
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_98);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_100);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
}
}
}
else
{
lean_object* x_138; 
lean_dec(x_7);
lean_dec(x_1);
x_138 = l_Lean_JsonRpc_instFromJsonMessage___closed__2;
return x_138;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not a notification", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_96; lean_object* x_97; 
x_96 = l_Lean_JsonRpc_instToJsonMessage___closed__3;
lean_inc(x_2);
x_97 = l_Lean_Json_getObjVal_x3f(x_2, x_96);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
return x_97;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
else
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_97, 0);
lean_inc(x_101);
lean_dec(x_97);
if (lean_obj_tag(x_101) == 3)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_104 = lean_string_dec_eq(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_2);
lean_dec(x_1);
x_105 = l_Lean_JsonRpc_instFromJsonMessage___closed__2;
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_144; 
x_106 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
lean_inc(x_2);
x_107 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_2, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_165; 
x_165 = lean_box(0);
x_144 = x_165;
goto block_164;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_107, 0);
lean_inc(x_166);
x_167 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_inc(x_2);
x_168 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_2, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
lean_dec(x_168);
lean_dec(x_166);
x_169 = lean_box(0);
x_144 = x_169;
goto block_164;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_107);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_172 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_2, x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_172);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_174, 0, x_166);
lean_ctor_set(x_174, 1, x_170);
lean_ctor_set(x_174, 2, x_173);
x_3 = x_174;
goto block_95;
}
else
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_172);
if (x_175 == 0)
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_176, 0, x_166);
lean_ctor_set(x_176, 1, x_170);
lean_ctor_set(x_176, 2, x_172);
x_3 = x_176;
goto block_95;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_172, 0);
lean_inc(x_177);
lean_dec(x_172);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_179, 0, x_166);
lean_ctor_set(x_179, 1, x_170);
lean_ctor_set(x_179, 2, x_178);
x_3 = x_179;
goto block_95;
}
}
}
}
block_143:
{
lean_dec(x_108);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_109; 
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
return x_107;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
lean_dec(x_107);
x_113 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_114 = l_Lean_Json_getObjVal_x3f(x_2, x_113);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
lean_dec(x_112);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
return x_114;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
lean_dec(x_114);
x_119 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
lean_inc(x_118);
x_120 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_118, x_119);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
lean_dec(x_118);
lean_dec(x_112);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
return x_120;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_120, 0);
lean_inc(x_124);
lean_dec(x_120);
x_125 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
lean_inc(x_118);
x_126 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_118, x_125);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
lean_dec(x_124);
lean_dec(x_118);
lean_dec(x_112);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
return x_126;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
lean_dec(x_126);
x_131 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_132 = l_Lean_Json_getObjVal_x3f(x_118, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_132);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_134, 0, x_112);
lean_ctor_set(x_134, 1, x_130);
lean_ctor_set(x_134, 2, x_133);
x_135 = lean_unbox(x_124);
lean_dec(x_124);
lean_ctor_set_uint8(x_134, sizeof(void*)*3, x_135);
x_3 = x_134;
goto block_95;
}
else
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_132);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_137, 0, x_112);
lean_ctor_set(x_137, 1, x_130);
lean_ctor_set(x_137, 2, x_132);
x_138 = lean_unbox(x_124);
lean_dec(x_124);
lean_ctor_set_uint8(x_137, sizeof(void*)*3, x_138);
x_3 = x_137;
goto block_95;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_132, 0);
lean_inc(x_139);
lean_dec(x_132);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_141, 0, x_112);
lean_ctor_set(x_141, 1, x_130);
lean_ctor_set(x_141, 2, x_140);
x_142 = lean_unbox(x_124);
lean_dec(x_124);
lean_ctor_set_uint8(x_141, sizeof(void*)*3, x_142);
x_3 = x_141;
goto block_95;
}
}
}
}
}
}
}
block_164:
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_144);
x_145 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_inc(x_2);
x_146 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_2, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_dec(x_146);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_147; 
x_147 = lean_box(0);
x_108 = x_147;
goto block_143;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_107, 0);
lean_inc(x_148);
x_149 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_inc(x_2);
x_150 = l_Lean_Json_getObjVal_x3f(x_2, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
lean_dec(x_150);
lean_dec(x_148);
x_151 = lean_box(0);
x_108 = x_151;
goto block_143;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_107);
lean_dec(x_2);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_148);
lean_ctor_set(x_153, 1, x_152);
x_3 = x_153;
goto block_95;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_107);
x_154 = lean_ctor_get(x_146, 0);
lean_inc(x_154);
lean_dec(x_146);
x_155 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_156 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_2, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_156);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_157);
x_3 = x_158;
goto block_95;
}
else
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_156);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_156);
x_3 = x_160;
goto block_95;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_156, 0);
lean_inc(x_161);
lean_dec(x_156);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_154);
lean_ctor_set(x_163, 1, x_162);
x_3 = x_163;
goto block_95;
}
}
}
}
}
}
else
{
lean_object* x_180; 
lean_dec(x_101);
lean_dec(x_2);
lean_dec(x_1);
x_180 = l_Lean_JsonRpc_instFromJsonMessage___closed__2;
return x_180;
}
}
block_95:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_free_object(x_3);
lean_dec(x_6);
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
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_3);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = lean_apply_1(x_1, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_24 = x_19;
} else {
 lean_dec_ref(x_19);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
lean_dec(x_4);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; 
lean_ctor_set_tag(x_27, 4);
x_32 = lean_apply_1(x_1, x_27);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_free_object(x_3);
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_32, 0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_32, 0, x_3);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_38);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_3);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 0);
lean_inc(x_40);
lean_dec(x_27);
x_41 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_apply_1(x_1, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_3);
lean_dec(x_29);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_47 = x_42;
} else {
 lean_dec_ref(x_42);
 x_47 = lean_box(0);
}
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_46);
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_3);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_3, 0);
lean_inc(x_49);
lean_dec(x_3);
x_50 = lean_ctor_get(x_27, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_51 = x_27;
} else {
 lean_dec_ref(x_27);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(4, 1, 0);
} else {
 x_52 = x_51;
 lean_ctor_set_tag(x_52, 4);
}
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_apply_1(x_1, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_49);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_58 = x_53;
} else {
 lean_dec_ref(x_53);
 x_58 = lean_box(0);
}
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_57);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_3);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_3, 0);
x_63 = lean_ctor_get(x_3, 1);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_27);
if (x_64 == 0)
{
lean_object* x_65; 
lean_ctor_set_tag(x_27, 5);
x_65 = lean_apply_1(x_1, x_27);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
lean_free_object(x_3);
lean_dec(x_62);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_65);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_65, 0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_70);
lean_ctor_set(x_65, 0, x_3);
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
lean_dec(x_65);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_71);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_3);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_27, 0);
lean_inc(x_73);
lean_dec(x_27);
x_74 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_apply_1(x_1, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_free_object(x_3);
lean_dec(x_62);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_80 = x_75;
} else {
 lean_dec_ref(x_75);
 x_80 = lean_box(0);
}
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_79);
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_3);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_3, 0);
lean_inc(x_82);
lean_dec(x_3);
x_83 = lean_ctor_get(x_27, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_84 = x_27;
} else {
 lean_dec_ref(x_27);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(5, 1, 0);
} else {
 x_85 = x_84;
 lean_ctor_set_tag(x_85, 5);
}
lean_ctor_set(x_85, 0, x_83);
x_86 = lean_apply_1(x_1, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_82);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 1, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_91 = x_86;
} else {
 lean_dec_ref(x_86);
 x_91 = lean_box(0);
}
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_82);
lean_ctor_set(x_92, 1, x_90);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
}
}
else
{
lean_object* x_94; 
lean_dec(x_3);
lean_dec(x_1);
x_94 = l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__2;
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("JSON '", 6, 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readMessage___closed__2() {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_20; lean_object* x_21; 
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
x_20 = l_Lean_JsonRpc_instToJsonMessage___closed__3;
lean_inc(x_5);
x_21 = l_Lean_Json_getObjVal_x3f(x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_8 = x_22;
goto block_19;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 3)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_26 = lean_string_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_JsonRpc_instFromJsonMessage___closed__1;
x_8 = x_27;
goto block_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_61; 
x_28 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
lean_inc(x_5);
x_29 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_5, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_86; 
x_86 = lean_box(0);
x_61 = x_86;
goto block_85;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_29, 0);
lean_inc(x_87);
x_88 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_inc(x_5);
x_89 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_5, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
lean_dec(x_89);
lean_dec(x_87);
x_90 = lean_box(0);
x_61 = x_90;
goto block_85;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_29);
lean_dec(x_7);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_93 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_5, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_93);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_87);
lean_ctor_set(x_95, 1, x_91);
lean_ctor_set(x_95, 2, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_6);
return x_96;
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_93);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_91);
lean_ctor_set(x_98, 2, x_93);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_6);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_100);
lean_dec(x_93);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_102, 0, x_87);
lean_ctor_set(x_102, 1, x_91);
lean_ctor_set(x_102, 2, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_6);
return x_103;
}
}
}
}
block_60:
{
lean_dec(x_30);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_8 = x_31;
goto block_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
lean_inc(x_5);
x_34 = l_Lean_Json_getObjVal_x3f(x_5, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_8 = x_35;
goto block_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
lean_inc(x_36);
x_38 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_36, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_32);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_8 = x_39;
goto block_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
lean_inc(x_36);
x_42 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_36, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_32);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_8 = x_43;
goto block_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_7);
lean_dec(x_5);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_46 = l_Lean_Json_getObjVal_x3f(x_36, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
lean_dec(x_46);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_48, 0, x_32);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_6);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_52 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_52, 0, x_32);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_46);
x_53 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_6);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_46, 0);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_57, 0, x_32);
lean_ctor_set(x_57, 1, x_44);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_6);
return x_59;
}
}
}
}
}
}
}
block_85:
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_61);
x_62 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_inc(x_5);
x_63 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_5, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_dec(x_63);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_64; 
x_64 = lean_box(0);
x_30 = x_64;
goto block_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_29, 0);
lean_inc(x_65);
x_66 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_inc(x_5);
x_67 = l_Lean_Json_getObjVal_x3f(x_5, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
lean_dec(x_67);
lean_dec(x_65);
x_68 = lean_box(0);
x_30 = x_68;
goto block_60;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_5);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_6);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_29);
lean_dec(x_7);
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
lean_dec(x_63);
x_73 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_74 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_5, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_74);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_6);
return x_77;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_72);
lean_ctor_set(x_79, 1, x_74);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_6);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_6);
return x_84;
}
}
}
}
}
}
else
{
lean_object* x_104; 
lean_dec(x_23);
x_104 = l_Lean_JsonRpc_instFromJsonMessage___closed__1;
x_8 = x_104;
goto block_19;
}
}
block_19:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Json_compress(x_5);
x_10 = l_IO_FS_Stream_readMessage___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_IO_FS_Stream_readMessage___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_8);
lean_dec(x_8);
x_15 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
if (lean_is_scalar(x_7)) {
 x_18 = lean_alloc_ctor(1, 2, 0);
} else {
 x_18 = x_7;
 lean_ctor_set_tag(x_18, 1);
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_4);
if (x_105 == 0)
{
return x_4;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_4, 0);
x_107 = lean_ctor_get(x_4, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_4);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
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
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected method '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', got method '", 15, 15);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unexpected param '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' for method '", 14, 14);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected JSON-RPC request, got: '", 33, 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 x_14 = x_8;
} else {
 lean_dec_ref(x_8);
 x_14 = lean_box(0);
}
x_15 = lean_string_dec_eq(x_12, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
x_16 = l_IO_FS_Stream_readRequestAs___closed__1;
x_17 = lean_string_append(x_16, x_3);
lean_dec(x_3);
x_18 = l_IO_FS_Stream_readRequestAs___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_12);
lean_dec(x_12);
x_21 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
if (lean_is_scalar(x_10)) {
 x_24 = lean_alloc_ctor(1, 2, 0);
} else {
 x_24 = x_10;
 lean_ctor_set_tag(x_24, 1);
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_25 = x_59;
goto block_58;
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_13, 0);
lean_inc(x_60);
lean_dec(x_13);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_ctor_set_tag(x_60, 4);
x_25 = x_60;
goto block_58;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_25 = x_63;
goto block_58;
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_ctor_set_tag(x_60, 5);
x_25 = x_60;
goto block_58;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_25 = x_66;
goto block_58;
}
}
}
block_58:
{
lean_object* x_26; 
lean_inc(x_25);
x_26 = lean_apply_1(x_5, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_11);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Json_compress(x_25);
x_30 = l_IO_FS_Stream_readRequestAs___closed__3;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_IO_FS_Stream_readRequestAs___closed__4;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_3);
lean_dec(x_3);
x_35 = l_IO_FS_Stream_readRequestAs___closed__5;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_28);
lean_dec(x_28);
x_38 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_39 = lean_string_append(x_37, x_38);
lean_ctor_set_tag(x_26, 18);
lean_ctor_set(x_26, 0, x_39);
if (lean_is_scalar(x_10)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_10;
 lean_ctor_set_tag(x_40, 1);
}
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_9);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
lean_dec(x_26);
x_42 = l_Lean_Json_compress(x_25);
x_43 = l_IO_FS_Stream_readRequestAs___closed__3;
x_44 = lean_string_append(x_43, x_42);
lean_dec(x_42);
x_45 = l_IO_FS_Stream_readRequestAs___closed__4;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_string_append(x_46, x_3);
lean_dec(x_3);
x_48 = l_IO_FS_Stream_readRequestAs___closed__5;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_string_append(x_49, x_41);
lean_dec(x_41);
x_51 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_10)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_10;
 lean_ctor_set_tag(x_54, 1);
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_9);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_25);
x_55 = lean_ctor_get(x_26, 0);
lean_inc(x_55);
lean_dec(x_26);
if (lean_is_scalar(x_14)) {
 x_56 = lean_alloc_ctor(0, 3, 0);
} else {
 x_56 = x_14;
}
lean_ctor_set(x_56, 0, x_11);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_55);
if (lean_is_scalar(x_10)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_10;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_9);
return x_57;
}
}
}
}
case 1:
{
uint8_t x_67; 
lean_dec(x_5);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_7);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_7, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_8);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_70 = lean_ctor_get(x_8, 0);
x_71 = lean_ctor_get(x_8, 1);
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_70);
x_73 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 1, x_72);
lean_ctor_set(x_8, 0, x_73);
x_74 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_75 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_74, x_71);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_8);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lean_Json_mkObj(x_78);
x_80 = l_Lean_Json_compress(x_79);
x_81 = l_IO_FS_Stream_readRequestAs___closed__6;
x_82 = lean_string_append(x_81, x_80);
lean_dec(x_80);
x_83 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_85);
return x_7;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_86 = lean_ctor_get(x_8, 0);
x_87 = lean_ctor_get(x_8, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_8);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_86);
x_89 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_92 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_91, x_87);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Json_mkObj(x_95);
x_97 = l_Lean_Json_compress(x_96);
x_98 = l_IO_FS_Stream_readRequestAs___closed__6;
x_99 = lean_string_append(x_98, x_97);
lean_dec(x_97);
x_100 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_102);
return x_7;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_103 = lean_ctor_get(x_7, 1);
lean_inc(x_103);
lean_dec(x_7);
x_104 = lean_ctor_get(x_8, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_8, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_106 = x_8;
} else {
 lean_dec_ref(x_8);
 x_106 = lean_box(0);
}
x_107 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_107, 0, x_104);
x_108 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_106;
 lean_ctor_set_tag(x_109, 0);
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_111 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_110, x_105);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l_Lean_Json_mkObj(x_114);
x_116 = l_Lean_Json_compress(x_115);
x_117 = l_IO_FS_Stream_readRequestAs___closed__6;
x_118 = lean_string_append(x_117, x_116);
lean_dec(x_116);
x_119 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_103);
return x_122;
}
}
case 2:
{
uint8_t x_123; 
lean_dec(x_5);
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_7);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_7, 0);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_8);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_8, 0);
x_127 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_127);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_8);
lean_ctor_set(x_129, 1, x_128);
switch (lean_obj_tag(x_126)) {
case 0:
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_126);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_ctor_set_tag(x_126, 3);
x_131 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_126);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_129);
x_134 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l_Lean_Json_mkObj(x_135);
x_137 = l_Lean_Json_compress(x_136);
x_138 = l_IO_FS_Stream_readRequestAs___closed__6;
x_139 = lean_string_append(x_138, x_137);
lean_dec(x_137);
x_140 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_141 = lean_string_append(x_139, x_140);
x_142 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_142);
return x_7;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_143 = lean_ctor_get(x_126, 0);
lean_inc(x_143);
lean_dec(x_126);
x_144 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_129);
x_148 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = l_Lean_Json_mkObj(x_149);
x_151 = l_Lean_Json_compress(x_150);
x_152 = l_IO_FS_Stream_readRequestAs___closed__6;
x_153 = lean_string_append(x_152, x_151);
lean_dec(x_151);
x_154 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_155 = lean_string_append(x_153, x_154);
x_156 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_156);
return x_7;
}
}
case 1:
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_126);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_ctor_set_tag(x_126, 2);
x_158 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_126);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_129);
x_161 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Lean_Json_mkObj(x_162);
x_164 = l_Lean_Json_compress(x_163);
x_165 = l_IO_FS_Stream_readRequestAs___closed__6;
x_166 = lean_string_append(x_165, x_164);
lean_dec(x_164);
x_167 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_168 = lean_string_append(x_166, x_167);
x_169 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_169);
return x_7;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_170 = lean_ctor_get(x_126, 0);
lean_inc(x_170);
lean_dec(x_126);
x_171 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_129);
x_175 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
x_177 = l_Lean_Json_mkObj(x_176);
x_178 = l_Lean_Json_compress(x_177);
x_179 = l_IO_FS_Stream_readRequestAs___closed__6;
x_180 = lean_string_append(x_179, x_178);
lean_dec(x_178);
x_181 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_182 = lean_string_append(x_180, x_181);
x_183 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_183);
return x_7;
}
}
default: 
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_184 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_129);
x_186 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
x_188 = l_Lean_Json_mkObj(x_187);
x_189 = l_Lean_Json_compress(x_188);
x_190 = l_IO_FS_Stream_readRequestAs___closed__6;
x_191 = lean_string_append(x_190, x_189);
lean_dec(x_189);
x_192 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_193 = lean_string_append(x_191, x_192);
x_194 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_194);
return x_7;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_195 = lean_ctor_get(x_8, 0);
x_196 = lean_ctor_get(x_8, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_8);
x_197 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
switch (lean_obj_tag(x_195)) {
case 0:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_201 = lean_ctor_get(x_195, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_202 = x_195;
} else {
 lean_dec_ref(x_195);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(3, 1, 0);
} else {
 x_203 = x_202;
 lean_ctor_set_tag(x_203, 3);
}
lean_ctor_set(x_203, 0, x_201);
x_204 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_200);
x_207 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = l_Lean_Json_mkObj(x_208);
x_210 = l_Lean_Json_compress(x_209);
x_211 = l_IO_FS_Stream_readRequestAs___closed__6;
x_212 = lean_string_append(x_211, x_210);
lean_dec(x_210);
x_213 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_214 = lean_string_append(x_212, x_213);
x_215 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_215);
return x_7;
}
case 1:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_216 = lean_ctor_get(x_195, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_217 = x_195;
} else {
 lean_dec_ref(x_195);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(2, 1, 0);
} else {
 x_218 = x_217;
 lean_ctor_set_tag(x_218, 2);
}
lean_ctor_set(x_218, 0, x_216);
x_219 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_200);
x_222 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
x_224 = l_Lean_Json_mkObj(x_223);
x_225 = l_Lean_Json_compress(x_224);
x_226 = l_IO_FS_Stream_readRequestAs___closed__6;
x_227 = lean_string_append(x_226, x_225);
lean_dec(x_225);
x_228 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_229 = lean_string_append(x_227, x_228);
x_230 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_230);
return x_7;
}
default: 
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_231 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_200);
x_233 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = l_Lean_Json_mkObj(x_234);
x_236 = l_Lean_Json_compress(x_235);
x_237 = l_IO_FS_Stream_readRequestAs___closed__6;
x_238 = lean_string_append(x_237, x_236);
lean_dec(x_236);
x_239 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_240 = lean_string_append(x_238, x_239);
x_241 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_241);
return x_7;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_242 = lean_ctor_get(x_7, 1);
lean_inc(x_242);
lean_dec(x_7);
x_243 = lean_ctor_get(x_8, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_8, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_245 = x_8;
} else {
 lean_dec_ref(x_8);
 x_245 = lean_box(0);
}
x_246 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_245;
 lean_ctor_set_tag(x_247, 0);
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
x_248 = lean_box(0);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
switch (lean_obj_tag(x_243)) {
case 0:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_250 = lean_ctor_get(x_243, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_251 = x_243;
} else {
 lean_dec_ref(x_243);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(3, 1, 0);
} else {
 x_252 = x_251;
 lean_ctor_set_tag(x_252, 3);
}
lean_ctor_set(x_252, 0, x_250);
x_253 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_252);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_249);
x_256 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_255);
x_258 = l_Lean_Json_mkObj(x_257);
x_259 = l_Lean_Json_compress(x_258);
x_260 = l_IO_FS_Stream_readRequestAs___closed__6;
x_261 = lean_string_append(x_260, x_259);
lean_dec(x_259);
x_262 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_263 = lean_string_append(x_261, x_262);
x_264 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_264, 0, x_263);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_242);
return x_265;
}
case 1:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_266 = lean_ctor_get(x_243, 0);
lean_inc(x_266);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_267 = x_243;
} else {
 lean_dec_ref(x_243);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(2, 1, 0);
} else {
 x_268 = x_267;
 lean_ctor_set_tag(x_268, 2);
}
lean_ctor_set(x_268, 0, x_266);
x_269 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_249);
x_272 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
x_274 = l_Lean_Json_mkObj(x_273);
x_275 = l_Lean_Json_compress(x_274);
x_276 = l_IO_FS_Stream_readRequestAs___closed__6;
x_277 = lean_string_append(x_276, x_275);
lean_dec(x_275);
x_278 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_279 = lean_string_append(x_277, x_278);
x_280 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_280, 0, x_279);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_242);
return x_281;
}
default: 
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_282 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_249);
x_284 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_283);
x_286 = l_Lean_Json_mkObj(x_285);
x_287 = l_Lean_Json_compress(x_286);
x_288 = l_IO_FS_Stream_readRequestAs___closed__6;
x_289 = lean_string_append(x_288, x_287);
lean_dec(x_287);
x_290 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_291 = lean_string_append(x_289, x_290);
x_292 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_292, 0, x_291);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_242);
return x_293;
}
}
}
}
default: 
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_5);
lean_dec(x_3);
x_294 = lean_ctor_get(x_7, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_295 = x_7;
} else {
 lean_dec_ref(x_7);
 x_295 = lean_box(0);
}
x_296 = lean_ctor_get(x_8, 0);
lean_inc(x_296);
x_297 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_298 = lean_ctor_get(x_8, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_8, 2);
lean_inc(x_299);
lean_dec(x_8);
x_300 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_300, 0, x_298);
x_301 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_300);
x_303 = lean_box(0);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_306 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_305, x_299);
lean_dec(x_299);
switch (lean_obj_tag(x_296)) {
case 0:
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_296);
if (x_344 == 0)
{
lean_ctor_set_tag(x_296, 3);
x_307 = x_296;
goto block_343;
}
else
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_ctor_get(x_296, 0);
lean_inc(x_345);
lean_dec(x_296);
x_346 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_346, 0, x_345);
x_307 = x_346;
goto block_343;
}
}
case 1:
{
uint8_t x_347; 
x_347 = !lean_is_exclusive(x_296);
if (x_347 == 0)
{
lean_ctor_set_tag(x_296, 2);
x_307 = x_296;
goto block_343;
}
else
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_296, 0);
lean_inc(x_348);
lean_dec(x_296);
x_349 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_349, 0, x_348);
x_307 = x_349;
goto block_343;
}
}
default: 
{
lean_object* x_350; 
x_350 = lean_box(0);
x_307 = x_350;
goto block_343;
}
}
block_343:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_307);
switch (x_297) {
case 0:
{
lean_object* x_331; 
x_331 = l_Lean_JsonRpc_instToJsonErrorCode___closed__2;
x_310 = x_331;
goto block_330;
}
case 1:
{
lean_object* x_332; 
x_332 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_310 = x_332;
goto block_330;
}
case 2:
{
lean_object* x_333; 
x_333 = l_Lean_JsonRpc_instToJsonErrorCode___closed__6;
x_310 = x_333;
goto block_330;
}
case 3:
{
lean_object* x_334; 
x_334 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_310 = x_334;
goto block_330;
}
case 4:
{
lean_object* x_335; 
x_335 = l_Lean_JsonRpc_instToJsonErrorCode___closed__10;
x_310 = x_335;
goto block_330;
}
case 5:
{
lean_object* x_336; 
x_336 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_310 = x_336;
goto block_330;
}
case 6:
{
lean_object* x_337; 
x_337 = l_Lean_JsonRpc_instToJsonErrorCode___closed__14;
x_310 = x_337;
goto block_330;
}
case 7:
{
lean_object* x_338; 
x_338 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_310 = x_338;
goto block_330;
}
case 8:
{
lean_object* x_339; 
x_339 = l_Lean_JsonRpc_instToJsonErrorCode___closed__18;
x_310 = x_339;
goto block_330;
}
case 9:
{
lean_object* x_340; 
x_340 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_310 = x_340;
goto block_330;
}
case 10:
{
lean_object* x_341; 
x_341 = l_Lean_JsonRpc_instToJsonErrorCode___closed__22;
x_310 = x_341;
goto block_330;
}
default: 
{
lean_object* x_342; 
x_342 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_310 = x_342;
goto block_330;
}
}
block_330:
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_311 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_310);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_304);
x_314 = l_List_appendTR___rarg(x_313, x_306);
x_315 = l_Lean_Json_mkObj(x_314);
x_316 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_315);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_303);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_309);
lean_ctor_set(x_319, 1, x_318);
x_320 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_319);
x_322 = l_Lean_Json_mkObj(x_321);
x_323 = l_Lean_Json_compress(x_322);
x_324 = l_IO_FS_Stream_readRequestAs___closed__6;
x_325 = lean_string_append(x_324, x_323);
lean_dec(x_323);
x_326 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_327 = lean_string_append(x_325, x_326);
x_328 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_328, 0, x_327);
if (lean_is_scalar(x_295)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_295;
 lean_ctor_set_tag(x_329, 1);
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_294);
return x_329;
}
}
}
}
}
else
{
uint8_t x_351; 
lean_dec(x_5);
lean_dec(x_3);
x_351 = !lean_is_exclusive(x_7);
if (x_351 == 0)
{
return x_7;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_7, 0);
x_353 = lean_ctor_get(x_7, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_7);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
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
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected JSON-RPC notification, got: '", 38, 38);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
switch (lean_obj_tag(x_11)) {
case 0:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_ctor_set_tag(x_11, 3);
x_22 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
x_25 = l_List_appendTR___rarg(x_24, x_20);
x_26 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Json_mkObj(x_27);
x_29 = l_Lean_Json_compress(x_28);
x_30 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_34);
return x_7;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_18);
x_40 = l_List_appendTR___rarg(x_39, x_20);
x_41 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Json_mkObj(x_42);
x_44 = l_Lean_Json_compress(x_43);
x_45 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_49);
return x_7;
}
}
case 1:
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_11);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_ctor_set_tag(x_11, 2);
x_51 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_11);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_18);
x_54 = l_List_appendTR___rarg(x_53, x_20);
x_55 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Json_mkObj(x_56);
x_58 = l_Lean_Json_compress(x_57);
x_59 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_61 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_63);
return x_7;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_64 = lean_ctor_get(x_11, 0);
lean_inc(x_64);
lean_dec(x_11);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_18);
x_69 = l_List_appendTR___rarg(x_68, x_20);
x_70 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Json_mkObj(x_71);
x_73 = l_Lean_Json_compress(x_72);
x_74 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_78);
return x_7;
}
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_79 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_18);
x_81 = l_List_appendTR___rarg(x_80, x_20);
x_82 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_Json_mkObj(x_83);
x_85 = l_Lean_Json_compress(x_84);
x_86 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_90);
return x_7;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_91 = lean_ctor_get(x_7, 1);
lean_inc(x_91);
lean_dec(x_7);
x_92 = lean_ctor_get(x_8, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_8, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_8, 2);
lean_inc(x_94);
lean_dec(x_8);
x_95 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_95, 0, x_93);
x_96 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_101 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_100, x_94);
switch (lean_obj_tag(x_92)) {
case 0:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_102 = lean_ctor_get(x_92, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_103 = x_92;
} else {
 lean_dec_ref(x_92);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(3, 1, 0);
} else {
 x_104 = x_103;
 lean_ctor_set_tag(x_104, 3);
}
lean_ctor_set(x_104, 0, x_102);
x_105 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_99);
x_108 = l_List_appendTR___rarg(x_107, x_101);
x_109 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_Json_mkObj(x_110);
x_112 = l_Lean_Json_compress(x_111);
x_113 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_114 = lean_string_append(x_113, x_112);
lean_dec(x_112);
x_115 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_91);
return x_118;
}
case 1:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_119 = lean_ctor_get(x_92, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_120 = x_92;
} else {
 lean_dec_ref(x_92);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(2, 1, 0);
} else {
 x_121 = x_120;
 lean_ctor_set_tag(x_121, 2);
}
lean_ctor_set(x_121, 0, x_119);
x_122 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_99);
x_125 = l_List_appendTR___rarg(x_124, x_101);
x_126 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = l_Lean_Json_mkObj(x_127);
x_129 = l_Lean_Json_compress(x_128);
x_130 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
x_132 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_133 = lean_string_append(x_131, x_132);
x_134 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_91);
return x_135;
}
default: 
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_136 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_99);
x_138 = l_List_appendTR___rarg(x_137, x_101);
x_139 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Lean_Json_mkObj(x_140);
x_142 = l_Lean_Json_compress(x_141);
x_143 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_144 = lean_string_append(x_143, x_142);
lean_dec(x_142);
x_145 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_146 = lean_string_append(x_144, x_145);
x_147 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_91);
return x_148;
}
}
}
}
case 1:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_149 = lean_ctor_get(x_7, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_150 = x_7;
} else {
 lean_dec_ref(x_7);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_8, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_8, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_153 = x_8;
} else {
 lean_dec_ref(x_8);
 x_153 = lean_box(0);
}
x_154 = lean_string_dec_eq(x_151, x_3);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_5);
x_155 = l_IO_FS_Stream_readRequestAs___closed__1;
x_156 = lean_string_append(x_155, x_3);
lean_dec(x_3);
x_157 = l_IO_FS_Stream_readRequestAs___closed__2;
x_158 = lean_string_append(x_156, x_157);
x_159 = lean_string_append(x_158, x_151);
lean_dec(x_151);
x_160 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_161 = lean_string_append(x_159, x_160);
x_162 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_162, 0, x_161);
if (lean_is_scalar(x_150)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_150;
 lean_ctor_set_tag(x_163, 1);
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_149);
return x_163;
}
else
{
lean_object* x_164; 
lean_dec(x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_198; 
x_198 = lean_box(0);
x_164 = x_198;
goto block_197;
}
else
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_152, 0);
lean_inc(x_199);
lean_dec(x_152);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
lean_ctor_set_tag(x_199, 4);
x_164 = x_199;
goto block_197;
}
else
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_164 = x_202;
goto block_197;
}
}
else
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_199);
if (x_203 == 0)
{
lean_ctor_set_tag(x_199, 5);
x_164 = x_199;
goto block_197;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_199, 0);
lean_inc(x_204);
lean_dec(x_199);
x_205 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_164 = x_205;
goto block_197;
}
}
}
block_197:
{
lean_object* x_165; 
lean_inc(x_164);
x_165 = lean_apply_1(x_5, x_164);
if (lean_obj_tag(x_165) == 0)
{
uint8_t x_166; 
lean_dec(x_153);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_167 = lean_ctor_get(x_165, 0);
x_168 = l_Lean_Json_compress(x_164);
x_169 = l_IO_FS_Stream_readRequestAs___closed__3;
x_170 = lean_string_append(x_169, x_168);
lean_dec(x_168);
x_171 = l_IO_FS_Stream_readRequestAs___closed__4;
x_172 = lean_string_append(x_170, x_171);
x_173 = lean_string_append(x_172, x_3);
lean_dec(x_3);
x_174 = l_IO_FS_Stream_readRequestAs___closed__5;
x_175 = lean_string_append(x_173, x_174);
x_176 = lean_string_append(x_175, x_167);
lean_dec(x_167);
x_177 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_178 = lean_string_append(x_176, x_177);
lean_ctor_set_tag(x_165, 18);
lean_ctor_set(x_165, 0, x_178);
if (lean_is_scalar(x_150)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_150;
 lean_ctor_set_tag(x_179, 1);
}
lean_ctor_set(x_179, 0, x_165);
lean_ctor_set(x_179, 1, x_149);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_180 = lean_ctor_get(x_165, 0);
lean_inc(x_180);
lean_dec(x_165);
x_181 = l_Lean_Json_compress(x_164);
x_182 = l_IO_FS_Stream_readRequestAs___closed__3;
x_183 = lean_string_append(x_182, x_181);
lean_dec(x_181);
x_184 = l_IO_FS_Stream_readRequestAs___closed__4;
x_185 = lean_string_append(x_183, x_184);
x_186 = lean_string_append(x_185, x_3);
lean_dec(x_3);
x_187 = l_IO_FS_Stream_readRequestAs___closed__5;
x_188 = lean_string_append(x_186, x_187);
x_189 = lean_string_append(x_188, x_180);
lean_dec(x_180);
x_190 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_192, 0, x_191);
if (lean_is_scalar(x_150)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_150;
 lean_ctor_set_tag(x_193, 1);
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_149);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_164);
x_194 = lean_ctor_get(x_165, 0);
lean_inc(x_194);
lean_dec(x_165);
if (lean_is_scalar(x_153)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_153;
 lean_ctor_set_tag(x_195, 0);
}
lean_ctor_set(x_195, 0, x_3);
lean_ctor_set(x_195, 1, x_194);
if (lean_is_scalar(x_150)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_150;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_149);
return x_196;
}
}
}
}
case 2:
{
uint8_t x_206; 
lean_dec(x_5);
lean_dec(x_3);
x_206 = !lean_is_exclusive(x_7);
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_7, 0);
lean_dec(x_207);
x_208 = !lean_is_exclusive(x_8);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_ctor_get(x_8, 0);
x_210 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_210);
x_211 = lean_box(0);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_8);
lean_ctor_set(x_212, 1, x_211);
switch (lean_obj_tag(x_209)) {
case 0:
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_209);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_ctor_set_tag(x_209, 3);
x_214 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_209);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_212);
x_217 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_219 = l_Lean_Json_mkObj(x_218);
x_220 = l_Lean_Json_compress(x_219);
x_221 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_222 = lean_string_append(x_221, x_220);
lean_dec(x_220);
x_223 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_224 = lean_string_append(x_222, x_223);
x_225 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_225);
return x_7;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_226 = lean_ctor_get(x_209, 0);
lean_inc(x_226);
lean_dec(x_209);
x_227 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_212);
x_231 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = l_Lean_Json_mkObj(x_232);
x_234 = l_Lean_Json_compress(x_233);
x_235 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_236 = lean_string_append(x_235, x_234);
lean_dec(x_234);
x_237 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_238 = lean_string_append(x_236, x_237);
x_239 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_239);
return x_7;
}
}
case 1:
{
uint8_t x_240; 
x_240 = !lean_is_exclusive(x_209);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_ctor_set_tag(x_209, 2);
x_241 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_209);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_212);
x_244 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
x_246 = l_Lean_Json_mkObj(x_245);
x_247 = l_Lean_Json_compress(x_246);
x_248 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_249 = lean_string_append(x_248, x_247);
lean_dec(x_247);
x_250 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_251 = lean_string_append(x_249, x_250);
x_252 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_252);
return x_7;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_253 = lean_ctor_get(x_209, 0);
lean_inc(x_253);
lean_dec(x_209);
x_254 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_254, 0, x_253);
x_255 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_212);
x_258 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
x_260 = l_Lean_Json_mkObj(x_259);
x_261 = l_Lean_Json_compress(x_260);
x_262 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_263 = lean_string_append(x_262, x_261);
lean_dec(x_261);
x_264 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_265 = lean_string_append(x_263, x_264);
x_266 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_266);
return x_7;
}
}
default: 
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_267 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_212);
x_269 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
x_271 = l_Lean_Json_mkObj(x_270);
x_272 = l_Lean_Json_compress(x_271);
x_273 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_274 = lean_string_append(x_273, x_272);
lean_dec(x_272);
x_275 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_276 = lean_string_append(x_274, x_275);
x_277 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_277);
return x_7;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_278 = lean_ctor_get(x_8, 0);
x_279 = lean_ctor_get(x_8, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_8);
x_280 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_279);
x_282 = lean_box(0);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
switch (lean_obj_tag(x_278)) {
case 0:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_284 = lean_ctor_get(x_278, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 x_285 = x_278;
} else {
 lean_dec_ref(x_278);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(3, 1, 0);
} else {
 x_286 = x_285;
 lean_ctor_set_tag(x_286, 3);
}
lean_ctor_set(x_286, 0, x_284);
x_287 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_283);
x_290 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
x_292 = l_Lean_Json_mkObj(x_291);
x_293 = l_Lean_Json_compress(x_292);
x_294 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_295 = lean_string_append(x_294, x_293);
lean_dec(x_293);
x_296 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_297 = lean_string_append(x_295, x_296);
x_298 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_298);
return x_7;
}
case 1:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_299 = lean_ctor_get(x_278, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 x_300 = x_278;
} else {
 lean_dec_ref(x_278);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(2, 1, 0);
} else {
 x_301 = x_300;
 lean_ctor_set_tag(x_301, 2);
}
lean_ctor_set(x_301, 0, x_299);
x_302 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_301);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_283);
x_305 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_304);
x_307 = l_Lean_Json_mkObj(x_306);
x_308 = l_Lean_Json_compress(x_307);
x_309 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_310 = lean_string_append(x_309, x_308);
lean_dec(x_308);
x_311 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_312 = lean_string_append(x_310, x_311);
x_313 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_313);
return x_7;
}
default: 
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_314 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_283);
x_316 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_315);
x_318 = l_Lean_Json_mkObj(x_317);
x_319 = l_Lean_Json_compress(x_318);
x_320 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_321 = lean_string_append(x_320, x_319);
lean_dec(x_319);
x_322 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_323 = lean_string_append(x_321, x_322);
x_324 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_324);
return x_7;
}
}
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_325 = lean_ctor_get(x_7, 1);
lean_inc(x_325);
lean_dec(x_7);
x_326 = lean_ctor_get(x_8, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_8, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_328 = x_8;
} else {
 lean_dec_ref(x_8);
 x_328 = lean_box(0);
}
x_329 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
if (lean_is_scalar(x_328)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_328;
 lean_ctor_set_tag(x_330, 0);
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_327);
x_331 = lean_box(0);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
switch (lean_obj_tag(x_326)) {
case 0:
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_333 = lean_ctor_get(x_326, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_334 = x_326;
} else {
 lean_dec_ref(x_326);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(3, 1, 0);
} else {
 x_335 = x_334;
 lean_ctor_set_tag(x_335, 3);
}
lean_ctor_set(x_335, 0, x_333);
x_336 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_335);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_332);
x_339 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
x_341 = l_Lean_Json_mkObj(x_340);
x_342 = l_Lean_Json_compress(x_341);
x_343 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_344 = lean_string_append(x_343, x_342);
lean_dec(x_342);
x_345 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_346 = lean_string_append(x_344, x_345);
x_347 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_347, 0, x_346);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_325);
return x_348;
}
case 1:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_349 = lean_ctor_get(x_326, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_350 = x_326;
} else {
 lean_dec_ref(x_326);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(2, 1, 0);
} else {
 x_351 = x_350;
 lean_ctor_set_tag(x_351, 2);
}
lean_ctor_set(x_351, 0, x_349);
x_352 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_332);
x_355 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
x_357 = l_Lean_Json_mkObj(x_356);
x_358 = l_Lean_Json_compress(x_357);
x_359 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_360 = lean_string_append(x_359, x_358);
lean_dec(x_358);
x_361 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_362 = lean_string_append(x_360, x_361);
x_363 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_363, 0, x_362);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_325);
return x_364;
}
default: 
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_365 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_332);
x_367 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
x_369 = l_Lean_Json_mkObj(x_368);
x_370 = l_Lean_Json_compress(x_369);
x_371 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_372 = lean_string_append(x_371, x_370);
lean_dec(x_370);
x_373 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_374 = lean_string_append(x_372, x_373);
x_375 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_375, 0, x_374);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_325);
return x_376;
}
}
}
}
default: 
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_5);
lean_dec(x_3);
x_377 = lean_ctor_get(x_7, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_378 = x_7;
} else {
 lean_dec_ref(x_7);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_8, 0);
lean_inc(x_379);
x_380 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_381 = lean_ctor_get(x_8, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_8, 2);
lean_inc(x_382);
lean_dec(x_8);
x_383 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_383, 0, x_381);
x_384 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = lean_box(0);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_389 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_388, x_382);
lean_dec(x_382);
switch (lean_obj_tag(x_379)) {
case 0:
{
uint8_t x_427; 
x_427 = !lean_is_exclusive(x_379);
if (x_427 == 0)
{
lean_ctor_set_tag(x_379, 3);
x_390 = x_379;
goto block_426;
}
else
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_379, 0);
lean_inc(x_428);
lean_dec(x_379);
x_429 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_429, 0, x_428);
x_390 = x_429;
goto block_426;
}
}
case 1:
{
uint8_t x_430; 
x_430 = !lean_is_exclusive(x_379);
if (x_430 == 0)
{
lean_ctor_set_tag(x_379, 2);
x_390 = x_379;
goto block_426;
}
else
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_ctor_get(x_379, 0);
lean_inc(x_431);
lean_dec(x_379);
x_432 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_432, 0, x_431);
x_390 = x_432;
goto block_426;
}
}
default: 
{
lean_object* x_433; 
x_433 = lean_box(0);
x_390 = x_433;
goto block_426;
}
}
block_426:
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_390);
switch (x_380) {
case 0:
{
lean_object* x_414; 
x_414 = l_Lean_JsonRpc_instToJsonErrorCode___closed__2;
x_393 = x_414;
goto block_413;
}
case 1:
{
lean_object* x_415; 
x_415 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_393 = x_415;
goto block_413;
}
case 2:
{
lean_object* x_416; 
x_416 = l_Lean_JsonRpc_instToJsonErrorCode___closed__6;
x_393 = x_416;
goto block_413;
}
case 3:
{
lean_object* x_417; 
x_417 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_393 = x_417;
goto block_413;
}
case 4:
{
lean_object* x_418; 
x_418 = l_Lean_JsonRpc_instToJsonErrorCode___closed__10;
x_393 = x_418;
goto block_413;
}
case 5:
{
lean_object* x_419; 
x_419 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_393 = x_419;
goto block_413;
}
case 6:
{
lean_object* x_420; 
x_420 = l_Lean_JsonRpc_instToJsonErrorCode___closed__14;
x_393 = x_420;
goto block_413;
}
case 7:
{
lean_object* x_421; 
x_421 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_393 = x_421;
goto block_413;
}
case 8:
{
lean_object* x_422; 
x_422 = l_Lean_JsonRpc_instToJsonErrorCode___closed__18;
x_393 = x_422;
goto block_413;
}
case 9:
{
lean_object* x_423; 
x_423 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_393 = x_423;
goto block_413;
}
case 10:
{
lean_object* x_424; 
x_424 = l_Lean_JsonRpc_instToJsonErrorCode___closed__22;
x_393 = x_424;
goto block_413;
}
default: 
{
lean_object* x_425; 
x_425 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_393 = x_425;
goto block_413;
}
}
block_413:
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_394 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_393);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_387);
x_397 = l_List_appendTR___rarg(x_396, x_389);
x_398 = l_Lean_Json_mkObj(x_397);
x_399 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_386);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_392);
lean_ctor_set(x_402, 1, x_401);
x_403 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_402);
x_405 = l_Lean_Json_mkObj(x_404);
x_406 = l_Lean_Json_compress(x_405);
x_407 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_408 = lean_string_append(x_407, x_406);
lean_dec(x_406);
x_409 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_410 = lean_string_append(x_408, x_409);
x_411 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_411, 0, x_410);
if (lean_is_scalar(x_378)) {
 x_412 = lean_alloc_ctor(1, 2, 0);
} else {
 x_412 = x_378;
 lean_ctor_set_tag(x_412, 1);
}
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_377);
return x_412;
}
}
}
}
}
else
{
uint8_t x_434; 
lean_dec(x_5);
lean_dec(x_3);
x_434 = !lean_is_exclusive(x_7);
if (x_434 == 0)
{
return x_7;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_7, 0);
x_436 = lean_ctor_get(x_7, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_7);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
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
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected JSON-RPC response, got: '", 34, 34);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected id ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", got id ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unexpected result '", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
switch (lean_obj_tag(x_11)) {
case 0:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_ctor_set_tag(x_11, 3);
x_22 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
x_25 = l_List_appendTR___rarg(x_24, x_20);
x_26 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Json_mkObj(x_27);
x_29 = l_Lean_Json_compress(x_28);
x_30 = l_IO_FS_Stream_readResponseAs___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_34);
return x_7;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_18);
x_40 = l_List_appendTR___rarg(x_39, x_20);
x_41 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Json_mkObj(x_42);
x_44 = l_Lean_Json_compress(x_43);
x_45 = l_IO_FS_Stream_readResponseAs___closed__1;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_49);
return x_7;
}
}
case 1:
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_11);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_ctor_set_tag(x_11, 2);
x_51 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_11);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_18);
x_54 = l_List_appendTR___rarg(x_53, x_20);
x_55 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Json_mkObj(x_56);
x_58 = l_Lean_Json_compress(x_57);
x_59 = l_IO_FS_Stream_readResponseAs___closed__1;
x_60 = lean_string_append(x_59, x_58);
lean_dec(x_58);
x_61 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_63);
return x_7;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_64 = lean_ctor_get(x_11, 0);
lean_inc(x_64);
lean_dec(x_11);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_18);
x_69 = l_List_appendTR___rarg(x_68, x_20);
x_70 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Json_mkObj(x_71);
x_73 = l_Lean_Json_compress(x_72);
x_74 = l_IO_FS_Stream_readResponseAs___closed__1;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_78);
return x_7;
}
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_79 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_18);
x_81 = l_List_appendTR___rarg(x_80, x_20);
x_82 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_Json_mkObj(x_83);
x_85 = l_Lean_Json_compress(x_84);
x_86 = l_IO_FS_Stream_readResponseAs___closed__1;
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_90);
return x_7;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_91 = lean_ctor_get(x_7, 1);
lean_inc(x_91);
lean_dec(x_7);
x_92 = lean_ctor_get(x_8, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_8, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_8, 2);
lean_inc(x_94);
lean_dec(x_8);
x_95 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_95, 0, x_93);
x_96 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_101 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_100, x_94);
switch (lean_obj_tag(x_92)) {
case 0:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_102 = lean_ctor_get(x_92, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_103 = x_92;
} else {
 lean_dec_ref(x_92);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(3, 1, 0);
} else {
 x_104 = x_103;
 lean_ctor_set_tag(x_104, 3);
}
lean_ctor_set(x_104, 0, x_102);
x_105 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_99);
x_108 = l_List_appendTR___rarg(x_107, x_101);
x_109 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_Json_mkObj(x_110);
x_112 = l_Lean_Json_compress(x_111);
x_113 = l_IO_FS_Stream_readResponseAs___closed__1;
x_114 = lean_string_append(x_113, x_112);
lean_dec(x_112);
x_115 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_91);
return x_118;
}
case 1:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_119 = lean_ctor_get(x_92, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_120 = x_92;
} else {
 lean_dec_ref(x_92);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(2, 1, 0);
} else {
 x_121 = x_120;
 lean_ctor_set_tag(x_121, 2);
}
lean_ctor_set(x_121, 0, x_119);
x_122 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_99);
x_125 = l_List_appendTR___rarg(x_124, x_101);
x_126 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = l_Lean_Json_mkObj(x_127);
x_129 = l_Lean_Json_compress(x_128);
x_130 = l_IO_FS_Stream_readResponseAs___closed__1;
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
x_132 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_133 = lean_string_append(x_131, x_132);
x_134 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_91);
return x_135;
}
default: 
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_136 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_99);
x_138 = l_List_appendTR___rarg(x_137, x_101);
x_139 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Lean_Json_mkObj(x_140);
x_142 = l_Lean_Json_compress(x_141);
x_143 = l_IO_FS_Stream_readResponseAs___closed__1;
x_144 = lean_string_append(x_143, x_142);
lean_dec(x_142);
x_145 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_146 = lean_string_append(x_144, x_145);
x_147 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_91);
return x_148;
}
}
}
}
case 1:
{
uint8_t x_149; 
lean_dec(x_5);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_7);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_7, 0);
lean_dec(x_150);
x_151 = !lean_is_exclusive(x_8);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_152 = lean_ctor_get(x_8, 0);
x_153 = lean_ctor_get(x_8, 1);
x_154 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_154, 0, x_152);
x_155 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 1, x_154);
lean_ctor_set(x_8, 0, x_155);
x_156 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_157 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_156, x_153);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_8);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_Json_mkObj(x_160);
x_162 = l_Lean_Json_compress(x_161);
x_163 = l_IO_FS_Stream_readResponseAs___closed__1;
x_164 = lean_string_append(x_163, x_162);
lean_dec(x_162);
x_165 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_166 = lean_string_append(x_164, x_165);
x_167 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_167);
return x_7;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_168 = lean_ctor_get(x_8, 0);
x_169 = lean_ctor_get(x_8, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_8);
x_170 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_170, 0, x_168);
x_171 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_174 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_173, x_169);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = l_Lean_Json_mkObj(x_177);
x_179 = l_Lean_Json_compress(x_178);
x_180 = l_IO_FS_Stream_readResponseAs___closed__1;
x_181 = lean_string_append(x_180, x_179);
lean_dec(x_179);
x_182 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_183 = lean_string_append(x_181, x_182);
x_184 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_184);
return x_7;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_185 = lean_ctor_get(x_7, 1);
lean_inc(x_185);
lean_dec(x_7);
x_186 = lean_ctor_get(x_8, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_8, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_188 = x_8;
} else {
 lean_dec_ref(x_8);
 x_188 = lean_box(0);
}
x_189 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_189, 0, x_186);
x_190 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
if (lean_is_scalar(x_188)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_188;
 lean_ctor_set_tag(x_191, 0);
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
x_192 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_193 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_192, x_187);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = l_Lean_Json_mkObj(x_196);
x_198 = l_Lean_Json_compress(x_197);
x_199 = l_IO_FS_Stream_readResponseAs___closed__1;
x_200 = lean_string_append(x_199, x_198);
lean_dec(x_198);
x_201 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_202 = lean_string_append(x_200, x_201);
x_203 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_185);
return x_204;
}
}
case 2:
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_205 = lean_ctor_get(x_7, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_206 = x_7;
} else {
 lean_dec_ref(x_7);
 x_206 = lean_box(0);
}
x_207 = !lean_is_exclusive(x_8);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_254; 
x_208 = lean_ctor_get(x_8, 0);
x_209 = lean_ctor_get(x_8, 1);
x_254 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_208, x_3);
if (x_254 == 0)
{
lean_free_object(x_8);
lean_dec(x_209);
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_3, 0);
lean_inc(x_255);
lean_dec(x_3);
x_256 = l_Lean_JsonRpc_instToStringRequestID___closed__1;
x_257 = lean_string_append(x_256, x_255);
lean_dec(x_255);
x_258 = lean_string_append(x_257, x_256);
x_210 = x_258;
goto block_253;
}
case 1:
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_3, 0);
lean_inc(x_259);
lean_dec(x_3);
x_260 = l_Lean_JsonNumber_toString(x_259);
x_210 = x_260;
goto block_253;
}
default: 
{
lean_object* x_261; 
x_261 = l_Lean_JsonRpc_instToStringRequestID___closed__2;
x_210 = x_261;
goto block_253;
}
}
}
else
{
lean_object* x_262; 
lean_dec(x_208);
lean_dec(x_206);
lean_inc(x_209);
x_262 = lean_apply_1(x_5, x_209);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_263; 
lean_dec(x_3);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_264 = lean_ctor_get(x_262, 0);
x_265 = l_Lean_Json_compress(x_209);
x_266 = l_IO_FS_Stream_readResponseAs___closed__4;
x_267 = lean_string_append(x_266, x_265);
lean_dec(x_265);
x_268 = l_IO_FS_Stream_readRequestAs___closed__5;
x_269 = lean_string_append(x_267, x_268);
x_270 = lean_string_append(x_269, x_264);
lean_dec(x_264);
x_271 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_272 = lean_string_append(x_270, x_271);
lean_ctor_set_tag(x_262, 18);
lean_ctor_set(x_262, 0, x_272);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_205);
lean_ctor_set(x_8, 0, x_262);
return x_8;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_273 = lean_ctor_get(x_262, 0);
lean_inc(x_273);
lean_dec(x_262);
x_274 = l_Lean_Json_compress(x_209);
x_275 = l_IO_FS_Stream_readResponseAs___closed__4;
x_276 = lean_string_append(x_275, x_274);
lean_dec(x_274);
x_277 = l_IO_FS_Stream_readRequestAs___closed__5;
x_278 = lean_string_append(x_276, x_277);
x_279 = lean_string_append(x_278, x_273);
lean_dec(x_273);
x_280 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_281 = lean_string_append(x_279, x_280);
x_282 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_205);
lean_ctor_set(x_8, 0, x_282);
return x_8;
}
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_209);
x_283 = lean_ctor_get(x_262, 0);
lean_inc(x_283);
lean_dec(x_262);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 1, x_283);
lean_ctor_set(x_8, 0, x_3);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_8);
lean_ctor_set(x_284, 1, x_205);
return x_284;
}
}
block_253:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = l_IO_FS_Stream_readResponseAs___closed__2;
x_212 = lean_string_append(x_211, x_210);
lean_dec(x_210);
x_213 = l_IO_FS_Stream_readResponseAs___closed__3;
x_214 = lean_string_append(x_212, x_213);
switch (lean_obj_tag(x_208)) {
case 0:
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_208);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_216 = lean_ctor_get(x_208, 0);
x_217 = l_Lean_JsonRpc_instToStringRequestID___closed__1;
x_218 = lean_string_append(x_217, x_216);
lean_dec(x_216);
x_219 = lean_string_append(x_218, x_217);
x_220 = lean_string_append(x_214, x_219);
lean_dec(x_219);
x_221 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_222 = lean_string_append(x_220, x_221);
lean_ctor_set_tag(x_208, 18);
lean_ctor_set(x_208, 0, x_222);
if (lean_is_scalar(x_206)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_206;
 lean_ctor_set_tag(x_223, 1);
}
lean_ctor_set(x_223, 0, x_208);
lean_ctor_set(x_223, 1, x_205);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_224 = lean_ctor_get(x_208, 0);
lean_inc(x_224);
lean_dec(x_208);
x_225 = l_Lean_JsonRpc_instToStringRequestID___closed__1;
x_226 = lean_string_append(x_225, x_224);
lean_dec(x_224);
x_227 = lean_string_append(x_226, x_225);
x_228 = lean_string_append(x_214, x_227);
lean_dec(x_227);
x_229 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_230 = lean_string_append(x_228, x_229);
x_231 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_231, 0, x_230);
if (lean_is_scalar(x_206)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_206;
 lean_ctor_set_tag(x_232, 1);
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_205);
return x_232;
}
}
case 1:
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_208);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_234 = lean_ctor_get(x_208, 0);
x_235 = l_Lean_JsonNumber_toString(x_234);
x_236 = lean_string_append(x_214, x_235);
lean_dec(x_235);
x_237 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_238 = lean_string_append(x_236, x_237);
lean_ctor_set_tag(x_208, 18);
lean_ctor_set(x_208, 0, x_238);
if (lean_is_scalar(x_206)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_206;
 lean_ctor_set_tag(x_239, 1);
}
lean_ctor_set(x_239, 0, x_208);
lean_ctor_set(x_239, 1, x_205);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_240 = lean_ctor_get(x_208, 0);
lean_inc(x_240);
lean_dec(x_208);
x_241 = l_Lean_JsonNumber_toString(x_240);
x_242 = lean_string_append(x_214, x_241);
lean_dec(x_241);
x_243 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_244 = lean_string_append(x_242, x_243);
x_245 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_245, 0, x_244);
if (lean_is_scalar(x_206)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_206;
 lean_ctor_set_tag(x_246, 1);
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_205);
return x_246;
}
}
default: 
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_247 = l_Lean_JsonRpc_instToStringRequestID___closed__2;
x_248 = lean_string_append(x_214, x_247);
x_249 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_250 = lean_string_append(x_248, x_249);
x_251 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_251, 0, x_250);
if (lean_is_scalar(x_206)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_206;
 lean_ctor_set_tag(x_252, 1);
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_205);
return x_252;
}
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_317; 
x_285 = lean_ctor_get(x_8, 0);
x_286 = lean_ctor_get(x_8, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_8);
x_317 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_36_(x_285, x_3);
if (x_317 == 0)
{
lean_dec(x_286);
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_318 = lean_ctor_get(x_3, 0);
lean_inc(x_318);
lean_dec(x_3);
x_319 = l_Lean_JsonRpc_instToStringRequestID___closed__1;
x_320 = lean_string_append(x_319, x_318);
lean_dec(x_318);
x_321 = lean_string_append(x_320, x_319);
x_287 = x_321;
goto block_316;
}
case 1:
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_3, 0);
lean_inc(x_322);
lean_dec(x_3);
x_323 = l_Lean_JsonNumber_toString(x_322);
x_287 = x_323;
goto block_316;
}
default: 
{
lean_object* x_324; 
x_324 = l_Lean_JsonRpc_instToStringRequestID___closed__2;
x_287 = x_324;
goto block_316;
}
}
}
else
{
lean_object* x_325; 
lean_dec(x_285);
lean_dec(x_206);
lean_inc(x_286);
x_325 = lean_apply_1(x_5, x_286);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_3);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 x_327 = x_325;
} else {
 lean_dec_ref(x_325);
 x_327 = lean_box(0);
}
x_328 = l_Lean_Json_compress(x_286);
x_329 = l_IO_FS_Stream_readResponseAs___closed__4;
x_330 = lean_string_append(x_329, x_328);
lean_dec(x_328);
x_331 = l_IO_FS_Stream_readRequestAs___closed__5;
x_332 = lean_string_append(x_330, x_331);
x_333 = lean_string_append(x_332, x_326);
lean_dec(x_326);
x_334 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_335 = lean_string_append(x_333, x_334);
if (lean_is_scalar(x_327)) {
 x_336 = lean_alloc_ctor(18, 1, 0);
} else {
 x_336 = x_327;
 lean_ctor_set_tag(x_336, 18);
}
lean_ctor_set(x_336, 0, x_335);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_205);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_286);
x_338 = lean_ctor_get(x_325, 0);
lean_inc(x_338);
lean_dec(x_325);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_3);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_205);
return x_340;
}
}
block_316:
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = l_IO_FS_Stream_readResponseAs___closed__2;
x_289 = lean_string_append(x_288, x_287);
lean_dec(x_287);
x_290 = l_IO_FS_Stream_readResponseAs___closed__3;
x_291 = lean_string_append(x_289, x_290);
switch (lean_obj_tag(x_285)) {
case 0:
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_292 = lean_ctor_get(x_285, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_293 = x_285;
} else {
 lean_dec_ref(x_285);
 x_293 = lean_box(0);
}
x_294 = l_Lean_JsonRpc_instToStringRequestID___closed__1;
x_295 = lean_string_append(x_294, x_292);
lean_dec(x_292);
x_296 = lean_string_append(x_295, x_294);
x_297 = lean_string_append(x_291, x_296);
lean_dec(x_296);
x_298 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_299 = lean_string_append(x_297, x_298);
if (lean_is_scalar(x_293)) {
 x_300 = lean_alloc_ctor(18, 1, 0);
} else {
 x_300 = x_293;
 lean_ctor_set_tag(x_300, 18);
}
lean_ctor_set(x_300, 0, x_299);
if (lean_is_scalar(x_206)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_206;
 lean_ctor_set_tag(x_301, 1);
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_205);
return x_301;
}
case 1:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_285, 0);
lean_inc(x_302);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_303 = x_285;
} else {
 lean_dec_ref(x_285);
 x_303 = lean_box(0);
}
x_304 = l_Lean_JsonNumber_toString(x_302);
x_305 = lean_string_append(x_291, x_304);
lean_dec(x_304);
x_306 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_307 = lean_string_append(x_305, x_306);
if (lean_is_scalar(x_303)) {
 x_308 = lean_alloc_ctor(18, 1, 0);
} else {
 x_308 = x_303;
 lean_ctor_set_tag(x_308, 18);
}
lean_ctor_set(x_308, 0, x_307);
if (lean_is_scalar(x_206)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_206;
 lean_ctor_set_tag(x_309, 1);
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_205);
return x_309;
}
default: 
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_310 = l_Lean_JsonRpc_instToStringRequestID___closed__2;
x_311 = lean_string_append(x_291, x_310);
x_312 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_313 = lean_string_append(x_311, x_312);
x_314 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_314, 0, x_313);
if (lean_is_scalar(x_206)) {
 x_315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_315 = x_206;
 lean_ctor_set_tag(x_315, 1);
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_205);
return x_315;
}
}
}
}
}
default: 
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_5);
lean_dec(x_3);
x_341 = lean_ctor_get(x_7, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_342 = x_7;
} else {
 lean_dec_ref(x_7);
 x_342 = lean_box(0);
}
x_343 = lean_ctor_get(x_8, 0);
lean_inc(x_343);
x_344 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_345 = lean_ctor_get(x_8, 1);
lean_inc(x_345);
x_346 = lean_ctor_get(x_8, 2);
lean_inc(x_346);
lean_dec(x_8);
x_347 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_347, 0, x_345);
x_348 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_347);
x_350 = lean_box(0);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
x_352 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_353 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_352, x_346);
lean_dec(x_346);
switch (lean_obj_tag(x_343)) {
case 0:
{
uint8_t x_391; 
x_391 = !lean_is_exclusive(x_343);
if (x_391 == 0)
{
lean_ctor_set_tag(x_343, 3);
x_354 = x_343;
goto block_390;
}
else
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_343, 0);
lean_inc(x_392);
lean_dec(x_343);
x_393 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_393, 0, x_392);
x_354 = x_393;
goto block_390;
}
}
case 1:
{
uint8_t x_394; 
x_394 = !lean_is_exclusive(x_343);
if (x_394 == 0)
{
lean_ctor_set_tag(x_343, 2);
x_354 = x_343;
goto block_390;
}
else
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_343, 0);
lean_inc(x_395);
lean_dec(x_343);
x_396 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_396, 0, x_395);
x_354 = x_396;
goto block_390;
}
}
default: 
{
lean_object* x_397; 
x_397 = lean_box(0);
x_354 = x_397;
goto block_390;
}
}
block_390:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
switch (x_344) {
case 0:
{
lean_object* x_378; 
x_378 = l_Lean_JsonRpc_instToJsonErrorCode___closed__2;
x_357 = x_378;
goto block_377;
}
case 1:
{
lean_object* x_379; 
x_379 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_357 = x_379;
goto block_377;
}
case 2:
{
lean_object* x_380; 
x_380 = l_Lean_JsonRpc_instToJsonErrorCode___closed__6;
x_357 = x_380;
goto block_377;
}
case 3:
{
lean_object* x_381; 
x_381 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_357 = x_381;
goto block_377;
}
case 4:
{
lean_object* x_382; 
x_382 = l_Lean_JsonRpc_instToJsonErrorCode___closed__10;
x_357 = x_382;
goto block_377;
}
case 5:
{
lean_object* x_383; 
x_383 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_357 = x_383;
goto block_377;
}
case 6:
{
lean_object* x_384; 
x_384 = l_Lean_JsonRpc_instToJsonErrorCode___closed__14;
x_357 = x_384;
goto block_377;
}
case 7:
{
lean_object* x_385; 
x_385 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_357 = x_385;
goto block_377;
}
case 8:
{
lean_object* x_386; 
x_386 = l_Lean_JsonRpc_instToJsonErrorCode___closed__18;
x_357 = x_386;
goto block_377;
}
case 9:
{
lean_object* x_387; 
x_387 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_357 = x_387;
goto block_377;
}
case 10:
{
lean_object* x_388; 
x_388 = l_Lean_JsonRpc_instToJsonErrorCode___closed__22;
x_357 = x_388;
goto block_377;
}
default: 
{
lean_object* x_389; 
x_389 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_357 = x_389;
goto block_377;
}
}
block_377:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_358 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_357);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_351);
x_361 = l_List_appendTR___rarg(x_360, x_353);
x_362 = l_Lean_Json_mkObj(x_361);
x_363 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_362);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_350);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_356);
lean_ctor_set(x_366, 1, x_365);
x_367 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
x_369 = l_Lean_Json_mkObj(x_368);
x_370 = l_Lean_Json_compress(x_369);
x_371 = l_IO_FS_Stream_readResponseAs___closed__1;
x_372 = lean_string_append(x_371, x_370);
lean_dec(x_370);
x_373 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_374 = lean_string_append(x_372, x_373);
x_375 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_375, 0, x_374);
if (lean_is_scalar(x_342)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_342;
 lean_ctor_set_tag(x_376, 1);
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_341);
return x_376;
}
}
}
}
}
else
{
uint8_t x_398; 
lean_dec(x_5);
lean_dec(x_3);
x_398 = !lean_is_exclusive(x_7);
if (x_398 == 0)
{
return x_7;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_7, 0);
x_400 = lean_ctor_get(x_7, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_7);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
return x_401;
}
}
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
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
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_ctor_set_tag(x_4, 3);
x_15 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
x_18 = l_List_appendTR___rarg(x_17, x_13);
x_19 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Json_mkObj(x_20);
x_22 = l_IO_FS_Stream_writeJson(x_1, x_21, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec(x_4);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
x_28 = l_List_appendTR___rarg(x_27, x_13);
x_29 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Json_mkObj(x_30);
x_32 = l_IO_FS_Stream_writeJson(x_1, x_31, x_3);
return x_32;
}
}
case 1:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_ctor_set_tag(x_4, 2);
x_34 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_4);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
x_37 = l_List_appendTR___rarg(x_36, x_13);
x_38 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Json_mkObj(x_39);
x_41 = l_IO_FS_Stream_writeJson(x_1, x_40, x_3);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
lean_dec(x_4);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_11);
x_47 = l_List_appendTR___rarg(x_46, x_13);
x_48 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Json_mkObj(x_49);
x_51 = l_IO_FS_Stream_writeJson(x_1, x_50, x_3);
return x_51;
}
}
default: 
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_11);
x_54 = l_List_appendTR___rarg(x_53, x_13);
x_55 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Json_mkObj(x_56);
x_58 = l_IO_FS_Stream_writeJson(x_1, x_57, x_3);
return x_58;
}
}
}
case 1:
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_ctor_get(x_2, 1);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_60);
x_63 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_62);
lean_ctor_set(x_2, 0, x_63);
x_64 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_65 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_64, x_61);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_2);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_Json_mkObj(x_68);
x_70 = l_IO_FS_Stream_writeJson(x_1, x_69, x_3);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = lean_ctor_get(x_2, 0);
x_72 = lean_ctor_get(x_2, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_2);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_71);
x_74 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_77 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_76, x_72);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Json_mkObj(x_80);
x_82 = l_IO_FS_Stream_writeJson(x_1, x_81, x_3);
return x_82;
}
}
case 2:
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_2);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_2, 0);
x_85 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_85);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_2);
lean_ctor_set(x_87, 1, x_86);
switch (lean_obj_tag(x_84)) {
case 0:
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_84);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_ctor_set_tag(x_84, 3);
x_89 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
x_92 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l_Lean_Json_mkObj(x_93);
x_95 = l_IO_FS_Stream_writeJson(x_1, x_94, x_3);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_84, 0);
lean_inc(x_96);
lean_dec(x_84);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_87);
x_101 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Lean_Json_mkObj(x_102);
x_104 = l_IO_FS_Stream_writeJson(x_1, x_103, x_3);
return x_104;
}
}
case 1:
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_84);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_ctor_set_tag(x_84, 2);
x_106 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_84);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_87);
x_109 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_Json_mkObj(x_110);
x_112 = l_IO_FS_Stream_writeJson(x_1, x_111, x_3);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = lean_ctor_get(x_84, 0);
lean_inc(x_113);
lean_dec(x_84);
x_114 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_87);
x_118 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = l_Lean_Json_mkObj(x_119);
x_121 = l_IO_FS_Stream_writeJson(x_1, x_120, x_3);
return x_121;
}
}
default: 
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_122 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_87);
x_124 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = l_Lean_Json_mkObj(x_125);
x_127 = l_IO_FS_Stream_writeJson(x_1, x_126, x_3);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_2, 0);
x_129 = lean_ctor_get(x_2, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_2);
x_130 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
switch (lean_obj_tag(x_128)) {
case 0:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_134 = lean_ctor_get(x_128, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_135 = x_128;
} else {
 lean_dec_ref(x_128);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(3, 1, 0);
} else {
 x_136 = x_135;
 lean_ctor_set_tag(x_136, 3);
}
lean_ctor_set(x_136, 0, x_134);
x_137 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_133);
x_140 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_Json_mkObj(x_141);
x_143 = l_IO_FS_Stream_writeJson(x_1, x_142, x_3);
return x_143;
}
case 1:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_144 = lean_ctor_get(x_128, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_145 = x_128;
} else {
 lean_dec_ref(x_128);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(2, 1, 0);
} else {
 x_146 = x_145;
 lean_ctor_set_tag(x_146, 2);
}
lean_ctor_set(x_146, 0, x_144);
x_147 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_133);
x_150 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = l_Lean_Json_mkObj(x_151);
x_153 = l_IO_FS_Stream_writeJson(x_1, x_152, x_3);
return x_153;
}
default: 
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_133);
x_156 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Lean_Json_mkObj(x_157);
x_159 = l_IO_FS_Stream_writeJson(x_1, x_158, x_3);
return x_159;
}
}
}
}
default: 
{
lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_160 = lean_ctor_get(x_2, 0);
lean_inc(x_160);
x_161 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_162 = lean_ctor_get(x_2, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_2, 2);
lean_inc(x_163);
lean_dec(x_2);
x_164 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_164, 0, x_162);
x_165 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_170 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_169, x_163);
lean_dec(x_163);
switch (lean_obj_tag(x_160)) {
case 0:
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_160);
if (x_202 == 0)
{
lean_ctor_set_tag(x_160, 3);
x_171 = x_160;
goto block_201;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_160, 0);
lean_inc(x_203);
lean_dec(x_160);
x_204 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_171 = x_204;
goto block_201;
}
}
case 1:
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_160);
if (x_205 == 0)
{
lean_ctor_set_tag(x_160, 2);
x_171 = x_160;
goto block_201;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_160, 0);
lean_inc(x_206);
lean_dec(x_160);
x_207 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_171 = x_207;
goto block_201;
}
}
default: 
{
lean_object* x_208; 
x_208 = lean_box(0);
x_171 = x_208;
goto block_201;
}
}
block_201:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
switch (x_161) {
case 0:
{
lean_object* x_189; 
x_189 = l_Lean_JsonRpc_instToJsonErrorCode___closed__2;
x_174 = x_189;
goto block_188;
}
case 1:
{
lean_object* x_190; 
x_190 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_174 = x_190;
goto block_188;
}
case 2:
{
lean_object* x_191; 
x_191 = l_Lean_JsonRpc_instToJsonErrorCode___closed__6;
x_174 = x_191;
goto block_188;
}
case 3:
{
lean_object* x_192; 
x_192 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_174 = x_192;
goto block_188;
}
case 4:
{
lean_object* x_193; 
x_193 = l_Lean_JsonRpc_instToJsonErrorCode___closed__10;
x_174 = x_193;
goto block_188;
}
case 5:
{
lean_object* x_194; 
x_194 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_174 = x_194;
goto block_188;
}
case 6:
{
lean_object* x_195; 
x_195 = l_Lean_JsonRpc_instToJsonErrorCode___closed__14;
x_174 = x_195;
goto block_188;
}
case 7:
{
lean_object* x_196; 
x_196 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_174 = x_196;
goto block_188;
}
case 8:
{
lean_object* x_197; 
x_197 = l_Lean_JsonRpc_instToJsonErrorCode___closed__18;
x_174 = x_197;
goto block_188;
}
case 9:
{
lean_object* x_198; 
x_198 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_174 = x_198;
goto block_188;
}
case 10:
{
lean_object* x_199; 
x_199 = l_Lean_JsonRpc_instToJsonErrorCode___closed__22;
x_174 = x_199;
goto block_188;
}
default: 
{
lean_object* x_200; 
x_200 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_174 = x_200;
goto block_188;
}
}
block_188:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_175 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_168);
x_178 = l_List_appendTR___rarg(x_177, x_170);
x_179 = l_Lean_Json_mkObj(x_178);
x_180 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_167);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_173);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = l_Lean_Json_mkObj(x_185);
x_187 = l_IO_FS_Stream_writeJson(x_1, x_186, x_3);
return x_187;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 2);
x_7 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_3, 2, x_8);
x_9 = l_IO_FS_Stream_writeMessage(x_2, x_3, x_4);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_ctor_set(x_3, 2, x_7);
x_11 = l_IO_FS_Stream_writeMessage(x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_3, 2, x_13);
x_14 = l_IO_FS_Stream_writeMessage(x_2, x_3, x_4);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_18 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_IO_FS_Stream_writeMessage(x_2, x_20, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(1, 1, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_IO_FS_Stream_writeMessage(x_2, x_25, x_4);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeRequest___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_8);
x_9 = l_IO_FS_Stream_writeMessage(x_2, x_3, x_4);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_7);
x_11 = l_IO_FS_Stream_writeMessage(x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_13);
x_14 = l_IO_FS_Stream_writeMessage(x_2, x_3, x_4);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_IO_FS_Stream_writeMessage(x_2, x_19, x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_22 = x_17;
} else {
 lean_dec_ref(x_17);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(1, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_IO_FS_Stream_writeMessage(x_2, x_24, x_4);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeNotification___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeResponse___rarg), 4, 0);
return x_2;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 2);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 2, x_8);
x_9 = l_IO_FS_Stream_writeMessage(x_2, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_11);
x_15 = l_IO_FS_Stream_writeMessage(x_2, x_14, x_4);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_3, 2);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_apply_1(x_1, x_19);
lean_ctor_set(x_5, 0, x_20);
lean_ctor_set_tag(x_3, 3);
x_21 = l_IO_FS_Stream_writeMessage(x_2, x_3, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_apply_1(x_1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 2, x_24);
x_25 = l_IO_FS_Stream_writeMessage(x_2, x_3, x_4);
return x_25;
}
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_26);
lean_dec(x_3);
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_30 = x_5;
} else {
 lean_dec_ref(x_5);
 x_30 = lean_box(0);
}
x_31 = lean_apply_1(x_1, x_29);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_27);
x_34 = l_IO_FS_Stream_writeMessage(x_2, x_33, x_4);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeResponseErrorWithData___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_JsonRpc_instInhabitedRequestID___closed__1 = _init_l_Lean_JsonRpc_instInhabitedRequestID___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedRequestID___closed__1);
l_Lean_JsonRpc_instInhabitedRequestID___closed__2 = _init_l_Lean_JsonRpc_instInhabitedRequestID___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedRequestID___closed__2);
l_Lean_JsonRpc_instInhabitedRequestID = _init_l_Lean_JsonRpc_instInhabitedRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedRequestID);
l_Lean_JsonRpc_instBEqRequestID___closed__1 = _init_l_Lean_JsonRpc_instBEqRequestID___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instBEqRequestID___closed__1);
l_Lean_JsonRpc_instBEqRequestID = _init_l_Lean_JsonRpc_instBEqRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instBEqRequestID);
l_Lean_JsonRpc_instOrdRequestID___closed__1 = _init_l_Lean_JsonRpc_instOrdRequestID___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instOrdRequestID___closed__1);
l_Lean_JsonRpc_instOrdRequestID = _init_l_Lean_JsonRpc_instOrdRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instOrdRequestID);
l_Lean_JsonRpc_instToStringRequestID___closed__1 = _init_l_Lean_JsonRpc_instToStringRequestID___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instToStringRequestID___closed__1);
l_Lean_JsonRpc_instToStringRequestID___closed__2 = _init_l_Lean_JsonRpc_instToStringRequestID___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instToStringRequestID___closed__2);
l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___closed__1 = _init_l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___closed__1);
l_Lean_JsonRpc_instInhabitedErrorCode = _init_l_Lean_JsonRpc_instInhabitedErrorCode();
l_Lean_JsonRpc_instBEqErrorCode___closed__1 = _init_l_Lean_JsonRpc_instBEqErrorCode___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instBEqErrorCode___closed__1);
l_Lean_JsonRpc_instBEqErrorCode = _init_l_Lean_JsonRpc_instBEqErrorCode();
lean_mark_persistent(l_Lean_JsonRpc_instBEqErrorCode);
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
l_Lean_JsonRpc_instFromJsonErrorCode___closed__12 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__12();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__12);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__13 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__13();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__13);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__14 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__14();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__14);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__15 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__15();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__15);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__16 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__16();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__16);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__17 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__17();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__17);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__18 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__18();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__18);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__19 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__19();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__19);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__20 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__20();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__20);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__21 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__21();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__21);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__22 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__22();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__22);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__23 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__23();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__23);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__24 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__24();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__24);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__25 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__25();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__25);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__26 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__26();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__26);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__27 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__27();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__27);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__28 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__28();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__28);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__29 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__29();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__29);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__30 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__30();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__30);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__31 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__31();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__31);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__32 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__32();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__32);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__33 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__33();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__33);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__34 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__34();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__34);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__35 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__35();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__35);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__36 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__36();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__36);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__37 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__37();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__37);
l_Lean_JsonRpc_instFromJsonErrorCode___closed__38 = _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__38();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonErrorCode___closed__38);
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
l_Lean_JsonRpc_instInhabitedResponseError___closed__1 = _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instInhabitedResponseError___closed__1);
l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp = _init_l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp();
lean_mark_persistent(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp);
l_Lean_JsonRpc_instLTRequestID = _init_l_Lean_JsonRpc_instLTRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instLTRequestID);
l_Lean_JsonRpc_instFromJsonRequestID___closed__1 = _init_l_Lean_JsonRpc_instFromJsonRequestID___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonRequestID___closed__1);
l_Lean_JsonRpc_instFromJsonRequestID___closed__2 = _init_l_Lean_JsonRpc_instFromJsonRequestID___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonRequestID___closed__2);
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
l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1 = _init_l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1);
l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2 = _init_l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2);
l_Lean_JsonRpc_instFromJsonMessage___closed__1 = _init_l_Lean_JsonRpc_instFromJsonMessage___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessage___closed__1);
l_Lean_JsonRpc_instFromJsonMessage___closed__2 = _init_l_Lean_JsonRpc_instFromJsonMessage___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonMessage___closed__2);
l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__1 = _init_l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__1);
l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__2 = _init_l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__2);
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
l_IO_FS_Stream_readRequestAs___closed__6 = _init_l_IO_FS_Stream_readRequestAs___closed__6();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__6);
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
