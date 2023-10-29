// Lean compiler output
// Module: Lean.Data.JsonRpc
// Imports: Init Init.Control Init.System.IO Lean.Data.RBTree Lean.Data.Json
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1661_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequestID;
static lean_object* l_Lean_JsonRpc_instFromJsonRequestID___closed__1;
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__13;
lean_object* l_Lean_JsonNumber_toString(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__7;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__41;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessage___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object*);
static lean_object* l_IO_FS_Stream_readMessage___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__6;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOfNatRequestID(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__5;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_1098____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1661____rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedErrorCode;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__2;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__5;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__12;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object*);
static lean_object* l_Lean_JsonRpc_instToStringRequestID___closed__1;
static lean_object* l_IO_FS_Stream_readResponseAs___closed__2;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__30;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__17;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__10;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__1;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__21;
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_414_(uint8_t, uint8_t);
static lean_object* l_IO_FS_Stream_readRequestAs___closed__2;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode(uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__45;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__27;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__34;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___boxed(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__18;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__33;
static lean_object* l_IO_FS_Stream_readResponseAs___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instLTRequestID;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__9;
static lean_object* l_Lean_JsonRpc_instFromJsonRequestID___closed__2;
static lean_object* l_Lean_JsonRpc_instBEqErrorCode___closed__1;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__3;
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__6;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessage___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__14;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__13;
lean_object* l_IO_FS_Stream_readJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__10;
static lean_object* l_IO_FS_Stream_readNotificationAs___closed__1;
static lean_object* l_Lean_JsonRpc_instToStringRequestID___closed__2;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__9;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequestID;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__29;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_ltProp;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__31;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__11;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Json_Basic_0__Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_22_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__11;
static lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__1;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__48;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__25;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx(uint8_t);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__22;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessage(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__46;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__39;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessage(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
static lean_object* l_IO_FS_Stream_readRequestAs___closed__6;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__19;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID;
static lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___closed__1;
static lean_object* l_IO_FS_Stream_readResponseAs___closed__4;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__9;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessage___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__4;
static lean_object* l_Lean_JsonRpc_instInhabitedRequestID___closed__2;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__8;
static lean_object* l_IO_FS_Stream_readResponseAs___closed__3;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__15;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__6;
static lean_object* l_IO_FS_Stream_readRequestAs___closed__5;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___closed__4;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestIDInstLTRequestID___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__7;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Lean_JsonRpc_instInhabitedResponseError___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___rarg(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___closed__3;
static lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_414____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__12;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__23;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__15;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessage(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__47;
static lean_object* l_IO_FS_Stream_readRequestAs___closed__1;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1467_(lean_object*);
static lean_object* l_Lean_JsonRpc_instBEqRequestID___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__42;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__2;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__11;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__38;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__37;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__3;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__35;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__14;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__2;
static lean_object* l_Lean_JsonRpc_instOrdRequestID___closed__1;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___boxed(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__1;
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__4;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg(lean_object*);
lean_object* l_IO_FS_Stream_writeJson(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__43;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__10;
static lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
static lean_object* l_IO_FS_Stream_readMessage___closed__2;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___rarg(lean_object*);
uint8_t l_Lean_JsonNumber_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1467____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__5;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_data_x3f___default(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_1098_(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1296_(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object*);
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__26;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__8;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessage___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__13;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID(lean_object*);
static lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1296____rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestIDInstLTRequestID(lean_object*, lean_object*);
static lean_object* _init_l_Lean_JsonRpc_instInhabitedRequestID___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
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
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(lean_object* x_1, lean_object* x_2) {
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
x_9 = l___private_Lean_Data_Json_Basic_0__Lean_decEqJsonNumber____x40_Lean_Data_Json_Basic___hyg_22_(x_7, x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34____boxed), 2, 0);
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
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151_(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151_(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonRpc_instOrdRequestID___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151____boxed), 2, 0);
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
x_1 = lean_mk_string_from_bytes("\"", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToStringRequestID___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
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
LEAN_EXPORT uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_414_(uint8_t x_1, uint8_t x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_414____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_414_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_JsonRpc_instBEqErrorCode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_414____boxed), 2, 0);
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
x_1 = lean_mk_string_from_bytes("expected error code", 19);
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
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__4() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__5() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__6() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__7() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__8() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__9() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__10() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__11() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__12() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__13() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__14() {
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
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___closed__15() {
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
x_5 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__3;
x_6 = lean_int_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
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
x_21 = lean_unsigned_to_nat(32001u);
x_22 = lean_nat_dec_eq(x_10, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_unsigned_to_nat(32000u);
x_24 = lean_nat_dec_eq(x_10, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(32800u);
x_26 = lean_nat_dec_eq(x_10, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(32799u);
x_28 = lean_nat_dec_eq(x_10, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(32899u);
x_30 = lean_nat_dec_eq(x_10, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(32900u);
x_32 = lean_nat_dec_eq(x_10, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(32901u);
x_34 = lean_nat_dec_eq(x_10, x_33);
lean_dec(x_10);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_4, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_38;
}
else
{
lean_object* x_39; 
x_39 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__4;
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_10);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_4, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_42;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__5;
return x_43;
}
}
}
else
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_10);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_4, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_46;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__6;
return x_47;
}
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_10);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_4, x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_50;
}
else
{
lean_object* x_51; 
x_51 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__7;
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_10);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_eq(x_4, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_54;
}
else
{
lean_object* x_55; 
x_55 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__8;
return x_55;
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_dec(x_10);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_eq(x_4, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_58;
}
else
{
lean_object* x_59; 
x_59 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__9;
return x_59;
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
lean_dec(x_10);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_eq(x_4, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_62;
}
else
{
lean_object* x_63; 
x_63 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__10;
return x_63;
}
}
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_10);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_nat_dec_eq(x_4, x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_66;
}
else
{
lean_object* x_67; 
x_67 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__11;
return x_67;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
lean_dec(x_10);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_eq(x_4, x_68);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_70;
}
else
{
lean_object* x_71; 
x_71 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__12;
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_10);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_eq(x_4, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_74;
}
else
{
lean_object* x_75; 
x_75 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__13;
return x_75;
}
}
}
else
{
lean_object* x_76; uint8_t x_77; 
lean_dec(x_10);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_eq(x_4, x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_78;
}
else
{
lean_object* x_79; 
x_79 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__14;
return x_79;
}
}
}
else
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_10);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_nat_dec_eq(x_4, x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_82;
}
else
{
lean_object* x_83; 
x_83 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__15;
return x_83;
}
}
}
}
else
{
lean_object* x_84; 
x_84 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_84;
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
x_1 = lean_unsigned_to_nat(32002u);
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
x_1 = lean_unsigned_to_nat(32001u);
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
x_1 = lean_unsigned_to_nat(32801u);
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
x_1 = lean_unsigned_to_nat(32800u);
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
x_1 = lean_unsigned_to_nat(32900u);
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
x_1 = lean_unsigned_to_nat(32901u);
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
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__45;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__46;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_instToJsonErrorCode___closed__47;
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
case 10:
{
lean_object* x_12; 
x_12 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
return x_12;
}
default: 
{
lean_object* x_13; 
x_13 = l_Lean_JsonRpc_instToJsonErrorCode___closed__48;
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_1098____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(x_4, x_7);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_1098_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_1098____rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequest____x40_Lean_Data_JsonRpc___hyg_1098____rarg), 3, 1);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessage___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessage___rarg), 2, 0);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1296____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1296_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1296____rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqNotification____x40_Lean_Data_JsonRpc___hyg_1296____rarg), 3, 1);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessage___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessage___rarg), 2, 0);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1467____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(x_4, x_6);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1467_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1467____rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponse____x40_Lean_Data_JsonRpc___hyg_1467____rarg), 3, 1);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessage___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessage___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_data_x3f___default(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1661____rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(x_4, x_8);
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
x_15 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqErrorCode____x40_Lean_Data_JsonRpc___hyg_414_(x_5, x_9);
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
x_21 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____rarg(x_1, x_7, x_11);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1661_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1661____rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqResponseError____x40_Lean_Data_JsonRpc___hyg_1661____rarg), 3, 1);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessage___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessage___rarg), 2, 0);
return x_2;
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
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestIDInstLTRequestID(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestIDInstLTRequestID___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_JsonRpc_instDecidableLtRequestIDInstLTRequestID(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonRequestID___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("a request id needs to be a number or a string", 45);
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
x_8 = l_Lean_JsonRpc_instFromJsonRequestID___closed__2;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instFromJsonRequestID(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instToJsonRequestID(x_1);
lean_dec(x_1);
return x_2;
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
x_1 = lean_mk_string_from_bytes("2.0", 3);
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
x_1 = lean_mk_string_from_bytes("jsonrpc", 7);
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
x_1 = lean_mk_string_from_bytes("method", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("params", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("id", 2);
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
x_1 = lean_mk_string_from_bytes("result", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("message", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("data", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("code", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonMessage___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error", 5);
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
x_17 = l_List_appendTR___rarg(x_16, x_11);
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
x_26 = l_List_appendTR___rarg(x_25, x_11);
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
x_32 = l_List_appendTR___rarg(x_31, x_11);
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
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_74, 0);
lean_inc(x_115);
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_85 = x_116;
goto block_114;
}
case 1:
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_74, 0);
lean_inc(x_117);
x_118 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_85 = x_118;
goto block_114;
}
default: 
{
lean_object* x_119; 
x_119 = lean_box(0);
x_85 = x_119;
goto block_114;
}
}
block_114:
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
case 10:
{
lean_object* x_112; 
x_112 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_88 = x_112;
goto block_101;
}
default: 
{
lean_object* x_113; 
x_113 = l_Lean_JsonRpc_instToJsonErrorCode___closed__48;
x_88 = x_113;
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
x_92 = l_List_appendTR___rarg(x_91, x_84);
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instToJsonMessage(x_1);
lean_dec(x_1);
return x_2;
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
x_10 = l_Lean_JsonRpc_instFromJsonRequestID___closed__2;
return x_10;
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
x_7 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__3;
x_8 = lean_int_dec_lt(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
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
x_23 = lean_unsigned_to_nat(32001u);
x_24 = lean_nat_dec_eq(x_12, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(32000u);
x_26 = lean_nat_dec_eq(x_12, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(32800u);
x_28 = lean_nat_dec_eq(x_12, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(32799u);
x_30 = lean_nat_dec_eq(x_12, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(32899u);
x_32 = lean_nat_dec_eq(x_12, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(32900u);
x_34 = lean_nat_dec_eq(x_12, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_unsigned_to_nat(32901u);
x_36 = lean_nat_dec_eq(x_12, x_35);
lean_dec(x_12);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_6);
x_37 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_37;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_6, x_38);
lean_dec(x_6);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__4;
return x_41;
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_12);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_eq(x_6, x_42);
lean_dec(x_6);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_44;
}
else
{
lean_object* x_45; 
x_45 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__5;
return x_45;
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_12);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_6, x_46);
lean_dec(x_6);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_48;
}
else
{
lean_object* x_49; 
x_49 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__6;
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_12);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_eq(x_6, x_50);
lean_dec(x_6);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_52;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__7;
return x_53;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_12);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_6, x_54);
lean_dec(x_6);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_56;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__8;
return x_57;
}
}
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_12);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_6, x_58);
lean_dec(x_6);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_60;
}
else
{
lean_object* x_61; 
x_61 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__9;
return x_61;
}
}
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_dec(x_12);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_6, x_62);
lean_dec(x_6);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_64;
}
else
{
lean_object* x_65; 
x_65 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__10;
return x_65;
}
}
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_12);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_6, x_66);
lean_dec(x_6);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_68;
}
else
{
lean_object* x_69; 
x_69 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__11;
return x_69;
}
}
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_dec(x_12);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_6, x_70);
lean_dec(x_6);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_72;
}
else
{
lean_object* x_73; 
x_73 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__12;
return x_73;
}
}
}
else
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_12);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_eq(x_6, x_74);
lean_dec(x_6);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_76;
}
else
{
lean_object* x_77; 
x_77 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__13;
return x_77;
}
}
}
else
{
lean_object* x_78; uint8_t x_79; 
lean_dec(x_12);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_6, x_78);
lean_dec(x_6);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_80;
}
else
{
lean_object* x_81; 
x_81 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__14;
return x_81;
}
}
}
else
{
lean_object* x_82; uint8_t x_83; 
lean_dec(x_12);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_nat_dec_eq(x_6, x_82);
lean_dec(x_6);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_84;
}
else
{
lean_object* x_85; 
x_85 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__15;
return x_85;
}
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_3);
x_86 = l_Lean_JsonRpc_instFromJsonErrorCode___closed__2;
return x_86;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getStr_x3f(x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected structured object, got '", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(80u);
x_11 = l_Lean_Json_pretty(x_3, x_10);
x_12 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("only version 2.0 of JSON RPC is supported", 41);
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
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_JsonRpc_instFromJsonMessage___closed__2;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_59; 
x_12 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_13 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_92; 
x_92 = lean_box(0);
x_59 = x_92;
goto block_91;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_13, 0);
lean_inc(x_93);
x_94 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_95 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
lean_dec(x_95);
lean_dec(x_93);
x_96 = lean_box(0);
x_59 = x_96;
goto block_91;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_13);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_99 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_98);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
lean_dec(x_101);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_97);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set_tag(x_99, 1);
lean_ctor_set(x_99, 0, x_103);
return x_99;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_99);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_93);
lean_ctor_set(x_105, 1, x_97);
lean_ctor_set(x_105, 2, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_99);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_99, 0);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_93);
lean_ctor_set(x_110, 1, x_97);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set(x_99, 0, x_110);
return x_99;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
lean_dec(x_99);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_113, 0, x_93);
lean_ctor_set(x_113, 1, x_97);
lean_ctor_set(x_113, 2, x_112);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
}
block_58:
{
lean_dec(x_14);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_20 = l_Lean_Json_getObjVal_x3f(x_1, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_26 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_24, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_24);
lean_dec(x_18);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_32 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_24, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_18);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_38 = l_Lean_Json_getObjVal_x3f(x_24, x_37);
lean_dec(x_24);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_42, 0, x_18);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_43);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
lean_dec(x_38);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_36);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_46);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_51, 0, x_18);
lean_ctor_set(x_51, 1, x_36);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_52);
lean_ctor_set(x_38, 0, x_51);
return x_38;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_38, 0);
lean_inc(x_53);
lean_dec(x_38);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_55, 0, x_18);
lean_ctor_set(x_55, 1, x_36);
lean_ctor_set(x_55, 2, x_54);
x_56 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_56);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
}
}
}
}
}
}
block_91:
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_59);
x_60 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_61 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_61);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_62; 
x_62 = lean_box(0);
x_14 = x_62;
goto block_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_13, 0);
lean_inc(x_63);
x_64 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_65 = l_Lean_Json_getObjVal_x3f(x_1, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
lean_dec(x_65);
lean_dec(x_63);
x_66 = lean_box(0);
x_14 = x_66;
goto block_58;
}
else
{
uint8_t x_67; 
lean_dec(x_13);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_65, 0, x_69);
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_13);
x_73 = lean_ctor_get(x_61, 0);
lean_inc(x_73);
lean_dec(x_61);
x_74 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_75 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_74);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_tag(x_75, 1);
lean_ctor_set(x_75, 0, x_79);
return x_75;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_75);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_73);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_73);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_75, 0, x_86);
return x_75;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_75, 0);
lean_inc(x_87);
lean_dec(x_75);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_73);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
}
}
}
else
{
lean_object* x_115; 
lean_dec(x_7);
x_115 = l_Lean_JsonRpc_instFromJsonMessage___closed__2;
return x_115;
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
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_instFromJsonMessage(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("not a notfication", 17);
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
lean_object* x_3; lean_object* x_46; lean_object* x_47; 
x_46 = l_Lean_JsonRpc_instToJsonMessage___closed__3;
x_47 = l_Lean_Json_getObjVal_x3f(x_2, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_1);
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
lean_object* x_51; 
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec(x_47);
if (lean_obj_tag(x_51) == 3)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_JsonRpc_instToJsonMessage___closed__1;
x_54 = lean_string_dec_eq(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_1);
x_55 = l_Lean_JsonRpc_instFromJsonMessage___closed__2;
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_91; 
x_56 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_57 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_2, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_110; 
x_110 = lean_box(0);
x_91 = x_110;
goto block_109;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_57, 0);
lean_inc(x_111);
x_112 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_113 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_2, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
lean_dec(x_113);
lean_dec(x_111);
x_114 = lean_box(0);
x_91 = x_114;
goto block_109;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_57);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_117 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_2, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_117);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_111);
lean_ctor_set(x_119, 1, x_115);
lean_ctor_set(x_119, 2, x_118);
x_3 = x_119;
goto block_45;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_111);
lean_ctor_set(x_122, 1, x_115);
lean_ctor_set(x_122, 2, x_121);
x_3 = x_122;
goto block_45;
}
}
}
block_90:
{
lean_dec(x_58);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_59; 
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
lean_dec(x_57);
x_63 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_64 = l_Lean_Json_getObjVal_x3f(x_2, x_63);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
lean_dec(x_62);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
lean_dec(x_64);
x_69 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_70 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_68, x_69);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
lean_dec(x_68);
lean_dec(x_62);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_76 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_68, x_75);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
lean_dec(x_74);
lean_dec(x_68);
lean_dec(x_62);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
return x_76;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
lean_dec(x_76);
x_81 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_82 = l_Lean_Json_getObjVal_x3f(x_68, x_81);
lean_dec(x_68);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_82);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_84, 0, x_62);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_83);
x_85 = lean_unbox(x_74);
lean_dec(x_74);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_85);
x_3 = x_84;
goto block_45;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_88, 0, x_62);
lean_ctor_set(x_88, 1, x_80);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_unbox(x_74);
lean_dec(x_74);
lean_ctor_set_uint8(x_88, sizeof(void*)*3, x_89);
x_3 = x_88;
goto block_45;
}
}
}
}
}
}
block_109:
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_91);
x_92 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_93 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_2, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_dec(x_93);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_94; 
x_94 = lean_box(0);
x_58 = x_94;
goto block_90;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_57, 0);
lean_inc(x_95);
x_96 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_97 = l_Lean_Json_getObjVal_x3f(x_2, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
lean_dec(x_97);
lean_dec(x_95);
x_98 = lean_box(0);
x_58 = x_98;
goto block_90;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_57);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_99);
x_3 = x_100;
goto block_45;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_57);
x_101 = lean_ctor_get(x_93, 0);
lean_inc(x_101);
lean_dec(x_93);
x_102 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_103 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_2, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_103);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_104);
x_3 = x_105;
goto block_45;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_107);
x_3 = x_108;
goto block_45;
}
}
}
}
}
else
{
lean_object* x_123; 
lean_dec(x_51);
lean_dec(x_1);
x_123 = l_Lean_JsonRpc_instFromJsonMessage___closed__2;
return x_123;
}
}
block_45:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_apply_1(x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_18);
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
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
lean_dec(x_3);
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_apply_1(x_1, x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_31);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_3);
lean_dec(x_1);
x_44 = l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___closed__2;
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___boxed), 2, 1);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_instFromJsonNotification___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("JSON '", 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readMessage___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' did not have the format of a JSON-RPC message.\n", 49);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_57; 
x_28 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_29 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__1(x_5, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_79; 
x_79 = lean_box(0);
x_57 = x_79;
goto block_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_29, 0);
lean_inc(x_80);
x_81 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_82 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_5, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
lean_dec(x_82);
lean_dec(x_80);
x_83 = lean_box(0);
x_57 = x_83;
goto block_78;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_29);
lean_dec(x_7);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_86 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_5, x_85);
lean_dec(x_5);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_86);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_6);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_80);
lean_ctor_set(x_92, 1, x_84);
lean_ctor_set(x_92, 2, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_6);
return x_93;
}
}
}
block_56:
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
lean_dec(x_36);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_53, 0, x_32);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_54);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_6);
return x_55;
}
}
}
}
}
}
block_78:
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_57);
x_58 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_59 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_5, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_dec(x_59);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_60; 
x_60 = lean_box(0);
x_30 = x_60;
goto block_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_29, 0);
lean_inc(x_61);
x_62 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_63 = l_Lean_Json_getObjVal_x3f(x_5, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec(x_63);
lean_dec(x_61);
x_64 = lean_box(0);
x_30 = x_64;
goto block_56;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_5);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_6);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_29);
lean_dec(x_7);
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
lean_dec(x_59);
x_69 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_70 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4(x_5, x_69);
lean_dec(x_5);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_70);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_6);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_6);
return x_77;
}
}
}
}
}
else
{
lean_object* x_94; 
lean_dec(x_23);
x_94 = l_Lean_JsonRpc_instFromJsonMessage___closed__1;
x_8 = x_94;
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
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected method '", 17);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', got method '", 15);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unexpected param '", 18);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' for method '", 14);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'\n", 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected JSON-RPC request, got: '", 33);
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
x_20 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
lean_object* x_44; 
x_44 = lean_box(0);
x_24 = x_44;
goto block_43;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_13, 0);
lean_inc(x_45);
lean_dec(x_13);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_24 = x_47;
goto block_43;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_24 = x_49;
goto block_43;
}
}
block_43:
{
lean_object* x_25; 
lean_inc(x_24);
x_25 = lean_apply_1(x_5, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Json_compress(x_24);
x_28 = l_IO_FS_Stream_readRequestAs___closed__3;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_IO_FS_Stream_readRequestAs___closed__4;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_3);
lean_dec(x_3);
x_33 = l_IO_FS_Stream_readRequestAs___closed__5;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_string_append(x_34, x_26);
lean_dec(x_26);
x_36 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_10)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_10;
 lean_ctor_set_tag(x_39, 1);
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_24);
x_40 = lean_ctor_get(x_25, 0);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_11);
lean_ctor_set(x_41, 1, x_3);
lean_ctor_set(x_41, 2, x_40);
if (lean_is_scalar(x_10)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_10;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_9);
return x_42;
}
}
}
}
case 1:
{
uint8_t x_50; 
lean_dec(x_5);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_7);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_51 = lean_ctor_get(x_7, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_8, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_8, 1);
lean_inc(x_53);
lean_dec(x_8);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_52);
x_55 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_58 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_57, x_53);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Json_mkObj(x_61);
x_63 = l_Lean_Json_compress(x_62);
x_64 = l_IO_FS_Stream_readRequestAs___closed__6;
x_65 = lean_string_append(x_64, x_63);
lean_dec(x_63);
x_66 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_68);
return x_7;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_69 = lean_ctor_get(x_7, 1);
lean_inc(x_69);
lean_dec(x_7);
x_70 = lean_ctor_get(x_8, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_8, 1);
lean_inc(x_71);
lean_dec(x_8);
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_70);
x_73 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_76 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_75, x_71);
lean_dec(x_71);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Json_mkObj(x_79);
x_81 = l_Lean_Json_compress(x_80);
x_82 = l_IO_FS_Stream_readRequestAs___closed__6;
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
x_84 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_69);
return x_87;
}
}
case 2:
{
uint8_t x_88; 
lean_dec(x_5);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_7);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_7, 0);
lean_dec(x_89);
x_90 = lean_ctor_get(x_8, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_8, 1);
lean_inc(x_91);
lean_dec(x_8);
x_92 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
switch (lean_obj_tag(x_90)) {
case 0:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
lean_dec(x_90);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_95);
x_101 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Lean_Json_mkObj(x_102);
x_104 = l_Lean_Json_compress(x_103);
x_105 = l_IO_FS_Stream_readRequestAs___closed__6;
x_106 = lean_string_append(x_105, x_104);
lean_dec(x_104);
x_107 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_108 = lean_string_append(x_106, x_107);
x_109 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_109);
return x_7;
}
case 1:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_110 = lean_ctor_get(x_90, 0);
lean_inc(x_110);
lean_dec(x_90);
x_111 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_95);
x_115 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_Lean_Json_mkObj(x_116);
x_118 = l_Lean_Json_compress(x_117);
x_119 = l_IO_FS_Stream_readRequestAs___closed__6;
x_120 = lean_string_append(x_119, x_118);
lean_dec(x_118);
x_121 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_122 = lean_string_append(x_120, x_121);
x_123 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_123);
return x_7;
}
default: 
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_124 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_95);
x_126 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = l_Lean_Json_mkObj(x_127);
x_129 = l_Lean_Json_compress(x_128);
x_130 = l_IO_FS_Stream_readRequestAs___closed__6;
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
x_132 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_133 = lean_string_append(x_131, x_132);
x_134 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_134);
return x_7;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_7, 1);
lean_inc(x_135);
lean_dec(x_7);
x_136 = lean_ctor_get(x_8, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_8, 1);
lean_inc(x_137);
lean_dec(x_8);
x_138 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
switch (lean_obj_tag(x_136)) {
case 0:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_142 = lean_ctor_get(x_136, 0);
lean_inc(x_142);
lean_dec(x_136);
x_143 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_141);
x_147 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = l_Lean_Json_mkObj(x_148);
x_150 = l_Lean_Json_compress(x_149);
x_151 = l_IO_FS_Stream_readRequestAs___closed__6;
x_152 = lean_string_append(x_151, x_150);
lean_dec(x_150);
x_153 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_154 = lean_string_append(x_152, x_153);
x_155 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_135);
return x_156;
}
case 1:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_157 = lean_ctor_get(x_136, 0);
lean_inc(x_157);
lean_dec(x_136);
x_158 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_141);
x_162 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = l_Lean_Json_mkObj(x_163);
x_165 = l_Lean_Json_compress(x_164);
x_166 = l_IO_FS_Stream_readRequestAs___closed__6;
x_167 = lean_string_append(x_166, x_165);
lean_dec(x_165);
x_168 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_169 = lean_string_append(x_167, x_168);
x_170 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_135);
return x_171;
}
default: 
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_172 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_141);
x_174 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
x_176 = l_Lean_Json_mkObj(x_175);
x_177 = l_Lean_Json_compress(x_176);
x_178 = l_IO_FS_Stream_readRequestAs___closed__6;
x_179 = lean_string_append(x_178, x_177);
lean_dec(x_177);
x_180 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_181 = lean_string_append(x_179, x_180);
x_182 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_135);
return x_183;
}
}
}
}
default: 
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_5);
lean_dec(x_3);
x_184 = lean_ctor_get(x_7, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_185 = x_7;
} else {
 lean_dec_ref(x_7);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_8, 0);
lean_inc(x_186);
x_187 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_188 = lean_ctor_get(x_8, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_8, 2);
lean_inc(x_189);
lean_dec(x_8);
x_190 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_190, 0, x_188);
x_191 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_196 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_195, x_189);
lean_dec(x_189);
switch (lean_obj_tag(x_186)) {
case 0:
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_186, 0);
lean_inc(x_234);
lean_dec(x_186);
x_235 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_197 = x_235;
goto block_233;
}
case 1:
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_186, 0);
lean_inc(x_236);
lean_dec(x_186);
x_237 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_197 = x_237;
goto block_233;
}
default: 
{
lean_object* x_238; 
x_238 = lean_box(0);
x_197 = x_238;
goto block_233;
}
}
block_233:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
switch (x_187) {
case 0:
{
lean_object* x_221; 
x_221 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_200 = x_221;
goto block_220;
}
case 1:
{
lean_object* x_222; 
x_222 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_200 = x_222;
goto block_220;
}
case 2:
{
lean_object* x_223; 
x_223 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_200 = x_223;
goto block_220;
}
case 3:
{
lean_object* x_224; 
x_224 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_200 = x_224;
goto block_220;
}
case 4:
{
lean_object* x_225; 
x_225 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_200 = x_225;
goto block_220;
}
case 5:
{
lean_object* x_226; 
x_226 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_200 = x_226;
goto block_220;
}
case 6:
{
lean_object* x_227; 
x_227 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_200 = x_227;
goto block_220;
}
case 7:
{
lean_object* x_228; 
x_228 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_200 = x_228;
goto block_220;
}
case 8:
{
lean_object* x_229; 
x_229 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_200 = x_229;
goto block_220;
}
case 9:
{
lean_object* x_230; 
x_230 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_200 = x_230;
goto block_220;
}
case 10:
{
lean_object* x_231; 
x_231 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_200 = x_231;
goto block_220;
}
default: 
{
lean_object* x_232; 
x_232 = l_Lean_JsonRpc_instToJsonErrorCode___closed__48;
x_200 = x_232;
goto block_220;
}
}
block_220:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_201 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_194);
x_204 = l_List_appendTR___rarg(x_203, x_196);
x_205 = l_Lean_Json_mkObj(x_204);
x_206 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_193);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_199);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
x_212 = l_Lean_Json_mkObj(x_211);
x_213 = l_Lean_Json_compress(x_212);
x_214 = l_IO_FS_Stream_readRequestAs___closed__6;
x_215 = lean_string_append(x_214, x_213);
lean_dec(x_213);
x_216 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_217 = lean_string_append(x_215, x_216);
x_218 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_218, 0, x_217);
if (lean_is_scalar(x_185)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_185;
 lean_ctor_set_tag(x_219, 1);
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_184);
return x_219;
}
}
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_5);
lean_dec(x_3);
x_239 = !lean_is_exclusive(x_7);
if (x_239 == 0)
{
return x_7;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_7, 0);
x_241 = lean_ctor_get(x_7, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_7);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected JSON-RPC notification, got: '", 38);
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
x_26 = l_List_appendTR___rarg(x_25, x_20);
x_27 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Json_mkObj(x_28);
x_30 = l_Lean_Json_compress(x_29);
x_31 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
x_41 = l_List_appendTR___rarg(x_40, x_20);
x_42 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Json_mkObj(x_43);
x_45 = l_Lean_Json_compress(x_44);
x_46 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
x_53 = l_List_appendTR___rarg(x_52, x_20);
x_54 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Json_mkObj(x_55);
x_57 = l_Lean_Json_compress(x_56);
x_58 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
x_79 = l_List_appendTR___rarg(x_78, x_73);
x_80 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Json_mkObj(x_81);
x_83 = l_Lean_Json_compress(x_82);
x_84 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_85 = lean_string_append(x_84, x_83);
lean_dec(x_83);
x_86 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
x_95 = l_List_appendTR___rarg(x_94, x_73);
x_96 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Json_mkObj(x_97);
x_99 = l_Lean_Json_compress(x_98);
x_100 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
x_102 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
x_108 = l_List_appendTR___rarg(x_107, x_73);
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
x_129 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
lean_object* x_153; 
x_153 = lean_box(0);
x_133 = x_153;
goto block_152;
}
else
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_122, 0);
lean_inc(x_154);
lean_dec(x_122);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_133 = x_156;
goto block_152;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_154, 0);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_133 = x_158;
goto block_152;
}
}
block_152:
{
lean_object* x_134; 
lean_inc(x_133);
x_134 = lean_apply_1(x_5, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec(x_134);
x_136 = l_Lean_Json_compress(x_133);
x_137 = l_IO_FS_Stream_readRequestAs___closed__3;
x_138 = lean_string_append(x_137, x_136);
lean_dec(x_136);
x_139 = l_IO_FS_Stream_readRequestAs___closed__4;
x_140 = lean_string_append(x_138, x_139);
x_141 = lean_string_append(x_140, x_3);
lean_dec(x_3);
x_142 = l_IO_FS_Stream_readRequestAs___closed__5;
x_143 = lean_string_append(x_141, x_142);
x_144 = lean_string_append(x_143, x_135);
lean_dec(x_135);
x_145 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_146 = lean_string_append(x_144, x_145);
x_147 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_147, 0, x_146);
if (lean_is_scalar(x_120)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_120;
 lean_ctor_set_tag(x_148, 1);
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_119);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_133);
x_149 = lean_ctor_get(x_134, 0);
lean_inc(x_149);
lean_dec(x_134);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_3);
lean_ctor_set(x_150, 1, x_149);
if (lean_is_scalar(x_120)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_120;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_119);
return x_151;
}
}
}
}
case 2:
{
uint8_t x_159; 
lean_dec(x_5);
lean_dec(x_3);
x_159 = !lean_is_exclusive(x_7);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_160 = lean_ctor_get(x_7, 0);
lean_dec(x_160);
x_161 = lean_ctor_get(x_8, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_8, 1);
lean_inc(x_162);
lean_dec(x_8);
x_163 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
switch (lean_obj_tag(x_161)) {
case 0:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_167 = lean_ctor_get(x_161, 0);
lean_inc(x_167);
lean_dec(x_161);
x_168 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_166);
x_172 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_174 = l_Lean_Json_mkObj(x_173);
x_175 = l_Lean_Json_compress(x_174);
x_176 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_177 = lean_string_append(x_176, x_175);
lean_dec(x_175);
x_178 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_179 = lean_string_append(x_177, x_178);
x_180 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_180);
return x_7;
}
case 1:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_181 = lean_ctor_get(x_161, 0);
lean_inc(x_181);
lean_dec(x_161);
x_182 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_183 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_166);
x_186 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
x_188 = l_Lean_Json_mkObj(x_187);
x_189 = l_Lean_Json_compress(x_188);
x_190 = l_IO_FS_Stream_readNotificationAs___closed__1;
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
default: 
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_195 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_166);
x_197 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = l_Lean_Json_mkObj(x_198);
x_200 = l_Lean_Json_compress(x_199);
x_201 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_202 = lean_string_append(x_201, x_200);
lean_dec(x_200);
x_203 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_204 = lean_string_append(x_202, x_203);
x_205 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_205);
return x_7;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_206 = lean_ctor_get(x_7, 1);
lean_inc(x_206);
lean_dec(x_7);
x_207 = lean_ctor_get(x_8, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_8, 1);
lean_inc(x_208);
lean_dec(x_8);
x_209 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_box(0);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
switch (lean_obj_tag(x_207)) {
case 0:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_213 = lean_ctor_get(x_207, 0);
lean_inc(x_213);
lean_dec(x_207);
x_214 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_215 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_212);
x_218 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
x_220 = l_Lean_Json_mkObj(x_219);
x_221 = l_Lean_Json_compress(x_220);
x_222 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_223 = lean_string_append(x_222, x_221);
lean_dec(x_221);
x_224 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_225 = lean_string_append(x_223, x_224);
x_226 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_206);
return x_227;
}
case 1:
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_228 = lean_ctor_get(x_207, 0);
lean_inc(x_228);
lean_dec(x_207);
x_229 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_229, 0, x_228);
x_230 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_212);
x_233 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = l_Lean_Json_mkObj(x_234);
x_236 = l_Lean_Json_compress(x_235);
x_237 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_238 = lean_string_append(x_237, x_236);
lean_dec(x_236);
x_239 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_240 = lean_string_append(x_238, x_239);
x_241 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_241, 0, x_240);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_206);
return x_242;
}
default: 
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_243 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_212);
x_245 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
x_247 = l_Lean_Json_mkObj(x_246);
x_248 = l_Lean_Json_compress(x_247);
x_249 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_250 = lean_string_append(x_249, x_248);
lean_dec(x_248);
x_251 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_252 = lean_string_append(x_250, x_251);
x_253 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_253, 0, x_252);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_206);
return x_254;
}
}
}
}
default: 
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_5);
lean_dec(x_3);
x_255 = lean_ctor_get(x_7, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_256 = x_7;
} else {
 lean_dec_ref(x_7);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_8, 0);
lean_inc(x_257);
x_258 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_259 = lean_ctor_get(x_8, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_8, 2);
lean_inc(x_260);
lean_dec(x_8);
x_261 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_261, 0, x_259);
x_262 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
x_264 = lean_box(0);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_267 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_266, x_260);
lean_dec(x_260);
switch (lean_obj_tag(x_257)) {
case 0:
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_257, 0);
lean_inc(x_305);
lean_dec(x_257);
x_306 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_306, 0, x_305);
x_268 = x_306;
goto block_304;
}
case 1:
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_257, 0);
lean_inc(x_307);
lean_dec(x_257);
x_308 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_308, 0, x_307);
x_268 = x_308;
goto block_304;
}
default: 
{
lean_object* x_309; 
x_309 = lean_box(0);
x_268 = x_309;
goto block_304;
}
}
block_304:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
switch (x_258) {
case 0:
{
lean_object* x_292; 
x_292 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_271 = x_292;
goto block_291;
}
case 1:
{
lean_object* x_293; 
x_293 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_271 = x_293;
goto block_291;
}
case 2:
{
lean_object* x_294; 
x_294 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_271 = x_294;
goto block_291;
}
case 3:
{
lean_object* x_295; 
x_295 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_271 = x_295;
goto block_291;
}
case 4:
{
lean_object* x_296; 
x_296 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_271 = x_296;
goto block_291;
}
case 5:
{
lean_object* x_297; 
x_297 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_271 = x_297;
goto block_291;
}
case 6:
{
lean_object* x_298; 
x_298 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_271 = x_298;
goto block_291;
}
case 7:
{
lean_object* x_299; 
x_299 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_271 = x_299;
goto block_291;
}
case 8:
{
lean_object* x_300; 
x_300 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_271 = x_300;
goto block_291;
}
case 9:
{
lean_object* x_301; 
x_301 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_271 = x_301;
goto block_291;
}
case 10:
{
lean_object* x_302; 
x_302 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_271 = x_302;
goto block_291;
}
default: 
{
lean_object* x_303; 
x_303 = l_Lean_JsonRpc_instToJsonErrorCode___closed__48;
x_271 = x_303;
goto block_291;
}
}
block_291:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_272 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_265);
x_275 = l_List_appendTR___rarg(x_274, x_267);
x_276 = l_Lean_Json_mkObj(x_275);
x_277 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_264);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_270);
lean_ctor_set(x_280, 1, x_279);
x_281 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
x_283 = l_Lean_Json_mkObj(x_282);
x_284 = l_Lean_Json_compress(x_283);
x_285 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_286 = lean_string_append(x_285, x_284);
lean_dec(x_284);
x_287 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_288 = lean_string_append(x_286, x_287);
x_289 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_289, 0, x_288);
if (lean_is_scalar(x_256)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_256;
 lean_ctor_set_tag(x_290, 1);
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_255);
return x_290;
}
}
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_5);
lean_dec(x_3);
x_310 = !lean_is_exclusive(x_7);
if (x_310 == 0)
{
return x_7;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_7, 0);
x_312 = lean_ctor_get(x_7, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_7);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected JSON-RPC response, got: '", 34);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected id ", 12);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", got id ", 9);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readResponseAs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unexpected result '", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
lean_inc(x_1);
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
lean_dec(x_2);
lean_dec(x_1);
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
x_26 = l_List_appendTR___rarg(x_25, x_20);
x_27 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Json_mkObj(x_28);
x_30 = l_Lean_Json_compress(x_29);
x_31 = l_IO_FS_Stream_readResponseAs___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
x_41 = l_List_appendTR___rarg(x_40, x_20);
x_42 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Json_mkObj(x_43);
x_45 = l_Lean_Json_compress(x_44);
x_46 = l_IO_FS_Stream_readResponseAs___closed__1;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
x_53 = l_List_appendTR___rarg(x_52, x_20);
x_54 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Json_mkObj(x_55);
x_57 = l_Lean_Json_compress(x_56);
x_58 = l_IO_FS_Stream_readResponseAs___closed__1;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
x_79 = l_List_appendTR___rarg(x_78, x_73);
x_80 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Json_mkObj(x_81);
x_83 = l_Lean_Json_compress(x_82);
x_84 = l_IO_FS_Stream_readResponseAs___closed__1;
x_85 = lean_string_append(x_84, x_83);
lean_dec(x_83);
x_86 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
x_95 = l_List_appendTR___rarg(x_94, x_73);
x_96 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Json_mkObj(x_97);
x_99 = l_Lean_Json_compress(x_98);
x_100 = l_IO_FS_Stream_readResponseAs___closed__1;
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
x_102 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
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
x_108 = l_List_appendTR___rarg(x_107, x_73);
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
lean_ctor_set(x_118, 1, x_63);
return x_118;
}
}
}
}
case 1:
{
lean_object* x_119; 
lean_dec(x_8);
x_119 = lean_ctor_get(x_7, 1);
lean_inc(x_119);
lean_dec(x_7);
x_4 = lean_box(0);
x_6 = x_119;
goto _start;
}
case 2:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_153; 
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_ctor_get(x_7, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_122 = x_7;
} else {
 lean_dec_ref(x_7);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_8, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_8, 1);
lean_inc(x_124);
lean_dec(x_8);
x_153 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(x_123, x_3);
if (x_153 == 0)
{
lean_dec(x_124);
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_3, 0);
lean_inc(x_154);
lean_dec(x_3);
x_155 = l_Lean_JsonRpc_instToStringRequestID___closed__1;
x_156 = lean_string_append(x_155, x_154);
lean_dec(x_154);
x_157 = lean_string_append(x_156, x_155);
x_125 = x_157;
goto block_152;
}
case 1:
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_3, 0);
lean_inc(x_158);
lean_dec(x_3);
x_159 = l_Lean_JsonNumber_toString(x_158);
x_125 = x_159;
goto block_152;
}
default: 
{
lean_object* x_160; 
x_160 = l_Lean_JsonRpc_instToStringRequestID___closed__2;
x_125 = x_160;
goto block_152;
}
}
}
else
{
lean_object* x_161; 
lean_dec(x_123);
lean_dec(x_122);
lean_inc(x_124);
x_161 = lean_apply_1(x_5, x_124);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_3);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lean_Json_compress(x_124);
x_164 = l_IO_FS_Stream_readResponseAs___closed__4;
x_165 = lean_string_append(x_164, x_163);
lean_dec(x_163);
x_166 = l_IO_FS_Stream_readRequestAs___closed__5;
x_167 = lean_string_append(x_165, x_166);
x_168 = lean_string_append(x_167, x_162);
lean_dec(x_162);
x_169 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_170 = lean_string_append(x_168, x_169);
x_171 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_121);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_124);
x_173 = lean_ctor_get(x_161, 0);
lean_inc(x_173);
lean_dec(x_161);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_3);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_121);
return x_175;
}
}
block_152:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = l_IO_FS_Stream_readResponseAs___closed__2;
x_127 = lean_string_append(x_126, x_125);
lean_dec(x_125);
x_128 = l_IO_FS_Stream_readResponseAs___closed__3;
x_129 = lean_string_append(x_127, x_128);
switch (lean_obj_tag(x_123)) {
case 0:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_130 = lean_ctor_get(x_123, 0);
lean_inc(x_130);
lean_dec(x_123);
x_131 = l_Lean_JsonRpc_instToStringRequestID___closed__1;
x_132 = lean_string_append(x_131, x_130);
lean_dec(x_130);
x_133 = lean_string_append(x_132, x_131);
x_134 = lean_string_append(x_129, x_133);
lean_dec(x_133);
x_135 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_136 = lean_string_append(x_134, x_135);
x_137 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_137, 0, x_136);
if (lean_is_scalar(x_122)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_122;
 lean_ctor_set_tag(x_138, 1);
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_121);
return x_138;
}
case 1:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_123, 0);
lean_inc(x_139);
lean_dec(x_123);
x_140 = l_Lean_JsonNumber_toString(x_139);
x_141 = lean_string_append(x_129, x_140);
lean_dec(x_140);
x_142 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_143 = lean_string_append(x_141, x_142);
x_144 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_144, 0, x_143);
if (lean_is_scalar(x_122)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_122;
 lean_ctor_set_tag(x_145, 1);
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_121);
return x_145;
}
default: 
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = l_Lean_JsonRpc_instToStringRequestID___closed__2;
x_147 = lean_string_append(x_129, x_146);
x_148 = l_Lean_JsonRpc_instInhabitedRequestID___closed__1;
x_149 = lean_string_append(x_147, x_148);
x_150 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_150, 0, x_149);
if (lean_is_scalar(x_122)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_122;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_121);
return x_151;
}
}
}
}
default: 
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_176 = lean_ctor_get(x_7, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_177 = x_7;
} else {
 lean_dec_ref(x_7);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_8, 0);
lean_inc(x_178);
x_179 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_180 = lean_ctor_get(x_8, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_8, 2);
lean_inc(x_181);
lean_dec(x_8);
x_182 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_182, 0, x_180);
x_183 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = lean_box(0);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_188 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_187, x_181);
lean_dec(x_181);
switch (lean_obj_tag(x_178)) {
case 0:
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_178, 0);
lean_inc(x_226);
lean_dec(x_178);
x_227 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_189 = x_227;
goto block_225;
}
case 1:
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_178, 0);
lean_inc(x_228);
lean_dec(x_178);
x_229 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_229, 0, x_228);
x_189 = x_229;
goto block_225;
}
default: 
{
lean_object* x_230; 
x_230 = lean_box(0);
x_189 = x_230;
goto block_225;
}
}
block_225:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
switch (x_179) {
case 0:
{
lean_object* x_213; 
x_213 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_192 = x_213;
goto block_212;
}
case 1:
{
lean_object* x_214; 
x_214 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_192 = x_214;
goto block_212;
}
case 2:
{
lean_object* x_215; 
x_215 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_192 = x_215;
goto block_212;
}
case 3:
{
lean_object* x_216; 
x_216 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_192 = x_216;
goto block_212;
}
case 4:
{
lean_object* x_217; 
x_217 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_192 = x_217;
goto block_212;
}
case 5:
{
lean_object* x_218; 
x_218 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_192 = x_218;
goto block_212;
}
case 6:
{
lean_object* x_219; 
x_219 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_192 = x_219;
goto block_212;
}
case 7:
{
lean_object* x_220; 
x_220 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_192 = x_220;
goto block_212;
}
case 8:
{
lean_object* x_221; 
x_221 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_192 = x_221;
goto block_212;
}
case 9:
{
lean_object* x_222; 
x_222 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_192 = x_222;
goto block_212;
}
case 10:
{
lean_object* x_223; 
x_223 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_192 = x_223;
goto block_212;
}
default: 
{
lean_object* x_224; 
x_224 = l_Lean_JsonRpc_instToJsonErrorCode___closed__48;
x_192 = x_224;
goto block_212;
}
}
block_212:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_193 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_186);
x_196 = l_List_appendTR___rarg(x_195, x_188);
x_197 = l_Lean_Json_mkObj(x_196);
x_198 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_185);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_191);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = l_Lean_Json_mkObj(x_203);
x_205 = l_Lean_Json_compress(x_204);
x_206 = l_IO_FS_Stream_readResponseAs___closed__1;
x_207 = lean_string_append(x_206, x_205);
lean_dec(x_205);
x_208 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__4___closed__2;
x_209 = lean_string_append(x_207, x_208);
x_210 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_210, 0, x_209);
if (lean_is_scalar(x_177)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_177;
 lean_ctor_set_tag(x_211, 1);
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_176);
return x_211;
}
}
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_7);
if (x_231 == 0)
{
return x_7;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_7, 0);
x_233 = lean_ctor_get(x_7, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_7);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
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
x_19 = l_List_appendTR___rarg(x_18, x_13);
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
x_29 = l_List_appendTR___rarg(x_28, x_13);
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
x_36 = l_List_appendTR___rarg(x_35, x_13);
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
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_83, 0);
lean_inc(x_125);
x_126 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_94 = x_126;
goto block_124;
}
case 1:
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_83, 0);
lean_inc(x_127);
x_128 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_94 = x_128;
goto block_124;
}
default: 
{
lean_object* x_129; 
x_129 = lean_box(0);
x_94 = x_129;
goto block_124;
}
}
block_124:
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
case 10:
{
lean_object* x_122; 
x_122 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_97 = x_122;
goto block_111;
}
default: 
{
lean_object* x_123; 
x_123 = l_Lean_JsonRpc_instToJsonErrorCode___closed__48;
x_97 = x_123;
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
x_101 = l_List_appendTR___rarg(x_100, x_93);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_IO_FS_Stream_writeMessage(x_2, x_10, x_4);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_IO_FS_Stream_writeMessage(x_2, x_14, x_4);
lean_dec(x_14);
return x_15;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_IO_FS_Stream_writeMessage(x_2, x_9, x_4);
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_IO_FS_Stream_writeMessage(x_2, x_13, x_4);
lean_dec(x_13);
return x_14;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeResponseError(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeResponseErrorWithData___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_JsonRpc_instToJsonErrorCode___closed__45 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__45();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__45);
l_Lean_JsonRpc_instToJsonErrorCode___closed__46 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__46();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__46);
l_Lean_JsonRpc_instToJsonErrorCode___closed__47 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__47();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__47);
l_Lean_JsonRpc_instToJsonErrorCode___closed__48 = _init_l_Lean_JsonRpc_instToJsonErrorCode___closed__48();
lean_mark_persistent(l_Lean_JsonRpc_instToJsonErrorCode___closed__48);
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
