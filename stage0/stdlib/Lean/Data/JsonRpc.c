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
uint8_t lean_string_compare(lean_object*, lean_object*);
uint8_t l_Lean_JsonNumber_lt(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Json_Parser_strCore(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_Parser_num(lean_object*);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_IO_FS_Stream_writeJson(lean_object*, lean_object*);
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IO_FS_Stream_readJson(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object*);
uint8_t l_Lean_instDecidableEqJsonNumber_decEq(lean_object*, lean_object*);
lean_object* l_Lean_Option_toJson___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Lean_instHashableJsonNumber_hash(lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_str_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value;
static const lean_ctor_object l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value)}};
static const lean_object* l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instInhabitedRequestID_default = (const lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instInhabitedRequestID = (const lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequestID_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequestID_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instBEqRequestID___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instBEqRequestID_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instBEqRequestID___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instBEqRequestID___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instBEqRequestID = (const lean_object*)&l_Lean_JsonRpc_instBEqRequestID___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_JsonRpc_instHashableRequestID_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instHashableRequestID_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instHashableRequestID___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instHashableRequestID_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instHashableRequestID___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instHashableRequestID___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instHashableRequestID = (const lean_object*)&l_Lean_JsonRpc_instHashableRequestID___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instOrdRequestID_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instOrdRequestID___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instOrdRequestID_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instOrdRequestID___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instOrdRequestID___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instOrdRequestID = (const lean_object*)&l_Lean_JsonRpc_instOrdRequestID___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOfNatRequestID(lean_object*);
static const lean_string_object l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0_value;
static const lean_string_object l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instToStringRequestID___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instToStringRequestID___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instToStringRequestID___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instToStringRequestID___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instToStringRequestID = (const lean_object*)&l_Lean_JsonRpc_instToStringRequestID___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedErrorCode_default;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedErrorCode;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqErrorCode_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instBEqErrorCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instBEqErrorCode_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instBEqErrorCode___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instBEqErrorCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instBEqErrorCode = (const lean_object*)&l_Lean_JsonRpc_instBEqErrorCode___closed__0_value;
static const lean_string_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expected error code"};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__0_value)}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24;
static lean_once_cell_t l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(11) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(8) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instFromJsonErrorCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instFromJsonErrorCode = (const lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___closed__0_value;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22;
static lean_once_cell_t l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instToJsonErrorCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instToJsonErrorCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instToJsonErrorCode = (const lean_object*)&l_Lean_JsonRpc_instToJsonErrorCode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_JsonRpc_instInhabitedMessage_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value),((lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instInhabitedMessage_default___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instInhabitedMessage_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instInhabitedMessage_default = (const lean_object*)&l_Lean_JsonRpc_instInhabitedMessage_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instInhabitedMessage = (const lean_object*)&l_Lean_JsonRpc_instInhabitedMessage_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ofMessage_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ofMessage_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ofMessage_x3f(lean_object*);
static const lean_ctor_object l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value),((lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___redArg();
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError___redArg();
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage = (const lean_object*)&l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ofMessage_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instCoeStringRequestID___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instCoeStringRequestID___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instCoeStringRequestID___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instCoeStringRequestID___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instCoeStringRequestID = (const lean_object*)&l_Lean_JsonRpc_instCoeStringRequestID___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID = (const lean_object*)&l_Lean_JsonRpc_instCoeJsonNumberRequestID___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_RequestID_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ltProp;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instLTRequestID;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "a request id needs to be a number or a string"};
static const lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__0_value)}};
static const lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instFromJsonRequestID___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instFromJsonRequestID___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instFromJsonRequestID___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonRequestID___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instFromJsonRequestID = (const lean_object*)&l_Lean_JsonRpc_instFromJsonRequestID___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instToJsonRequestID___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instToJsonRequestID___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instToJsonRequestID___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instToJsonRequestID___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instToJsonRequestID = (const lean_object*)&l_Lean_JsonRpc_instToJsonRequestID___closed__0_value;
static const lean_string_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "jsonrpc"};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0_value;
static const lean_string_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "2.0"};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1_value)}};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0_value),((lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__2_value)}};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3_value;
static const lean_string_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4_value;
static const lean_string_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5_value;
static const lean_string_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "params"};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6_value;
static const lean_string_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7_value;
static const lean_string_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8_value;
static const lean_string_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9_value;
static const lean_string_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10_value;
static const lean_string_object l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instToJsonMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_Structured_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___closed__0_value;
static const lean_closure_object l_Lean_JsonRpc_instToJsonMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___closed__1_value;
static const lean_closure_object l_Lean_JsonRpc_instToJsonMessage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instToJsonMessage___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instToJsonMessage___closed__0_value),((lean_object*)&l_Lean_JsonRpc_instToJsonMessage___closed__1_value)} };
static const lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__2 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instToJsonMessage = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessage___closed__2_value;
static const lean_string_object l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "only version 2.0 of JSON RPC is supported"};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0_value)}};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instFromJsonMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getStr_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessage___closed__0_value;
static const lean_closure_object l_Lean_JsonRpc_instFromJsonMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_Structured_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessage___closed__1_value;
static const lean_closure_object l_Lean_JsonRpc_instFromJsonMessage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instFromJsonMessage___lam__0, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonRequestID___closed__0_value),((lean_object*)&l_Lean_JsonRpc_instFromJsonErrorCode___closed__0_value),((lean_object*)&l_Lean_JsonRpc_instFromJsonMessage___closed__0_value),((lean_object*)&l_Lean_JsonRpc_instFromJsonMessage___closed__1_value)} };
static const lean_object* l_Lean_JsonRpc_instFromJsonMessage___closed__2 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessage___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instFromJsonMessage = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessage___closed__2_value;
static const lean_string_object l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "not a notification"};
static const lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0_value)}};
static const lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value),((lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value)}};
static const lean_object* l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instInhabitedMessageMetaData_default = (const lean_object*)&l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instInhabitedMessageMetaData = (const lean_object*)&l_Lean_JsonRpc_instInhabitedMessageMetaData_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_metaData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_toMessage(lean_object*);
static const lean_string_object l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expected \""};
static const lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0 = (const lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0_value;
static const lean_ctor_object l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__0_value)}};
static const lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1 = (const lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "expected response error message kind"};
static const lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0 = (const lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0_value;
static const lean_ctor_object l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__0_value)}};
static const lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1 = (const lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1_value;
static const lean_string_object l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "expected `id`, `jsonrpc` or `error` field"};
static const lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2 = (const lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2_value;
static const lean_ctor_object l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__2_value)}};
static const lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3 = (const lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3_value;
static const lean_string_object l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "expected `method` or `result` field"};
static const lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4 = (const lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4_value;
static const lean_ctor_object l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__4_value)}};
static const lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5 = (const lean_object*)&l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedMessageDirection_default;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instInhabitedMessageDirection;
static const lean_string_object l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0_value)}};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1_value;
static const lean_string_object l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "serverToClient"};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2_value;
static const lean_string_object l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "clientToServer"};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3_value;
static const lean_string_object l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4_value)}};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection___closed__0_value;
static const lean_ctor_object l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3_value)}};
static const lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0_value;
static const lean_ctor_object l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2_value)}};
static const lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instToJsonMessageDirection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instToJsonMessageDirection___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessageDirection___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instToJsonMessageDirection = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessageDirection___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__0_value)}};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0_value;
static const lean_string_object l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "responseError"};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1_value;
static const lean_string_object l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "request"};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2_value;
static const lean_string_object l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "notification"};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3_value;
static const lean_string_object l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "response"};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__4_value)}};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8_value;
static const lean_ctor_object l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instFromJsonMessageKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instFromJsonMessageKind_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instFromJsonMessageKind = (const lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind___closed__0_value;
static const lean_ctor_object l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2_value)}};
static const lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0_value;
static const lean_ctor_object l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3_value)}};
static const lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1_value;
static const lean_ctor_object l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4_value)}};
static const lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2_value;
static const lean_ctor_object l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1_value)}};
static const lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_JsonRpc_instToJsonMessageKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_JsonRpc_instToJsonMessageKind___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessageKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_JsonRpc_instToJsonMessageKind = (const lean_object*)&l_Lean_JsonRpc_instToJsonMessageKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IO_FS_Stream_readMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "JSON '"};
static const lean_object* l_Lean_IO_FS_Stream_readMessage___closed__0 = (const lean_object*)&l_Lean_IO_FS_Stream_readMessage___closed__0_value;
static const lean_string_object l_Lean_IO_FS_Stream_readMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "' did not have the format of a JSON-RPC message.\n"};
static const lean_object* l_Lean_IO_FS_Stream_readMessage___closed__1 = (const lean_object*)&l_Lean_IO_FS_Stream_readMessage___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Expected method '"};
static const lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0 = (const lean_object*)&l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0_value;
static const lean_string_object l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "', got method '"};
static const lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1 = (const lean_object*)&l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1_value;
static const lean_string_object l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2 = (const lean_object*)&l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2_value;
static const lean_string_object l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unexpected param '"};
static const lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3 = (const lean_object*)&l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3_value;
static const lean_string_object l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "' for method '"};
static const lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4 = (const lean_object*)&l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4_value;
static const lean_string_object l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'\n"};
static const lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5 = (const lean_object*)&l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5_value;
static const lean_string_object l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Expected JSON-RPC request, got: '"};
static const lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__6 = (const lean_object*)&l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IO_FS_Stream_readNotificationAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Expected JSON-RPC notification, got: '"};
static const lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg___closed__0 = (const lean_object*)&l_Lean_IO_FS_Stream_readNotificationAs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Expected id "};
static const lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__0 = (const lean_object*)&l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__0_value;
static const lean_string_object l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", got id "};
static const lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__1 = (const lean_object*)&l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__1_value;
static const lean_string_object l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unexpected result '"};
static const lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__2 = (const lean_object*)&l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__2_value;
static const lean_string_object l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Expected JSON-RPC response, got: '"};
static const lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__3 = (const lean_object*)&l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_JsonRpc_RequestID_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 2)
{
return v_k_6_;
}
else
{
lean_object* v_s_7_; lean_object* v___x_8_; 
v_s_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_s_7_);
lean_dec(v_t_5_);
v___x_8_ = lean_apply_1(v_k_6_, v_s_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_JsonRpc_RequestID_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_str_elim___redArg(lean_object* v_t_21_, lean_object* v_str_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_21_, v_str_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_str_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_str_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_25_, v_str_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim___redArg(lean_object* v_t_29_, lean_object* v_num_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_29_, v_num_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_num_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_33_, v_num_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim___redArg(lean_object* v_t_37_, lean_object* v_null_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_37_, v_null_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_null_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_41_, v_null_43_);
return v___x_44_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequestID_beq(lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
switch(lean_obj_tag(v_x_50_))
{
case 0:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v_s_52_; lean_object* v_s_53_; uint8_t v___x_54_; 
v_s_52_ = lean_ctor_get(v_x_50_, 0);
v_s_53_ = lean_ctor_get(v_x_51_, 0);
v___x_54_ = lean_string_dec_eq(v_s_52_, v_s_53_);
return v___x_54_;
}
else
{
uint8_t v___x_55_; 
v___x_55_ = 0;
return v___x_55_;
}
}
case 1:
{
if (lean_obj_tag(v_x_51_) == 1)
{
lean_object* v_n_56_; lean_object* v_n_57_; uint8_t v___x_58_; 
v_n_56_ = lean_ctor_get(v_x_50_, 0);
v_n_57_ = lean_ctor_get(v_x_51_, 0);
v___x_58_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_56_, v_n_57_);
return v___x_58_;
}
else
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
}
default: 
{
if (lean_obj_tag(v_x_51_) == 2)
{
uint8_t v___x_60_; 
v___x_60_ = 1;
return v___x_60_;
}
else
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequestID_beq___boxed(lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_x_62_, v_x_63_);
lean_dec(v_x_63_);
lean_dec(v_x_62_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT uint64_t l_Lean_JsonRpc_instHashableRequestID_hash(lean_object* v_x_68_){
_start:
{
switch(lean_obj_tag(v_x_68_))
{
case 0:
{
lean_object* v_s_69_; uint64_t v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; 
v_s_69_ = lean_ctor_get(v_x_68_, 0);
v___x_70_ = 0ULL;
v___x_71_ = lean_string_hash(v_s_69_);
v___x_72_ = lean_uint64_mix_hash(v___x_70_, v___x_71_);
return v___x_72_;
}
case 1:
{
lean_object* v_n_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; 
v_n_73_ = lean_ctor_get(v_x_68_, 0);
v___x_74_ = 1ULL;
v___x_75_ = l_Lean_instHashableJsonNumber_hash(v_n_73_);
v___x_76_ = lean_uint64_mix_hash(v___x_74_, v___x_75_);
return v___x_76_;
}
default: 
{
uint64_t v___x_77_; 
v___x_77_ = 2ULL;
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instHashableRequestID_hash___boxed(lean_object* v_x_78_){
_start:
{
uint64_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lean_JsonRpc_instHashableRequestID_hash(v_x_78_);
lean_dec(v_x_78_);
v_r_80_ = lean_box_uint64(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instOrdRequestID_ord(lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
switch(lean_obj_tag(v_x_83_))
{
case 0:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_object* v_s_85_; lean_object* v_s_86_; uint8_t v___x_87_; 
v_s_85_ = lean_ctor_get(v_x_83_, 0);
lean_inc_ref(v_s_85_);
lean_dec_ref_known(v_x_83_, 1);
v_s_86_ = lean_ctor_get(v_x_84_, 0);
lean_inc_ref(v_s_86_);
lean_dec_ref_known(v_x_84_, 1);
v___x_87_ = lean_string_compare(v_s_85_, v_s_86_);
lean_dec_ref(v_s_86_);
lean_dec_ref(v_s_85_);
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
lean_dec_ref_known(v_x_83_, 1);
lean_dec(v_x_84_);
v___x_88_ = 0;
return v___x_88_;
}
}
case 1:
{
switch(lean_obj_tag(v_x_84_))
{
case 0:
{
uint8_t v___x_89_; 
lean_dec_ref_known(v_x_84_, 1);
lean_dec_ref_known(v_x_83_, 1);
v___x_89_ = 2;
return v___x_89_;
}
case 1:
{
lean_object* v_n_90_; lean_object* v_n_91_; uint8_t v___x_92_; 
v_n_90_ = lean_ctor_get(v_x_83_, 0);
lean_inc_ref_n(v_n_90_, 2);
lean_dec_ref_known(v_x_83_, 1);
v_n_91_ = lean_ctor_get(v_x_84_, 0);
lean_inc_ref_n(v_n_91_, 2);
lean_dec_ref_known(v_x_84_, 1);
v___x_92_ = l_Lean_JsonNumber_lt(v_n_90_, v_n_91_);
if (v___x_92_ == 0)
{
uint8_t v___x_93_; 
v___x_93_ = l_Lean_JsonNumber_lt(v_n_91_, v_n_90_);
if (v___x_93_ == 0)
{
uint8_t v___x_94_; 
v___x_94_ = 1;
return v___x_94_;
}
else
{
uint8_t v___x_95_; 
v___x_95_ = 2;
return v___x_95_;
}
}
else
{
uint8_t v___x_96_; 
lean_dec_ref(v_n_91_);
lean_dec_ref(v_n_90_);
v___x_96_ = 0;
return v___x_96_;
}
}
default: 
{
uint8_t v___x_97_; 
lean_dec_ref_known(v_x_83_, 1);
lean_dec(v_x_84_);
v___x_97_ = 0;
return v___x_97_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_84_) == 2)
{
uint8_t v___x_98_; 
v___x_98_ = 1;
return v___x_98_;
}
else
{
uint8_t v___x_99_; 
lean_dec(v_x_84_);
v___x_99_ = 2;
return v___x_99_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID_ord___boxed(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Lean_JsonRpc_instOrdRequestID_ord(v_x_100_, v_x_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOfNatRequestID(lean_object* v_n_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = l_Lean_JsonNumber_fromNat(v_n_106_);
v___x_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0(lean_object* v_x_111_){
_start:
{
switch(lean_obj_tag(v_x_111_))
{
case 0:
{
lean_object* v_s_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_s_112_ = lean_ctor_get(v_x_111_, 0);
lean_inc_ref(v_s_112_);
lean_dec_ref_known(v_x_111_, 1);
v___x_113_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_114_ = lean_string_append(v___x_113_, v_s_112_);
lean_dec_ref(v_s_112_);
v___x_115_ = lean_string_append(v___x_114_, v___x_113_);
return v___x_115_;
}
case 1:
{
lean_object* v_n_116_; lean_object* v___x_117_; 
v_n_116_ = lean_ctor_get(v_x_111_, 0);
lean_inc_ref(v_n_116_);
lean_dec_ref_known(v_x_111_, 1);
v___x_117_ = l_Lean_JsonNumber_toString(v_n_116_);
return v___x_117_;
}
default: 
{
lean_object* v___x_118_; 
v___x_118_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___impl(uint8_t v_x_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_box(v_x_121_);
v___x_123_ = lean_obj_tag_nat(v___x_122_);
lean_dec(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___impl___boxed(lean_object* v_x_124_){
_start:
{
uint8_t v_x_4__boxed_125_; lean_object* v_res_126_; 
v_x_4__boxed_125_ = lean_unbox(v_x_124_);
v_res_126_ = l_Lean_JsonRpc_ErrorCode_ctorIdx___impl(v_x_4__boxed_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(lean_object* v_k_127_){
_start:
{
lean_inc(v_k_127_);
return v_k_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg___boxed(lean_object* v_k_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(v_k_128_);
lean_dec(v_k_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim(lean_object* v_motive_130_, lean_object* v_ctorIdx_131_, uint8_t v_t_132_, lean_object* v_h_133_, lean_object* v_k_134_){
_start:
{
lean_inc(v_k_134_);
return v_k_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___boxed(lean_object* v_motive_135_, lean_object* v_ctorIdx_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_k_139_){
_start:
{
uint8_t v_t_boxed_140_; lean_object* v_res_141_; 
v_t_boxed_140_ = lean_unbox(v_t_137_);
v_res_141_ = l_Lean_JsonRpc_ErrorCode_ctorElim(v_motive_135_, v_ctorIdx_136_, v_t_boxed_140_, v_h_138_, v_k_139_);
lean_dec(v_k_139_);
lean_dec(v_ctorIdx_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(lean_object* v_parseError_142_){
_start:
{
lean_inc(v_parseError_142_);
return v_parseError_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg___boxed(lean_object* v_parseError_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(v_parseError_143_);
lean_dec(v_parseError_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_object* v_motive_145_, uint8_t v_t_146_, lean_object* v_h_147_, lean_object* v_parseError_148_){
_start:
{
lean_inc(v_parseError_148_);
return v_parseError_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___boxed(lean_object* v_motive_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_parseError_152_){
_start:
{
uint8_t v_t_boxed_153_; lean_object* v_res_154_; 
v_t_boxed_153_ = lean_unbox(v_t_150_);
v_res_154_ = l_Lean_JsonRpc_ErrorCode_parseError_elim(v_motive_149_, v_t_boxed_153_, v_h_151_, v_parseError_152_);
lean_dec(v_parseError_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(lean_object* v_invalidRequest_155_){
_start:
{
lean_inc(v_invalidRequest_155_);
return v_invalidRequest_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg___boxed(lean_object* v_invalidRequest_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(v_invalidRequest_156_);
lean_dec(v_invalidRequest_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_object* v_motive_158_, uint8_t v_t_159_, lean_object* v_h_160_, lean_object* v_invalidRequest_161_){
_start:
{
lean_inc(v_invalidRequest_161_);
return v_invalidRequest_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___boxed(lean_object* v_motive_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_invalidRequest_165_){
_start:
{
uint8_t v_t_boxed_166_; lean_object* v_res_167_; 
v_t_boxed_166_ = lean_unbox(v_t_163_);
v_res_167_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(v_motive_162_, v_t_boxed_166_, v_h_164_, v_invalidRequest_165_);
lean_dec(v_invalidRequest_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(lean_object* v_methodNotFound_168_){
_start:
{
lean_inc(v_methodNotFound_168_);
return v_methodNotFound_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg___boxed(lean_object* v_methodNotFound_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(v_methodNotFound_169_);
lean_dec(v_methodNotFound_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(lean_object* v_motive_171_, uint8_t v_t_172_, lean_object* v_h_173_, lean_object* v_methodNotFound_174_){
_start:
{
lean_inc(v_methodNotFound_174_);
return v_methodNotFound_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___boxed(lean_object* v_motive_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_methodNotFound_178_){
_start:
{
uint8_t v_t_boxed_179_; lean_object* v_res_180_; 
v_t_boxed_179_ = lean_unbox(v_t_176_);
v_res_180_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(v_motive_175_, v_t_boxed_179_, v_h_177_, v_methodNotFound_178_);
lean_dec(v_methodNotFound_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(lean_object* v_invalidParams_181_){
_start:
{
lean_inc(v_invalidParams_181_);
return v_invalidParams_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg___boxed(lean_object* v_invalidParams_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(v_invalidParams_182_);
lean_dec(v_invalidParams_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_object* v_motive_184_, uint8_t v_t_185_, lean_object* v_h_186_, lean_object* v_invalidParams_187_){
_start:
{
lean_inc(v_invalidParams_187_);
return v_invalidParams_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___boxed(lean_object* v_motive_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_invalidParams_191_){
_start:
{
uint8_t v_t_boxed_192_; lean_object* v_res_193_; 
v_t_boxed_192_ = lean_unbox(v_t_189_);
v_res_193_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim(v_motive_188_, v_t_boxed_192_, v_h_190_, v_invalidParams_191_);
lean_dec(v_invalidParams_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(lean_object* v_internalError_194_){
_start:
{
lean_inc(v_internalError_194_);
return v_internalError_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg___boxed(lean_object* v_internalError_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(v_internalError_195_);
lean_dec(v_internalError_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_object* v_motive_197_, uint8_t v_t_198_, lean_object* v_h_199_, lean_object* v_internalError_200_){
_start:
{
lean_inc(v_internalError_200_);
return v_internalError_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___boxed(lean_object* v_motive_201_, lean_object* v_t_202_, lean_object* v_h_203_, lean_object* v_internalError_204_){
_start:
{
uint8_t v_t_boxed_205_; lean_object* v_res_206_; 
v_t_boxed_205_ = lean_unbox(v_t_202_);
v_res_206_ = l_Lean_JsonRpc_ErrorCode_internalError_elim(v_motive_201_, v_t_boxed_205_, v_h_203_, v_internalError_204_);
lean_dec(v_internalError_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(lean_object* v_serverNotInitialized_207_){
_start:
{
lean_inc(v_serverNotInitialized_207_);
return v_serverNotInitialized_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg___boxed(lean_object* v_serverNotInitialized_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(v_serverNotInitialized_208_);
lean_dec(v_serverNotInitialized_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_object* v_motive_210_, uint8_t v_t_211_, lean_object* v_h_212_, lean_object* v_serverNotInitialized_213_){
_start:
{
lean_inc(v_serverNotInitialized_213_);
return v_serverNotInitialized_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___boxed(lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_serverNotInitialized_217_){
_start:
{
uint8_t v_t_boxed_218_; lean_object* v_res_219_; 
v_t_boxed_218_ = lean_unbox(v_t_215_);
v_res_219_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(v_motive_214_, v_t_boxed_218_, v_h_216_, v_serverNotInitialized_217_);
lean_dec(v_serverNotInitialized_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(lean_object* v_unknownErrorCode_220_){
_start:
{
lean_inc(v_unknownErrorCode_220_);
return v_unknownErrorCode_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg___boxed(lean_object* v_unknownErrorCode_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(v_unknownErrorCode_221_);
lean_dec(v_unknownErrorCode_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_object* v_motive_223_, uint8_t v_t_224_, lean_object* v_h_225_, lean_object* v_unknownErrorCode_226_){
_start:
{
lean_inc(v_unknownErrorCode_226_);
return v_unknownErrorCode_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___boxed(lean_object* v_motive_227_, lean_object* v_t_228_, lean_object* v_h_229_, lean_object* v_unknownErrorCode_230_){
_start:
{
uint8_t v_t_boxed_231_; lean_object* v_res_232_; 
v_t_boxed_231_ = lean_unbox(v_t_228_);
v_res_232_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(v_motive_227_, v_t_boxed_231_, v_h_229_, v_unknownErrorCode_230_);
lean_dec(v_unknownErrorCode_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(lean_object* v_contentModified_233_){
_start:
{
lean_inc(v_contentModified_233_);
return v_contentModified_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg___boxed(lean_object* v_contentModified_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(v_contentModified_234_);
lean_dec(v_contentModified_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_object* v_motive_236_, uint8_t v_t_237_, lean_object* v_h_238_, lean_object* v_contentModified_239_){
_start:
{
lean_inc(v_contentModified_239_);
return v_contentModified_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___boxed(lean_object* v_motive_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_contentModified_243_){
_start:
{
uint8_t v_t_boxed_244_; lean_object* v_res_245_; 
v_t_boxed_244_ = lean_unbox(v_t_241_);
v_res_245_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim(v_motive_240_, v_t_boxed_244_, v_h_242_, v_contentModified_243_);
lean_dec(v_contentModified_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(lean_object* v_requestCancelled_246_){
_start:
{
lean_inc(v_requestCancelled_246_);
return v_requestCancelled_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg___boxed(lean_object* v_requestCancelled_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(v_requestCancelled_247_);
lean_dec(v_requestCancelled_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_object* v_motive_249_, uint8_t v_t_250_, lean_object* v_h_251_, lean_object* v_requestCancelled_252_){
_start:
{
lean_inc(v_requestCancelled_252_);
return v_requestCancelled_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___boxed(lean_object* v_motive_253_, lean_object* v_t_254_, lean_object* v_h_255_, lean_object* v_requestCancelled_256_){
_start:
{
uint8_t v_t_boxed_257_; lean_object* v_res_258_; 
v_t_boxed_257_ = lean_unbox(v_t_254_);
v_res_258_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(v_motive_253_, v_t_boxed_257_, v_h_255_, v_requestCancelled_256_);
lean_dec(v_requestCancelled_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(lean_object* v_rpcNeedsReconnect_259_){
_start:
{
lean_inc(v_rpcNeedsReconnect_259_);
return v_rpcNeedsReconnect_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg___boxed(lean_object* v_rpcNeedsReconnect_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(v_rpcNeedsReconnect_260_);
lean_dec(v_rpcNeedsReconnect_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(lean_object* v_motive_262_, uint8_t v_t_263_, lean_object* v_h_264_, lean_object* v_rpcNeedsReconnect_265_){
_start:
{
lean_inc(v_rpcNeedsReconnect_265_);
return v_rpcNeedsReconnect_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___boxed(lean_object* v_motive_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_rpcNeedsReconnect_269_){
_start:
{
uint8_t v_t_boxed_270_; lean_object* v_res_271_; 
v_t_boxed_270_ = lean_unbox(v_t_267_);
v_res_271_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(v_motive_266_, v_t_boxed_270_, v_h_268_, v_rpcNeedsReconnect_269_);
lean_dec(v_rpcNeedsReconnect_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(lean_object* v_workerExited_272_){
_start:
{
lean_inc(v_workerExited_272_);
return v_workerExited_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg___boxed(lean_object* v_workerExited_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(v_workerExited_273_);
lean_dec(v_workerExited_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim(lean_object* v_motive_275_, uint8_t v_t_276_, lean_object* v_h_277_, lean_object* v_workerExited_278_){
_start:
{
lean_inc(v_workerExited_278_);
return v_workerExited_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___boxed(lean_object* v_motive_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_workerExited_282_){
_start:
{
uint8_t v_t_boxed_283_; lean_object* v_res_284_; 
v_t_boxed_283_ = lean_unbox(v_t_280_);
v_res_284_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim(v_motive_279_, v_t_boxed_283_, v_h_281_, v_workerExited_282_);
lean_dec(v_workerExited_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(lean_object* v_workerCrashed_285_){
_start:
{
lean_inc(v_workerCrashed_285_);
return v_workerCrashed_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg___boxed(lean_object* v_workerCrashed_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(v_workerCrashed_286_);
lean_dec(v_workerCrashed_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_object* v_motive_288_, uint8_t v_t_289_, lean_object* v_h_290_, lean_object* v_workerCrashed_291_){
_start:
{
lean_inc(v_workerCrashed_291_);
return v_workerCrashed_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___boxed(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_workerCrashed_295_){
_start:
{
uint8_t v_t_boxed_296_; lean_object* v_res_297_; 
v_t_boxed_296_ = lean_unbox(v_t_293_);
v_res_297_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(v_motive_292_, v_t_boxed_296_, v_h_294_, v_workerCrashed_295_);
lean_dec(v_workerCrashed_295_);
return v_res_297_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode_default(void){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode(void){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = 0;
return v___x_299_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqErrorCode_beq(uint8_t v_x_300_, uint8_t v_y_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_302_ = lean_box(v_x_300_);
v___x_303_ = lean_obj_tag_nat(v___x_302_);
lean_dec(v___x_302_);
v___x_304_ = lean_box(v_y_301_);
v___x_305_ = lean_obj_tag_nat(v___x_304_);
lean_dec(v___x_304_);
v___x_306_ = lean_nat_dec_eq(v___x_303_, v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode_beq___boxed(lean_object* v_x_307_, lean_object* v_y_308_){
_start:
{
uint8_t v_x_24__boxed_309_; uint8_t v_y_25__boxed_310_; uint8_t v_res_311_; lean_object* v_r_312_; 
v_x_24__boxed_309_ = lean_unbox(v_x_307_);
v_y_25__boxed_310_ = lean_unbox(v_y_308_);
v_res_311_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_x_24__boxed_309_, v_y_25__boxed_310_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(32700u);
v___x_319_ = lean_nat_to_int(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2);
v___x_321_ = lean_int_neg(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(32600u);
v___x_323_ = lean_nat_to_int(v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4);
v___x_325_ = lean_int_neg(v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_unsigned_to_nat(32601u);
v___x_327_ = lean_nat_to_int(v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6);
v___x_329_ = lean_int_neg(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(32602u);
v___x_331_ = lean_nat_to_int(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8);
v___x_333_ = lean_int_neg(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(32603u);
v___x_335_ = lean_nat_to_int(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10);
v___x_337_ = lean_int_neg(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(32002u);
v___x_339_ = lean_nat_to_int(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12);
v___x_341_ = lean_int_neg(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(32001u);
v___x_343_ = lean_nat_to_int(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14);
v___x_345_ = lean_int_neg(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(32801u);
v___x_347_ = lean_nat_to_int(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16);
v___x_349_ = lean_int_neg(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(32800u);
v___x_351_ = lean_nat_to_int(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18);
v___x_353_ = lean_int_neg(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(32900u);
v___x_355_ = lean_nat_to_int(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20);
v___x_357_ = lean_int_neg(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(32901u);
v___x_359_ = lean_nat_to_int(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22);
v___x_361_ = lean_int_neg(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_unsigned_to_nat(32902u);
v___x_363_ = lean_nat_to_int(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24);
v___x_365_ = lean_int_neg(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(lean_object* v_x_402_){
_start:
{
if (lean_obj_tag(v_x_402_) == 2)
{
lean_object* v_n_405_; lean_object* v_mantissa_406_; lean_object* v_exponent_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v_n_405_ = lean_ctor_get(v_x_402_, 0);
v_mantissa_406_ = lean_ctor_get(v_n_405_, 0);
v_exponent_407_ = lean_ctor_get(v_n_405_, 1);
v___x_408_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_409_ = lean_int_dec_eq(v_mantissa_406_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_411_ = lean_int_dec_eq(v_mantissa_406_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_413_ = lean_int_dec_eq(v_mantissa_406_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_415_ = lean_int_dec_eq(v_mantissa_406_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_417_ = lean_int_dec_eq(v_mantissa_406_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_419_ = lean_int_dec_eq(v_mantissa_406_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_421_ = lean_int_dec_eq(v_mantissa_406_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_423_ = lean_int_dec_eq(v_mantissa_406_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_425_ = lean_int_dec_eq(v_mantissa_406_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_427_ = lean_int_dec_eq(v_mantissa_406_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_429_ = lean_int_dec_eq(v_mantissa_406_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_431_ = lean_int_dec_eq(v_mantissa_406_, v___x_430_);
if (v___x_431_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_nat_dec_eq(v_exponent_407_, v___x_432_);
if (v___x_433_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_434_; 
v___x_434_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_434_;
}
}
}
else
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_nat_dec_eq(v_exponent_407_, v___x_435_);
if (v___x_436_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_437_;
}
}
}
else
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_nat_dec_eq(v_exponent_407_, v___x_438_);
if (v___x_439_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_440_; 
v___x_440_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_440_;
}
}
}
else
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_nat_dec_eq(v_exponent_407_, v___x_441_);
if (v___x_442_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_443_; 
v___x_443_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_443_;
}
}
}
else
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_nat_dec_eq(v_exponent_407_, v___x_444_);
if (v___x_445_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_446_; 
v___x_446_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_446_;
}
}
}
else
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = lean_nat_dec_eq(v_exponent_407_, v___x_447_);
if (v___x_448_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_449_;
}
}
}
else
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_nat_dec_eq(v_exponent_407_, v___x_450_);
if (v___x_451_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_452_; 
v___x_452_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_452_;
}
}
}
else
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_nat_dec_eq(v_exponent_407_, v___x_453_);
if (v___x_454_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_455_; 
v___x_455_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_455_;
}
}
}
else
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_nat_dec_eq(v_exponent_407_, v___x_456_);
if (v___x_457_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_458_;
}
}
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_nat_dec_eq(v_exponent_407_, v___x_459_);
if (v___x_460_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_461_;
}
}
}
else
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_nat_dec_eq(v_exponent_407_, v___x_462_);
if (v___x_463_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_464_; 
v___x_464_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_464_;
}
}
}
else
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_nat_dec_eq(v_exponent_407_, v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_403_;
}
else
{
lean_object* v___x_467_; 
v___x_467_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_467_;
}
}
}
else
{
goto v___jp_403_;
}
v___jp_403_:
{
lean_object* v___x_404_; 
v___x_404_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed(lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(v_x_468_);
lean_dec(v_x_468_);
return v_res_469_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_473_ = l_Lean_JsonNumber_fromInt(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0);
v___x_475_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_477_ = l_Lean_JsonNumber_fromInt(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2);
v___x_479_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_481_ = l_Lean_JsonNumber_fromInt(v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4);
v___x_483_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_485_ = l_Lean_JsonNumber_fromInt(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6);
v___x_487_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_489_ = l_Lean_JsonNumber_fromInt(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8);
v___x_491_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_493_ = l_Lean_JsonNumber_fromInt(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10);
v___x_495_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_497_ = l_Lean_JsonNumber_fromInt(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12);
v___x_499_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_501_ = l_Lean_JsonNumber_fromInt(v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14);
v___x_503_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_505_ = l_Lean_JsonNumber_fromInt(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16);
v___x_507_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_509_ = l_Lean_JsonNumber_fromInt(v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18);
v___x_511_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_513_ = l_Lean_JsonNumber_fromInt(v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20);
v___x_515_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_517_ = l_Lean_JsonNumber_fromInt(v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22);
v___x_519_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t v_x_520_){
_start:
{
switch(v_x_520_)
{
case 0:
{
lean_object* v___x_521_; 
v___x_521_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
return v___x_521_;
}
case 1:
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
return v___x_522_;
}
case 2:
{
lean_object* v___x_523_; 
v___x_523_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
return v___x_523_;
}
case 3:
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
return v___x_524_;
}
case 4:
{
lean_object* v___x_525_; 
v___x_525_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
return v___x_525_;
}
case 5:
{
lean_object* v___x_526_; 
v___x_526_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
return v___x_526_;
}
case 6:
{
lean_object* v___x_527_; 
v___x_527_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
return v___x_527_;
}
case 7:
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
return v___x_528_;
}
case 8:
{
lean_object* v___x_529_; 
v___x_529_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
return v___x_529_;
}
case 9:
{
lean_object* v___x_530_; 
v___x_530_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
return v___x_530_;
}
case 10:
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
return v___x_531_;
}
default: 
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object* v_x_533_){
_start:
{
uint8_t v_x_474__boxed_534_; lean_object* v_res_535_; 
v_x_474__boxed_534_ = lean_unbox(v_x_533_);
v_res_535_ = l_Lean_JsonRpc_instToJsonErrorCode___lam__0(v_x_474__boxed_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___impl(lean_object* v_x_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_tag_nat(v_x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___impl___boxed(lean_object* v_x_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_JsonRpc_Message_ctorIdx___impl(v_x_540_);
lean_dec_ref(v_x_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___redArg(lean_object* v_t_542_, lean_object* v_k_543_){
_start:
{
switch(lean_obj_tag(v_t_542_))
{
case 0:
{
lean_object* v_id_544_; lean_object* v_method_545_; lean_object* v_params_x3f_546_; lean_object* v___x_547_; 
v_id_544_ = lean_ctor_get(v_t_542_, 0);
lean_inc(v_id_544_);
v_method_545_ = lean_ctor_get(v_t_542_, 1);
lean_inc_ref(v_method_545_);
v_params_x3f_546_ = lean_ctor_get(v_t_542_, 2);
lean_inc(v_params_x3f_546_);
lean_dec_ref_known(v_t_542_, 3);
v___x_547_ = lean_apply_3(v_k_543_, v_id_544_, v_method_545_, v_params_x3f_546_);
return v___x_547_;
}
case 1:
{
lean_object* v_method_548_; lean_object* v_params_x3f_549_; lean_object* v___x_550_; 
v_method_548_ = lean_ctor_get(v_t_542_, 0);
lean_inc_ref(v_method_548_);
v_params_x3f_549_ = lean_ctor_get(v_t_542_, 1);
lean_inc(v_params_x3f_549_);
lean_dec_ref_known(v_t_542_, 2);
v___x_550_ = lean_apply_2(v_k_543_, v_method_548_, v_params_x3f_549_);
return v___x_550_;
}
case 2:
{
lean_object* v_id_551_; lean_object* v_result_552_; lean_object* v___x_553_; 
v_id_551_ = lean_ctor_get(v_t_542_, 0);
lean_inc(v_id_551_);
v_result_552_ = lean_ctor_get(v_t_542_, 1);
lean_inc(v_result_552_);
lean_dec_ref_known(v_t_542_, 2);
v___x_553_ = lean_apply_2(v_k_543_, v_id_551_, v_result_552_);
return v___x_553_;
}
default: 
{
lean_object* v_id_554_; uint8_t v_code_555_; lean_object* v_message_556_; lean_object* v_data_x3f_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_id_554_ = lean_ctor_get(v_t_542_, 0);
lean_inc(v_id_554_);
v_code_555_ = lean_ctor_get_uint8(v_t_542_, sizeof(void*)*3);
v_message_556_ = lean_ctor_get(v_t_542_, 1);
lean_inc_ref(v_message_556_);
v_data_x3f_557_ = lean_ctor_get(v_t_542_, 2);
lean_inc(v_data_x3f_557_);
lean_dec_ref_known(v_t_542_, 3);
v___x_558_ = lean_box(v_code_555_);
v___x_559_ = lean_apply_4(v_k_543_, v_id_554_, v___x_558_, v_message_556_, v_data_x3f_557_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim(lean_object* v_motive_560_, lean_object* v_ctorIdx_561_, lean_object* v_t_562_, lean_object* v_h_563_, lean_object* v_k_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_562_, v_k_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___boxed(lean_object* v_motive_566_, lean_object* v_ctorIdx_567_, lean_object* v_t_568_, lean_object* v_h_569_, lean_object* v_k_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_JsonRpc_Message_ctorElim(v_motive_566_, v_ctorIdx_567_, v_t_568_, v_h_569_, v_k_570_);
lean_dec(v_ctorIdx_567_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim___redArg(lean_object* v_t_572_, lean_object* v_request_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_572_, v_request_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim(lean_object* v_motive_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_request_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_576_, v_request_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim___redArg(lean_object* v_t_580_, lean_object* v_notification_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_580_, v_notification_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim(lean_object* v_motive_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_notification_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_584_, v_notification_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim___redArg(lean_object* v_t_588_, lean_object* v_response_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_588_, v_response_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim(lean_object* v_motive_591_, lean_object* v_t_592_, lean_object* v_h_593_, lean_object* v_response_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_592_, v_response_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim___redArg(lean_object* v_t_596_, lean_object* v_responseError_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_596_, v_responseError_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim(lean_object* v_motive_599_, lean_object* v_t_600_, lean_object* v_h_601_, lean_object* v_responseError_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_600_, v_responseError_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default___redArg(lean_object* v_inst_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default));
v___x_612_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
lean_ctor_set(v___x_613_, 2, v_inst_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default(lean_object* v_00_u03b1_614_, lean_object* v_inst_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___redArg(lean_object* v_inst_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object* v_a_619_, lean_object* v_inst_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_620_);
return v___x_621_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq___redArg(lean_object* v_inst_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v_id_625_; lean_object* v_method_626_; lean_object* v_param_627_; lean_object* v_id_628_; lean_object* v_method_629_; lean_object* v_param_630_; uint8_t v___x_631_; 
v_id_625_ = lean_ctor_get(v_x_623_, 0);
lean_inc(v_id_625_);
v_method_626_ = lean_ctor_get(v_x_623_, 1);
lean_inc_ref(v_method_626_);
v_param_627_ = lean_ctor_get(v_x_623_, 2);
lean_inc(v_param_627_);
lean_dec_ref(v_x_623_);
v_id_628_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_id_628_);
v_method_629_ = lean_ctor_get(v_x_624_, 1);
lean_inc_ref(v_method_629_);
v_param_630_ = lean_ctor_get(v_x_624_, 2);
lean_inc(v_param_630_);
lean_dec_ref(v_x_624_);
v___x_631_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_625_, v_id_628_);
lean_dec(v_id_628_);
lean_dec(v_id_625_);
if (v___x_631_ == 0)
{
lean_dec(v_param_630_);
lean_dec_ref(v_method_629_);
lean_dec(v_param_627_);
lean_dec_ref(v_method_626_);
lean_dec_ref(v_inst_622_);
return v___x_631_;
}
else
{
uint8_t v___x_632_; 
v___x_632_ = lean_string_dec_eq(v_method_626_, v_method_629_);
lean_dec_ref(v_method_629_);
lean_dec_ref(v_method_626_);
if (v___x_632_ == 0)
{
lean_dec(v_param_630_);
lean_dec(v_param_627_);
lean_dec_ref(v_inst_622_);
return v___x_632_;
}
else
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_apply_2(v_inst_622_, v_param_627_, v_param_630_);
v___x_634_ = lean_unbox(v___x_633_);
return v___x_634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___redArg___boxed(lean_object* v_inst_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
uint8_t v_res_638_; lean_object* v_r_639_; 
v_res_638_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_635_, v_x_636_, v_x_637_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq(lean_object* v_00_u03b1_640_, lean_object* v_inst_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_641_, v_x_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___boxed(lean_object* v_00_u03b1_645_, lean_object* v_inst_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l_Lean_JsonRpc_instBEqRequest_beq(v_00_u03b1_645_, v_inst_646_, v_x_647_, v_x_648_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object* v_inst_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_652_, 0, lean_box(0));
lean_closure_set(v___x_652_, 1, v_inst_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object* v_00_u03b1_653_, lean_object* v_inst_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_655_, 0, lean_box(0));
lean_closure_set(v___x_655_, 1, v_inst_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object* v_inst_656_, lean_object* v_r_657_){
_start:
{
lean_object* v_id_658_; lean_object* v_method_659_; lean_object* v_param_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_680_; 
v_id_658_ = lean_ctor_get(v_r_657_, 0);
v_method_659_ = lean_ctor_get(v_r_657_, 1);
v_param_660_ = lean_ctor_get(v_r_657_, 2);
v_isSharedCheck_680_ = !lean_is_exclusive(v_r_657_);
if (v_isSharedCheck_680_ == 0)
{
v___x_662_ = v_r_657_;
v_isShared_663_ = v_isSharedCheck_680_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_param_660_);
lean_inc(v_method_659_);
lean_inc(v_id_658_);
lean_dec(v_r_657_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_680_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_656_, v_param_660_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v___x_665_; lean_object* v___x_667_; 
lean_dec_ref_known(v___x_664_, 1);
v___x_665_ = lean_box(0);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 2, v___x_665_);
v___x_667_ = v___x_662_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_id_658_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_method_659_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_679_; 
v_a_669_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_679_ == 0)
{
v___x_671_ = v___x_664_;
v_isShared_672_ = v_isSharedCheck_679_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_664_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_679_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 2, v___x_674_);
v___x_676_ = v___x_662_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_id_658_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_method_659_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object* v_inst_681_){
_start:
{
lean_object* v___f_682_; 
v___f_682_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_682_, 0, v_inst_681_);
return v___f_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object* v_00_u03b1_683_, lean_object* v_inst_684_){
_start:
{
lean_object* v___f_685_; 
v___f_685_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_685_, 0, v_inst_684_);
return v___f_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object* v_x_686_){
_start:
{
if (lean_obj_tag(v_x_686_) == 0)
{
lean_object* v___x_687_; 
v___x_687_ = lean_box(0);
return v___x_687_;
}
else
{
lean_object* v_val_688_; lean_object* v___x_689_; 
v_val_688_ = lean_ctor_get(v_x_686_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v_x_686_, 1);
v___x_689_ = l_Lean_Json_Structured_toJson(v_val_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ofMessage_x3f(lean_object* v_x_690_){
_start:
{
if (lean_obj_tag(v_x_690_) == 0)
{
lean_object* v_id_691_; lean_object* v_method_692_; lean_object* v_params_x3f_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_702_; 
v_id_691_ = lean_ctor_get(v_x_690_, 0);
v_method_692_ = lean_ctor_get(v_x_690_, 1);
v_params_x3f_693_ = lean_ctor_get(v_x_690_, 2);
v_isSharedCheck_702_ = !lean_is_exclusive(v_x_690_);
if (v_isSharedCheck_702_ == 0)
{
v___x_695_ = v_x_690_;
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_params_x3f_693_);
lean_inc(v_method_692_);
lean_inc(v_id_691_);
lean_dec(v_x_690_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_702_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_693_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 2, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_id_691_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_method_692_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v___x_697_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; 
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
else
{
lean_object* v___x_703_; 
lean_dec_ref(v_x_690_);
v___x_703_ = lean_box(0);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default___redArg(lean_object* v_inst_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v_inst_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default(lean_object* v_00_u03b1_707_, lean_object* v_inst_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___redArg(lean_object* v_inst_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object* v_a_712_, lean_object* v_inst_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_713_);
return v___x_714_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq___redArg(lean_object* v_inst_715_, lean_object* v_x_716_, lean_object* v_x_717_){
_start:
{
lean_object* v_method_718_; lean_object* v_param_719_; lean_object* v_method_720_; lean_object* v_param_721_; uint8_t v___x_722_; 
v_method_718_ = lean_ctor_get(v_x_716_, 0);
lean_inc_ref(v_method_718_);
v_param_719_ = lean_ctor_get(v_x_716_, 1);
lean_inc(v_param_719_);
lean_dec_ref(v_x_716_);
v_method_720_ = lean_ctor_get(v_x_717_, 0);
lean_inc_ref(v_method_720_);
v_param_721_ = lean_ctor_get(v_x_717_, 1);
lean_inc(v_param_721_);
lean_dec_ref(v_x_717_);
v___x_722_ = lean_string_dec_eq(v_method_718_, v_method_720_);
lean_dec_ref(v_method_720_);
lean_dec_ref(v_method_718_);
if (v___x_722_ == 0)
{
lean_dec(v_param_721_);
lean_dec(v_param_719_);
lean_dec_ref(v_inst_715_);
return v___x_722_;
}
else
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = lean_apply_2(v_inst_715_, v_param_719_, v_param_721_);
v___x_724_ = lean_unbox(v___x_723_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___redArg___boxed(lean_object* v_inst_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
uint8_t v_res_728_; lean_object* v_r_729_; 
v_res_728_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_725_, v_x_726_, v_x_727_);
v_r_729_ = lean_box(v_res_728_);
return v_r_729_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq(lean_object* v_00_u03b1_730_, lean_object* v_inst_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
uint8_t v___x_734_; 
v___x_734_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_731_, v_x_732_, v_x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___boxed(lean_object* v_00_u03b1_735_, lean_object* v_inst_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = l_Lean_JsonRpc_instBEqNotification_beq(v_00_u03b1_735_, v_inst_736_, v_x_737_, v_x_738_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___redArg(lean_object* v_inst_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(v___x_742_, 0, lean_box(0));
lean_closure_set(v___x_742_, 1, v_inst_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object* v_00_u03b1_743_, lean_object* v_inst_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(v___x_745_, 0, lean_box(0));
lean_closure_set(v___x_745_, 1, v_inst_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(lean_object* v_inst_746_, lean_object* v_r_747_){
_start:
{
lean_object* v_method_748_; lean_object* v_param_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_769_; 
v_method_748_ = lean_ctor_get(v_r_747_, 0);
v_param_749_ = lean_ctor_get(v_r_747_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_r_747_);
if (v_isSharedCheck_769_ == 0)
{
v___x_751_ = v_r_747_;
v_isShared_752_ = v_isSharedCheck_769_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_param_749_);
lean_inc(v_method_748_);
lean_dec(v_r_747_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_769_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_746_, v_param_749_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v___x_754_; lean_object* v___x_756_; 
lean_dec_ref_known(v___x_753_, 1);
v___x_754_ = lean_box(0);
if (v_isShared_752_ == 0)
{
lean_ctor_set_tag(v___x_751_, 1);
lean_ctor_set(v___x_751_, 1, v___x_754_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_method_748_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_768_; 
v_a_758_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_768_ == 0)
{
v___x_760_ = v___x_753_;
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_753_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_767_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_765_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set_tag(v___x_751_, 1);
lean_ctor_set(v___x_751_, 1, v___x_763_);
v___x_765_ = v___x_751_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_method_748_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(lean_object* v_inst_770_){
_start:
{
lean_object* v___f_771_; 
v___f_771_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_771_, 0, v_inst_770_);
return v___f_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object* v_00_u03b1_772_, lean_object* v_inst_773_){
_start:
{
lean_object* v___f_774_; 
v___f_774_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_774_, 0, v_inst_773_);
return v___f_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ofMessage_x3f(lean_object* v_x_775_){
_start:
{
if (lean_obj_tag(v_x_775_) == 1)
{
lean_object* v_method_776_; lean_object* v_params_x3f_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_786_; 
v_method_776_ = lean_ctor_get(v_x_775_, 0);
v_params_x3f_777_ = lean_ctor_get(v_x_775_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_x_775_);
if (v_isSharedCheck_786_ == 0)
{
v___x_779_ = v_x_775_;
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_params_x3f_777_);
lean_inc(v_method_776_);
lean_dec(v_x_775_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_777_);
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 0);
lean_ctor_set(v___x_779_, 1, v___x_781_);
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_method_776_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_785_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; 
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
}
else
{
lean_object* v___x_787_; 
lean_dec_ref(v_x_775_);
v___x_787_ = lean_box(0);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default___redArg(lean_object* v_inst_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default));
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v_inst_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default(lean_object* v_00_u03b1_791_, lean_object* v_inst_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___redArg(lean_object* v_inst_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object* v_a_796_, lean_object* v_inst_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_797_);
return v___x_798_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq___redArg(lean_object* v_inst_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v_id_802_; lean_object* v_result_803_; lean_object* v_id_804_; lean_object* v_result_805_; uint8_t v___x_806_; 
v_id_802_ = lean_ctor_get(v_x_800_, 0);
lean_inc(v_id_802_);
v_result_803_ = lean_ctor_get(v_x_800_, 1);
lean_inc(v_result_803_);
lean_dec_ref(v_x_800_);
v_id_804_ = lean_ctor_get(v_x_801_, 0);
lean_inc(v_id_804_);
v_result_805_ = lean_ctor_get(v_x_801_, 1);
lean_inc(v_result_805_);
lean_dec_ref(v_x_801_);
v___x_806_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_802_, v_id_804_);
lean_dec(v_id_804_);
lean_dec(v_id_802_);
if (v___x_806_ == 0)
{
lean_dec(v_result_805_);
lean_dec(v_result_803_);
lean_dec_ref(v_inst_799_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_apply_2(v_inst_799_, v_result_803_, v_result_805_);
v___x_808_ = lean_unbox(v___x_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___redArg___boxed(lean_object* v_inst_809_, lean_object* v_x_810_, lean_object* v_x_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_809_, v_x_810_, v_x_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq(lean_object* v_00_u03b1_814_, lean_object* v_inst_815_, lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_815_, v_x_816_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___boxed(lean_object* v_00_u03b1_819_, lean_object* v_inst_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Lean_JsonRpc_instBEqResponse_beq(v_00_u03b1_819_, v_inst_820_, v_x_821_, v_x_822_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object* v_inst_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_826_, 0, lean_box(0));
lean_closure_set(v___x_826_, 1, v_inst_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object* v_00_u03b1_827_, lean_object* v_inst_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_829_, 0, lean_box(0));
lean_closure_set(v___x_829_, 1, v_inst_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(lean_object* v_inst_830_, lean_object* v_r_831_){
_start:
{
lean_object* v_id_832_; lean_object* v_result_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_841_; 
v_id_832_ = lean_ctor_get(v_r_831_, 0);
v_result_833_ = lean_ctor_get(v_r_831_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_r_831_);
if (v_isSharedCheck_841_ == 0)
{
v___x_835_ = v_r_831_;
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_result_833_);
lean_inc(v_id_832_);
lean_dec(v_r_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_apply_1(v_inst_830_, v_result_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 2);
lean_ctor_set(v___x_835_, 1, v___x_837_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_id_832_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object* v_inst_842_){
_start:
{
lean_object* v___f_843_; 
v___f_843_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_843_, 0, v_inst_842_);
return v___f_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object* v_00_u03b1_844_, lean_object* v_inst_845_){
_start:
{
lean_object* v___f_846_; 
v___f_846_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_846_, 0, v_inst_845_);
return v___f_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ofMessage_x3f(lean_object* v_x_847_){
_start:
{
if (lean_obj_tag(v_x_847_) == 2)
{
lean_object* v_id_848_; lean_object* v_result_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_857_; 
v_id_848_ = lean_ctor_get(v_x_847_, 0);
v_result_849_ = lean_ctor_get(v_x_847_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_x_847_);
if (v_isSharedCheck_857_ == 0)
{
v___x_851_ = v_x_847_;
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_result_849_);
lean_inc(v_id_848_);
lean_dec(v_x_847_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 0);
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_id_848_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_result_849_);
v___x_854_ = v_reuseFailAlloc_856_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_855_; 
v___x_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
}
}
else
{
lean_object* v___x_858_; 
lean_dec_ref(v_x_847_);
v___x_858_ = lean_box(0);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___redArg(){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___closed__0));
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___boxed(lean_object* v___dummy_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_JsonRpc_instInhabitedResponseError_default___redArg();
return v_res_867_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0(void){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_JsonRpc_instInhabitedResponseError_default___redArg();
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object* v_00_u03b1_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError___redArg(){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError___redArg___boxed(lean_object* v___dummy_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_JsonRpc_instInhabitedResponseError___redArg();
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object* v_a_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_876_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq___redArg(lean_object* v_inst_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
lean_object* v_id_880_; uint8_t v_code_881_; lean_object* v_message_882_; lean_object* v_data_x3f_883_; lean_object* v_id_884_; uint8_t v_code_885_; lean_object* v_message_886_; lean_object* v_data_x3f_887_; uint8_t v___x_888_; 
v_id_880_ = lean_ctor_get(v_x_878_, 0);
lean_inc(v_id_880_);
v_code_881_ = lean_ctor_get_uint8(v_x_878_, sizeof(void*)*3);
v_message_882_ = lean_ctor_get(v_x_878_, 1);
lean_inc_ref(v_message_882_);
v_data_x3f_883_ = lean_ctor_get(v_x_878_, 2);
lean_inc(v_data_x3f_883_);
lean_dec_ref(v_x_878_);
v_id_884_ = lean_ctor_get(v_x_879_, 0);
lean_inc(v_id_884_);
v_code_885_ = lean_ctor_get_uint8(v_x_879_, sizeof(void*)*3);
v_message_886_ = lean_ctor_get(v_x_879_, 1);
lean_inc_ref(v_message_886_);
v_data_x3f_887_ = lean_ctor_get(v_x_879_, 2);
lean_inc(v_data_x3f_887_);
lean_dec_ref(v_x_879_);
v___x_888_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_880_, v_id_884_);
lean_dec(v_id_884_);
lean_dec(v_id_880_);
if (v___x_888_ == 0)
{
lean_dec(v_data_x3f_887_);
lean_dec_ref(v_message_886_);
lean_dec(v_data_x3f_883_);
lean_dec_ref(v_message_882_);
lean_dec_ref(v_inst_877_);
return v___x_888_;
}
else
{
uint8_t v___x_889_; 
v___x_889_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_code_881_, v_code_885_);
if (v___x_889_ == 0)
{
lean_dec(v_data_x3f_887_);
lean_dec_ref(v_message_886_);
lean_dec(v_data_x3f_883_);
lean_dec_ref(v_message_882_);
lean_dec_ref(v_inst_877_);
return v___x_889_;
}
else
{
uint8_t v___x_890_; 
v___x_890_ = lean_string_dec_eq(v_message_882_, v_message_886_);
lean_dec_ref(v_message_886_);
lean_dec_ref(v_message_882_);
if (v___x_890_ == 0)
{
lean_dec(v_data_x3f_887_);
lean_dec(v_data_x3f_883_);
lean_dec_ref(v_inst_877_);
return v___x_890_;
}
else
{
uint8_t v___x_891_; 
v___x_891_ = l_instBEqOption_beq___redArg(v_inst_877_, v_data_x3f_883_, v_data_x3f_887_);
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(lean_object* v_inst_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
uint8_t v_res_895_; lean_object* v_r_896_; 
v_res_895_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_892_, v_x_893_, v_x_894_);
v_r_896_ = lean_box(v_res_895_);
return v_r_896_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object* v_00_u03b1_897_, lean_object* v_inst_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_898_, v_x_899_, v_x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___boxed(lean_object* v_00_u03b1_902_, lean_object* v_inst_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
uint8_t v_res_906_; lean_object* v_r_907_; 
v_res_906_ = l_Lean_JsonRpc_instBEqResponseError_beq(v_00_u03b1_902_, v_inst_903_, v_x_904_, v_x_905_);
v_r_907_ = lean_box(v_res_906_);
return v_r_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object* v_inst_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_909_, 0, lean_box(0));
lean_closure_set(v___x_909_, 1, v_inst_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object* v_00_u03b1_910_, lean_object* v_inst_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_912_, 0, lean_box(0));
lean_closure_set(v___x_912_, 1, v_inst_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object* v_inst_913_, lean_object* v_r_914_){
_start:
{
lean_object* v_data_x3f_915_; 
v_data_x3f_915_ = lean_ctor_get(v_r_914_, 2);
lean_inc(v_data_x3f_915_);
if (lean_obj_tag(v_data_x3f_915_) == 0)
{
lean_object* v_id_916_; uint8_t v_code_917_; lean_object* v_message_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v_inst_913_);
v_id_916_ = lean_ctor_get(v_r_914_, 0);
v_code_917_ = lean_ctor_get_uint8(v_r_914_, sizeof(void*)*3);
v_message_918_ = lean_ctor_get(v_r_914_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_r_914_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_r_914_, 2);
lean_dec(v_unused_927_);
v___x_920_ = v_r_914_;
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_message_918_);
lean_inc(v_id_916_);
lean_dec(v_r_914_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = lean_box(0);
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 3);
lean_ctor_set(v___x_920_, 2, v___x_922_);
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_id_916_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_message_918_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v___x_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_925_, sizeof(void*)*3, v_code_917_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
else
{
lean_object* v_id_928_; uint8_t v_code_929_; lean_object* v_message_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_946_; 
v_id_928_ = lean_ctor_get(v_r_914_, 0);
v_code_929_ = lean_ctor_get_uint8(v_r_914_, sizeof(void*)*3);
v_message_930_ = lean_ctor_get(v_r_914_, 1);
v_isSharedCheck_946_ = !lean_is_exclusive(v_r_914_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v_r_914_, 2);
lean_dec(v_unused_947_);
v___x_932_ = v_r_914_;
v_isShared_933_ = v_isSharedCheck_946_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_message_930_);
lean_inc(v_id_928_);
lean_dec(v_r_914_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_946_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_val_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_945_; 
v_val_934_ = lean_ctor_get(v_data_x3f_915_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_data_x3f_915_);
if (v_isSharedCheck_945_ == 0)
{
v___x_936_ = v_data_x3f_915_;
v_isShared_937_ = v_isSharedCheck_945_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_val_934_);
lean_dec(v_data_x3f_915_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_945_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = lean_apply_1(v_inst_913_, v_val_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_944_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 3);
lean_ctor_set(v___x_932_, 2, v___x_940_);
v___x_942_ = v___x_932_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_id_928_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_message_930_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v___x_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_943_, sizeof(void*)*3, v_code_929_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object* v_inst_948_){
_start:
{
lean_object* v___f_949_; 
v___f_949_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_949_, 0, v_inst_948_);
return v___f_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object* v_00_u03b1_950_, lean_object* v_inst_951_){
_start:
{
lean_object* v___f_952_; 
v___f_952_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_952_, 0, v_inst_951_);
return v___f_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object* v_r_953_){
_start:
{
lean_object* v_id_954_; uint8_t v_code_955_; lean_object* v_message_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_964_; 
v_id_954_ = lean_ctor_get(v_r_953_, 0);
v_code_955_ = lean_ctor_get_uint8(v_r_953_, sizeof(void*)*3);
v_message_956_ = lean_ctor_get(v_r_953_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_r_953_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v_r_953_, 2);
lean_dec(v_unused_965_);
v___x_958_ = v_r_953_;
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_message_956_);
lean_inc(v_id_954_);
lean_dec(v_r_953_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = lean_box(0);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 3);
lean_ctor_set(v___x_958_, 2, v___x_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_id_954_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_message_956_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v___x_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_963_, sizeof(void*)*3, v_code_955_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ofMessage_x3f(lean_object* v_x_968_){
_start:
{
if (lean_obj_tag(v_x_968_) == 3)
{
lean_object* v_id_969_; uint8_t v_code_970_; lean_object* v_message_971_; lean_object* v_data_x3f_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_980_; 
v_id_969_ = lean_ctor_get(v_x_968_, 0);
v_code_970_ = lean_ctor_get_uint8(v_x_968_, sizeof(void*)*3);
v_message_971_ = lean_ctor_get(v_x_968_, 1);
v_data_x3f_972_ = lean_ctor_get(v_x_968_, 2);
v_isSharedCheck_980_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_980_ == 0)
{
v___x_974_ = v_x_968_;
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_data_x3f_972_);
lean_inc(v_message_971_);
lean_inc(v_id_969_);
lean_dec(v_x_968_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set_tag(v___x_974_, 0);
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_id_969_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_message_971_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_data_x3f_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, sizeof(void*)*3, v_code_970_);
v___x_977_ = v_reuseFailAlloc_979_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; 
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
}
}
else
{
lean_object* v___x_981_; 
lean_dec_ref(v_x_968_);
v___x_981_ = lean_box(0);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object* v_s_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v_s_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object* v_n_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v_n_986_);
return v___x_987_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_RequestID_lt(lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
switch(lean_obj_tag(v_x_990_))
{
case 0:
{
if (lean_obj_tag(v_x_991_) == 0)
{
lean_object* v_s_992_; lean_object* v_s_993_; uint8_t v___x_994_; 
v_s_992_ = lean_ctor_get(v_x_990_, 0);
lean_inc_ref(v_s_992_);
lean_dec_ref_known(v_x_990_, 1);
v_s_993_ = lean_ctor_get(v_x_991_, 0);
lean_inc_ref(v_s_993_);
lean_dec_ref_known(v_x_991_, 1);
v___x_994_ = lean_string_dec_lt(v_s_992_, v_s_993_);
lean_dec_ref(v_s_993_);
lean_dec_ref(v_s_992_);
return v___x_994_;
}
else
{
uint8_t v___x_995_; 
lean_dec_ref_known(v_x_990_, 1);
lean_dec(v_x_991_);
v___x_995_ = 0;
return v___x_995_;
}
}
case 1:
{
switch(lean_obj_tag(v_x_991_))
{
case 1:
{
lean_object* v_n_996_; lean_object* v_n_997_; uint8_t v___x_998_; 
v_n_996_ = lean_ctor_get(v_x_990_, 0);
lean_inc_ref(v_n_996_);
lean_dec_ref_known(v_x_990_, 1);
v_n_997_ = lean_ctor_get(v_x_991_, 0);
lean_inc_ref(v_n_997_);
lean_dec_ref_known(v_x_991_, 1);
v___x_998_ = l_Lean_JsonNumber_lt(v_n_996_, v_n_997_);
return v___x_998_;
}
case 0:
{
uint8_t v___x_999_; 
lean_dec_ref_known(v_x_991_, 1);
lean_dec_ref_known(v_x_990_, 1);
v___x_999_ = 1;
return v___x_999_;
}
default: 
{
uint8_t v___x_1000_; 
lean_dec_ref_known(v_x_990_, 1);
lean_dec(v_x_991_);
v___x_1000_ = 0;
return v___x_1000_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_991_))
{
case 1:
{
uint8_t v___x_1001_; 
lean_dec_ref_known(v_x_991_, 1);
v___x_1001_ = 1;
return v___x_1001_;
}
case 0:
{
uint8_t v___x_1002_; 
lean_dec_ref_known(v_x_991_, 1);
v___x_1002_ = 1;
return v___x_1002_;
}
default: 
{
uint8_t v___x_1003_; 
lean_dec(v_x_991_);
v___x_1003_ = 0;
return v___x_1003_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_lt___boxed(lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
uint8_t v_res_1006_; lean_object* v_r_1007_; 
v_res_1006_ = l_Lean_JsonRpc_RequestID_lt(v_x_1004_, v_x_1005_);
v_r_1007_ = lean_box(v_res_1006_);
return v_r_1007_;
}
}
static lean_object* _init_l_Lean_JsonRpc_RequestID_ltProp(void){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_box(0);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instLTRequestID(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_box(0);
return v___x_1009_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object* v_a_1010_, lean_object* v_b_1011_){
_start:
{
uint8_t v___x_1012_; 
v___x_1012_ = l_Lean_JsonRpc_RequestID_lt(v_a_1010_, v_b_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object* v_a_1013_, lean_object* v_b_1014_){
_start:
{
uint8_t v_res_1015_; lean_object* v_r_1016_; 
v_res_1015_ = l_Lean_JsonRpc_instDecidableLtRequestID(v_a_1013_, v_b_1014_);
v_r_1016_ = lean_box(v_res_1015_);
return v_r_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object* v_j_1020_){
_start:
{
switch(lean_obj_tag(v_j_1020_))
{
case 3:
{
lean_object* v_s_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1029_; 
v_s_1021_ = lean_ctor_get(v_j_1020_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_j_1020_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1023_ = v_j_1020_;
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_s_1021_);
lean_dec(v_j_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 0);
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_s_1021_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
}
}
case 2:
{
lean_object* v_n_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1038_; 
v_n_1030_ = lean_ctor_get(v_j_1020_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_j_1020_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1032_ = v_j_1020_;
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_n_1030_);
lean_dec(v_j_1020_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 1);
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_n_1030_);
v___x_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
}
default: 
{
lean_object* v___x_1039_; 
lean_dec(v_j_1020_);
v___x_1039_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object* v_rid_1042_){
_start:
{
switch(lean_obj_tag(v_rid_1042_))
{
case 0:
{
lean_object* v_s_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_s_1043_ = lean_ctor_get(v_rid_1042_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_rid_1042_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v_rid_1042_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_s_1043_);
lean_dec(v_rid_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 3);
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_s_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
case 1:
{
lean_object* v_n_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
v_n_1051_ = lean_ctor_get(v_rid_1042_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_rid_1042_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v_rid_1042_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_n_1051_);
lean_dec(v_rid_1042_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 2);
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_n_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
default: 
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_box(0);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object* v___x_1077_, lean_object* v___x_1078_, lean_object* v_m_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v___y_1082_; 
v___x_1080_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_1079_))
{
case 0:
{
lean_object* v_id_1085_; lean_object* v_method_1086_; lean_object* v_params_x3f_1087_; lean_object* v___x_1088_; lean_object* v___y_1090_; 
lean_dec_ref(v___x_1078_);
v_id_1085_ = lean_ctor_get(v_m_1079_, 0);
lean_inc(v_id_1085_);
v_method_1086_ = lean_ctor_get(v_m_1079_, 1);
lean_inc_ref(v_method_1086_);
v_params_x3f_1087_ = lean_ctor_get(v_m_1079_, 2);
lean_inc(v_params_x3f_1087_);
lean_dec_ref_known(v_m_1079_, 3);
v___x_1088_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1085_))
{
case 0:
{
lean_object* v_s_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_s_1101_ = lean_ctor_get(v_id_1085_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_id_1085_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v_id_1085_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_s_1101_);
lean_dec(v_id_1085_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 3);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_s_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
v___y_1090_ = v___x_1106_;
goto v___jp_1089_;
}
}
}
case 1:
{
lean_object* v_n_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_n_1109_ = lean_ctor_get(v_id_1085_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_id_1085_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v_id_1085_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_n_1109_);
lean_dec(v_id_1085_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set_tag(v___x_1111_, 2);
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_n_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
v___y_1090_ = v___x_1114_;
goto v___jp_1089_;
}
}
}
default: 
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_box(0);
v___y_1090_ = v___x_1117_;
goto v___jp_1089_;
}
}
v___jp_1089_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1088_);
lean_ctor_set(v___x_1091_, 1, v___y_1090_);
v___x_1092_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1093_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_method_1086_);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1091_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1099_ = l_Lean_Json_opt___redArg(v___x_1077_, v___x_1098_, v_params_x3f_1087_);
v___x_1100_ = l_List_appendTR___redArg(v___x_1097_, v___x_1099_);
v___y_1082_ = v___x_1100_;
goto v___jp_1081_;
}
}
case 1:
{
lean_object* v_method_1118_; lean_object* v_params_x3f_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v___x_1078_);
v_method_1118_ = lean_ctor_get(v_m_1079_, 0);
v_params_x3f_1119_ = lean_ctor_get(v_m_1079_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_m_1079_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1121_ = v_m_1079_;
v_isShared_1122_ = v_isSharedCheck_1131_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_params_x3f_1119_);
lean_inc(v_method_1118_);
lean_dec(v_m_1079_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1131_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1123_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1124_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_method_1118_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 0);
lean_ctor_set(v___x_1121_, 1, v___x_1124_);
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1126_ = v___x_1121_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1128_ = l_Lean_Json_opt___redArg(v___x_1077_, v___x_1127_, v_params_x3f_1119_);
v___x_1129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1126_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___y_1082_ = v___x_1129_;
goto v___jp_1081_;
}
}
}
case 2:
{
lean_object* v_id_1132_; lean_object* v_result_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v___x_1078_);
lean_dec_ref(v___x_1077_);
v_id_1132_ = lean_ctor_get(v_m_1079_, 0);
v_result_1133_ = lean_ctor_get(v_m_1079_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_m_1079_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1135_ = v_m_1079_;
v_isShared_1136_ = v_isSharedCheck_1165_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_result_1133_);
lean_inc(v_id_1132_);
lean_dec(v_m_1079_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1165_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___y_1139_; 
v___x_1137_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1132_))
{
case 0:
{
lean_object* v_s_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
v_s_1148_ = lean_ctor_get(v_id_1132_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_id_1132_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v_id_1132_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_s_1148_);
lean_dec(v_id_1132_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 3);
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_s_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
v___y_1139_ = v___x_1153_;
goto v___jp_1138_;
}
}
}
case 1:
{
lean_object* v_n_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v_n_1156_ = lean_ctor_get(v_id_1132_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_id_1132_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v_id_1132_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_n_1156_);
lean_dec(v_id_1132_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set_tag(v___x_1158_, 2);
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_n_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
v___y_1139_ = v___x_1161_;
goto v___jp_1138_;
}
}
}
default: 
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_box(0);
v___y_1139_ = v___x_1164_;
goto v___jp_1138_;
}
}
v___jp_1138_:
{
lean_object* v___x_1141_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 0);
lean_ctor_set(v___x_1135_, 1, v___y_1139_);
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1141_ = v___x_1135_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___y_1139_);
v___x_1141_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1142_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v_result_1133_);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1141_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___y_1082_ = v___x_1146_;
goto v___jp_1081_;
}
}
}
}
default: 
{
lean_object* v_id_1166_; uint8_t v_code_1167_; lean_object* v_message_1168_; lean_object* v_data_x3f_1169_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___x_1189_; lean_object* v___y_1191_; 
lean_dec_ref(v___x_1077_);
v_id_1166_ = lean_ctor_get(v_m_1079_, 0);
lean_inc(v_id_1166_);
v_code_1167_ = lean_ctor_get_uint8(v_m_1079_, sizeof(void*)*3);
v_message_1168_ = lean_ctor_get(v_m_1079_, 1);
lean_inc_ref(v_message_1168_);
v_data_x3f_1169_ = lean_ctor_get(v_m_1079_, 2);
lean_inc(v_data_x3f_1169_);
lean_dec_ref_known(v_m_1079_, 3);
v___x_1189_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1166_))
{
case 0:
{
lean_object* v_s_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_s_1207_ = lean_ctor_get(v_id_1166_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_id_1166_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v_id_1166_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_s_1207_);
lean_dec(v_id_1166_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 3);
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_s_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
v___y_1191_ = v___x_1212_;
goto v___jp_1190_;
}
}
}
case 1:
{
lean_object* v_n_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_n_1215_ = lean_ctor_get(v_id_1166_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_id_1166_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v_id_1166_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_n_1215_);
lean_dec(v_id_1166_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set_tag(v___x_1217_, 2);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_n_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
v___y_1191_ = v___x_1220_;
goto v___jp_1190_;
}
}
}
default: 
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_box(0);
v___y_1191_ = v___x_1223_;
goto v___jp_1190_;
}
}
v___jp_1170_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_inc(v___y_1174_);
lean_inc_ref(v___y_1172_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___y_1172_);
lean_ctor_set(v___x_1175_, 1, v___y_1174_);
v___x_1176_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_message_1168_);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1175_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1183_ = l_Lean_Json_opt___redArg(v___x_1078_, v___x_1182_, v_data_x3f_1169_);
v___x_1184_ = l_List_appendTR___redArg(v___x_1181_, v___x_1183_);
v___x_1185_ = l_Lean_Json_mkObj(v___x_1184_);
lean_dec(v___x_1184_);
lean_inc_ref(v___y_1173_);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___y_1173_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1179_);
v___x_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___y_1171_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___y_1082_ = v___x_1188_;
goto v___jp_1081_;
}
v___jp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1189_);
lean_ctor_set(v___x_1192_, 1, v___y_1191_);
v___x_1193_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1194_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_1167_)
{
case 0:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1195_;
goto v___jp_1170_;
}
case 1:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1196_;
goto v___jp_1170_;
}
case 2:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1197_;
goto v___jp_1170_;
}
case 3:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1198_;
goto v___jp_1170_;
}
case 4:
{
lean_object* v___x_1199_; 
v___x_1199_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1199_;
goto v___jp_1170_;
}
case 5:
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1200_;
goto v___jp_1170_;
}
case 6:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1201_;
goto v___jp_1170_;
}
case 7:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1202_;
goto v___jp_1170_;
}
case 8:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1203_;
goto v___jp_1170_;
}
case 9:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1204_;
goto v___jp_1170_;
}
case 10:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1205_;
goto v___jp_1170_;
}
default: 
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_1171_ = v___x_1192_;
v___y_1172_ = v___x_1194_;
v___y_1173_ = v___x_1193_;
v___y_1174_ = v___x_1206_;
goto v___jp_1170_;
}
}
}
}
}
v___jp_1081_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1080_);
lean_ctor_set(v___x_1083_, 1, v___y_1082_);
v___x_1084_ = l_Lean_Json_mkObj(v___x_1083_);
lean_dec_ref_known(v___x_1083_, 2);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object* v___f_1233_, lean_object* v___f_1234_, lean_object* v___x_1235_, lean_object* v___x_1236_, lean_object* v_j_1237_){
_start:
{
lean_object* v___y_1241_; uint8_t v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1237_);
v___x_1253_ = l_Lean_Json_getObjVal_x3f(v_j_1237_, v___x_1252_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_j_1237_);
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___f_1234_);
lean_dec_ref(v___f_1233_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
else
{
lean_object* v_a_1262_; 
v_a_1262_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1253_, 1);
if (lean_obj_tag(v_a_1262_) == 3)
{
lean_object* v_s_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_s_1263_ = lean_ctor_get(v_a_1262_, 0);
lean_inc_ref(v_s_1263_);
lean_dec_ref_known(v_a_1262_, 1);
v___x_1264_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1265_ = lean_string_dec_eq(v_s_1263_, v___x_1264_);
lean_dec_ref(v_s_1263_);
if (v___x_1265_ == 0)
{
lean_dec(v_j_1237_);
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___f_1234_);
lean_dec_ref(v___f_1233_);
goto v___jp_1238_;
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1237_);
v___x_1267_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1237_, v___f_1233_, v___x_1266_);
if (lean_obj_tag(v___x_1267_) == 0)
{
goto v___jp_1324_;
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_a_1351_ = lean_ctor_get(v___x_1267_, 0);
v___x_1352_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1235_);
lean_inc(v_j_1237_);
v___x_1353_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1237_, v___x_1235_, v___x_1352_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_dec_ref_known(v___x_1353_, 1);
goto v___jp_1324_;
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1375_; 
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1267_, 1);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___f_1234_);
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1375_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1375_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___y_1359_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1365_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1237_, v___x_1236_, v___x_1364_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1366_; 
lean_dec_ref_known(v___x_1365_, 1);
v___x_1366_ = lean_box(0);
v___y_1359_ = v___x_1366_;
goto v___jp_1358_;
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
v_a_1367_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1365_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1365_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
v___y_1359_ = v___x_1372_;
goto v___jp_1358_;
}
}
}
v___jp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1360_, 0, v_a_1351_);
lean_ctor_set(v___x_1360_, 1, v_a_1354_);
lean_ctor_set(v___x_1360_, 2, v___y_1359_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1360_);
v___x_1362_ = v___x_1356_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
v___jp_1268_:
{
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v_j_1237_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___f_1234_);
v_a_1269_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1267_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1267_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_a_1277_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1278_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1279_ = l_Lean_Json_getObjVal_x3f(v_j_1237_, v___x_1278_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_a_1277_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___f_1234_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_a_1288_ = lean_ctor_get(v___x_1279_, 0);
lean_inc_n(v_a_1288_, 2);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1289_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1290_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1288_, v___f_1234_, v___x_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_a_1288_);
lean_dec(v_a_1277_);
lean_dec_ref(v___x_1235_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_a_1299_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1290_, 1);
v___x_1300_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1288_);
v___x_1301_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1288_, v___x_1235_, v___x_1300_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_a_1299_);
lean_dec(v_a_1288_);
lean_dec(v_a_1277_);
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_a_1310_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1301_, 1);
v___x_1311_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1312_ = l_Lean_Json_getObjVal_x3f(v_a_1288_, v___x_1311_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
lean_dec_ref_known(v___x_1312_, 1);
v___x_1313_ = lean_box(0);
v___x_1314_ = lean_unbox(v_a_1299_);
lean_dec(v_a_1299_);
v___y_1241_ = v_a_1310_;
v___y_1242_ = v___x_1314_;
v___y_1243_ = v_a_1277_;
v___y_1244_ = v___x_1313_;
goto v___jp_1240_;
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1323_; 
v_a_1315_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1317_ = v___x_1312_;
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1312_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_unbox(v_a_1299_);
lean_dec(v_a_1299_);
v___y_1241_ = v_a_1310_;
v___y_1242_ = v___x_1321_;
v___y_1243_ = v_a_1277_;
v___y_1244_ = v___x_1320_;
goto v___jp_1240_;
}
}
}
}
}
}
}
}
v___jp_1324_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1235_);
lean_inc(v_j_1237_);
v___x_1326_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1237_, v___x_1235_, v___x_1325_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_dec_ref_known(v___x_1326_, 1);
lean_dec_ref(v___x_1236_);
if (lean_obj_tag(v___x_1267_) == 0)
{
goto v___jp_1268_;
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v_a_1327_ = lean_ctor_get(v___x_1267_, 0);
v___x_1328_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1237_);
v___x_1329_ = l_Lean_Json_getObjVal_x3f(v_j_1237_, v___x_1328_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_dec_ref_known(v___x_1329_, 1);
goto v___jp_1268_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1338_; 
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1267_, 1);
lean_dec(v_j_1237_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___f_1234_);
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_a_1327_);
lean_ctor_set(v___x_1334_, 1, v_a_1330_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1334_);
v___x_1336_ = v___x_1332_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___f_1234_);
v_a_1339_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1340_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1341_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1237_, v___x_1236_, v___x_1340_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v___x_1342_; 
lean_dec_ref_known(v___x_1341_, 1);
v___x_1342_ = lean_box(0);
v___y_1248_ = v_a_1339_;
v___y_1249_ = v___x_1342_;
goto v___jp_1247_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1341_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1341_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
v___y_1248_ = v_a_1339_;
v___y_1249_ = v___x_1348_;
goto v___jp_1247_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1262_);
lean_dec(v_j_1237_);
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___f_1234_);
lean_dec_ref(v___f_1233_);
goto v___jp_1238_;
}
}
v___jp_1238_:
{
lean_object* v___x_1239_; 
v___x_1239_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1));
return v___x_1239_;
}
v___jp_1240_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1245_, 0, v___y_1243_);
lean_ctor_set(v___x_1245_, 1, v___y_1241_);
lean_ctor_set(v___x_1245_, 2, v___y_1244_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*3, v___y_1242_);
v___x_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
v___jp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___y_1248_);
lean_ctor_set(v___x_1250_, 1, v___y_1249_);
v___x_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object* v___x_1389_, lean_object* v_inst_1390_, lean_object* v_j_1391_){
_start:
{
lean_object* v_method_1395_; lean_object* v_params_x3f_1396_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1391_);
v___x_1419_ = l_Lean_Json_getObjVal_x3f(v_j_1391_, v___x_1418_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec(v_j_1391_);
lean_dec_ref(v_inst_1390_);
lean_dec_ref(v___x_1389_);
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
else
{
lean_object* v_a_1428_; 
v_a_1428_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1419_, 1);
if (lean_obj_tag(v_a_1428_) == 3)
{
lean_object* v_s_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_s_1429_ = lean_ctor_get(v_a_1428_, 0);
lean_inc_ref(v_s_1429_);
lean_dec_ref_known(v_a_1428_, 1);
v___x_1430_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1431_ = lean_string_dec_eq(v_s_1429_, v___x_1430_);
lean_dec_ref(v_s_1429_);
if (v___x_1431_ == 0)
{
lean_dec(v_j_1391_);
lean_dec_ref(v_inst_1390_);
lean_dec_ref(v___x_1389_);
goto v___jp_1416_;
}
else
{
lean_object* v___f_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___f_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___f_1432_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___closed__0));
v___x_1433_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__0));
v___x_1434_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__1));
v___f_1435_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___closed__0));
v___x_1436_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1391_);
v___x_1437_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1391_, v___f_1432_, v___x_1436_);
if (lean_obj_tag(v___x_1437_) == 0)
{
goto v___jp_1478_;
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1391_);
v___x_1496_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1391_, v___x_1433_, v___x_1495_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_dec_ref_known(v___x_1496_, 1);
goto v___jp_1478_;
}
else
{
lean_dec_ref_known(v___x_1496_, 1);
lean_dec_ref_known(v___x_1437_, 1);
lean_dec(v_j_1391_);
lean_dec_ref(v_inst_1390_);
lean_dec_ref(v___x_1389_);
goto v___jp_1392_;
}
}
v___jp_1438_:
{
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_j_1391_);
v_a_1439_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1437_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1437_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref_known(v___x_1437_, 1);
v___x_1447_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1448_ = l_Lean_Json_getObjVal_x3f(v_j_1391_, v___x_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_a_1457_ = lean_ctor_get(v___x_1448_, 0);
lean_inc_n(v_a_1457_, 2);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1458_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1459_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1457_, v___f_1435_, v___x_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_a_1457_);
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec_ref_known(v___x_1459_, 1);
v___x_1468_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1469_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1457_, v___x_1433_, v___x_1468_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
else
{
lean_dec_ref_known(v___x_1469_, 1);
goto v___jp_1392_;
}
}
}
}
}
v___jp_1478_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1391_);
v___x_1480_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1391_, v___x_1433_, v___x_1479_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_dec_ref_known(v___x_1480_, 1);
lean_dec_ref(v_inst_1390_);
lean_dec_ref(v___x_1389_);
if (lean_obj_tag(v___x_1437_) == 0)
{
goto v___jp_1438_;
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1391_);
v___x_1482_ = l_Lean_Json_getObjVal_x3f(v_j_1391_, v___x_1481_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_dec_ref_known(v___x_1482_, 1);
goto v___jp_1438_;
}
else
{
lean_dec_ref_known(v___x_1482_, 1);
lean_dec_ref_known(v___x_1437_, 1);
lean_dec(v_j_1391_);
goto v___jp_1392_;
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref(v___x_1437_);
v_a_1483_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1484_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1485_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1391_, v___x_1434_, v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v___x_1486_; 
lean_dec_ref_known(v___x_1485_, 1);
v___x_1486_ = lean_box(0);
v_method_1395_ = v_a_1483_;
v_params_x3f_1396_ = v___x_1486_;
goto v___jp_1394_;
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1485_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1485_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
v_method_1395_ = v_a_1483_;
v_params_x3f_1396_ = v___x_1492_;
goto v___jp_1394_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1428_);
lean_dec(v_j_1391_);
lean_dec_ref(v_inst_1390_);
lean_dec_ref(v___x_1389_);
goto v___jp_1416_;
}
}
v___jp_1392_:
{
lean_object* v___x_1393_; 
v___x_1393_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1));
return v___x_1393_;
}
v___jp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = l_Lean_Option_toJson___redArg(v___x_1389_, v_params_x3f_1396_);
v___x_1398_ = lean_apply_1(v_inst_1390_, v___x_1397_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec_ref(v_method_1395_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
v_a_1407_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v___x_1398_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1398_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_method_1395_);
lean_ctor_set(v___x_1411_, 1, v_a_1407_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
v___jp_1416_:
{
lean_object* v___x_1417_; 
v___x_1417_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2));
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object* v_inst_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___f_1499_; 
v___x_1498_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___f_1499_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1499_, 0, v___x_1498_);
lean_closure_set(v___f_1499_, 1, v_inst_1497_);
return v___f_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object* v_00_u03b1_1500_, lean_object* v_inst_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_JsonRpc_instFromJsonNotification___redArg(v_inst_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___impl(lean_object* v_x_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_obj_tag_nat(v_x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___impl___boxed(lean_object* v_x_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_JsonRpc_MessageMetaData_ctorIdx___impl(v_x_1505_);
lean_dec_ref(v_x_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(lean_object* v_t_1507_, lean_object* v_k_1508_){
_start:
{
switch(lean_obj_tag(v_t_1507_))
{
case 0:
{
lean_object* v_id_1509_; lean_object* v_method_1510_; lean_object* v___x_1511_; 
v_id_1509_ = lean_ctor_get(v_t_1507_, 0);
lean_inc(v_id_1509_);
v_method_1510_ = lean_ctor_get(v_t_1507_, 1);
lean_inc_ref(v_method_1510_);
lean_dec_ref_known(v_t_1507_, 2);
v___x_1511_ = lean_apply_2(v_k_1508_, v_id_1509_, v_method_1510_);
return v___x_1511_;
}
case 1:
{
lean_object* v_method_1512_; lean_object* v___x_1513_; 
v_method_1512_ = lean_ctor_get(v_t_1507_, 0);
lean_inc_ref(v_method_1512_);
lean_dec_ref_known(v_t_1507_, 1);
v___x_1513_ = lean_apply_1(v_k_1508_, v_method_1512_);
return v___x_1513_;
}
case 2:
{
lean_object* v_id_1514_; lean_object* v___x_1515_; 
v_id_1514_ = lean_ctor_get(v_t_1507_, 0);
lean_inc(v_id_1514_);
lean_dec_ref_known(v_t_1507_, 1);
v___x_1515_ = lean_apply_1(v_k_1508_, v_id_1514_);
return v___x_1515_;
}
default: 
{
lean_object* v_id_1516_; uint8_t v_code_1517_; lean_object* v_message_1518_; lean_object* v_data_x3f_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_id_1516_ = lean_ctor_get(v_t_1507_, 0);
lean_inc(v_id_1516_);
v_code_1517_ = lean_ctor_get_uint8(v_t_1507_, sizeof(void*)*3);
v_message_1518_ = lean_ctor_get(v_t_1507_, 1);
lean_inc_ref(v_message_1518_);
v_data_x3f_1519_ = lean_ctor_get(v_t_1507_, 2);
lean_inc(v_data_x3f_1519_);
lean_dec_ref_known(v_t_1507_, 3);
v___x_1520_ = lean_box(v_code_1517_);
v___x_1521_ = lean_apply_4(v_k_1508_, v_id_1516_, v___x_1520_, v_message_1518_, v_data_x3f_1519_);
return v___x_1521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim(lean_object* v_motive_1522_, lean_object* v_ctorIdx_1523_, lean_object* v_t_1524_, lean_object* v_h_1525_, lean_object* v_k_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1524_, v_k_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(lean_object* v_motive_1528_, lean_object* v_ctorIdx_1529_, lean_object* v_t_1530_, lean_object* v_h_1531_, lean_object* v_k_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_JsonRpc_MessageMetaData_ctorElim(v_motive_1528_, v_ctorIdx_1529_, v_t_1530_, v_h_1531_, v_k_1532_);
lean_dec(v_ctorIdx_1529_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim___redArg(lean_object* v_t_1534_, lean_object* v_request_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1534_, v_request_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim(lean_object* v_motive_1537_, lean_object* v_t_1538_, lean_object* v_h_1539_, lean_object* v_request_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1538_, v_request_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(lean_object* v_t_1542_, lean_object* v_notification_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1542_, v_notification_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim(lean_object* v_motive_1545_, lean_object* v_t_1546_, lean_object* v_h_1547_, lean_object* v_notification_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1546_, v_notification_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(lean_object* v_t_1550_, lean_object* v_response_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1550_, v_response_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim(lean_object* v_motive_1553_, lean_object* v_t_1554_, lean_object* v_h_1555_, lean_object* v_response_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1554_, v_response_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim___redArg(lean_object* v_t_1558_, lean_object* v_responseError_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1558_, v_responseError_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim(lean_object* v_motive_1561_, lean_object* v_t_1562_, lean_object* v_h_1563_, lean_object* v_responseError_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1562_, v_responseError_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_metaData(lean_object* v_x_1571_){
_start:
{
switch(lean_obj_tag(v_x_1571_))
{
case 0:
{
lean_object* v_id_1572_; lean_object* v_method_1573_; lean_object* v___x_1574_; 
v_id_1572_ = lean_ctor_get(v_x_1571_, 0);
lean_inc(v_id_1572_);
v_method_1573_ = lean_ctor_get(v_x_1571_, 1);
lean_inc_ref(v_method_1573_);
lean_dec_ref_known(v_x_1571_, 3);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_id_1572_);
lean_ctor_set(v___x_1574_, 1, v_method_1573_);
return v___x_1574_;
}
case 1:
{
lean_object* v_method_1575_; lean_object* v___x_1576_; 
v_method_1575_ = lean_ctor_get(v_x_1571_, 0);
lean_inc_ref(v_method_1575_);
lean_dec_ref_known(v_x_1571_, 2);
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_method_1575_);
return v___x_1576_;
}
case 2:
{
lean_object* v_id_1577_; lean_object* v___x_1578_; 
v_id_1577_ = lean_ctor_get(v_x_1571_, 0);
lean_inc(v_id_1577_);
lean_dec_ref_known(v_x_1571_, 2);
v___x_1578_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1578_, 0, v_id_1577_);
return v___x_1578_;
}
default: 
{
lean_object* v_id_1579_; uint8_t v_code_1580_; lean_object* v_message_1581_; lean_object* v_data_x3f_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_id_1579_ = lean_ctor_get(v_x_1571_, 0);
v_code_1580_ = lean_ctor_get_uint8(v_x_1571_, sizeof(void*)*3);
v_message_1581_ = lean_ctor_get(v_x_1571_, 1);
v_data_x3f_1582_ = lean_ctor_get(v_x_1571_, 2);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_x_1571_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v_x_1571_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_data_x3f_1582_);
lean_inc(v_message_1581_);
lean_inc(v_id_1579_);
lean_dec(v_x_1571_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_id_1579_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_message_1581_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_data_x3f_1582_);
lean_ctor_set_uint8(v_reuseFailAlloc_1588_, sizeof(void*)*3, v_code_1580_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_toMessage(lean_object* v_x_1590_){
_start:
{
switch(lean_obj_tag(v_x_1590_))
{
case 0:
{
lean_object* v_id_1591_; lean_object* v_method_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_id_1591_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_id_1591_);
v_method_1592_ = lean_ctor_get(v_x_1590_, 1);
lean_inc_ref(v_method_1592_);
lean_dec_ref_known(v_x_1590_, 2);
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1594_, 0, v_id_1591_);
lean_ctor_set(v___x_1594_, 1, v_method_1592_);
lean_ctor_set(v___x_1594_, 2, v___x_1593_);
return v___x_1594_;
}
case 1:
{
lean_object* v_method_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_method_1595_ = lean_ctor_get(v_x_1590_, 0);
lean_inc_ref(v_method_1595_);
lean_dec_ref_known(v_x_1590_, 1);
v___x_1596_ = lean_box(0);
v___x_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1597_, 0, v_method_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
return v___x_1597_;
}
case 2:
{
lean_object* v_id_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_id_1598_ = lean_ctor_get(v_x_1590_, 0);
lean_inc(v_id_1598_);
lean_dec_ref_known(v_x_1590_, 1);
v___x_1599_ = lean_box(0);
v___x_1600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1600_, 0, v_id_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
return v___x_1600_;
}
default: 
{
lean_object* v_id_1601_; uint8_t v_code_1602_; lean_object* v_message_1603_; lean_object* v_data_x3f_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_id_1601_ = lean_ctor_get(v_x_1590_, 0);
v_code_1602_ = lean_ctor_get_uint8(v_x_1590_, sizeof(void*)*3);
v_message_1603_ = lean_ctor_get(v_x_1590_, 1);
v_data_x3f_1604_ = lean_ctor_get(v_x_1590_, 2);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_x_1590_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v_x_1590_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_data_x3f_1604_);
lean_inc(v_message_1603_);
lean_inc(v_id_1601_);
lean_dec(v_x_1590_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_id_1601_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_message_1603_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_data_x3f_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*3, v_code_1602_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(lean_object* v_a_1615_){
_start:
{
lean_object* v_fst_1616_; lean_object* v_snd_1617_; lean_object* v___x_1618_; uint8_t v_decide_1619_; 
v_fst_1616_ = lean_ctor_get(v_a_1615_, 0);
v_snd_1617_ = lean_ctor_get(v_a_1615_, 1);
v___x_1618_ = lean_string_utf8_byte_size(v_fst_1616_);
v_decide_1619_ = lean_nat_dec_eq(v_snd_1617_, v___x_1618_);
if (v_decide_1619_ == 0)
{
uint32_t v___x_1620_; uint32_t v___x_1621_; uint8_t v___x_1622_; 
v___x_1620_ = lean_string_utf8_get_fast(v_fst_1616_, v_snd_1617_);
v___x_1621_ = 34;
v___x_1622_ = lean_uint32_dec_eq(v___x_1620_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1));
v___x_1624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1624_, 0, v_a_1615_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
return v___x_1624_;
}
else
{
lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1634_; 
lean_inc(v_snd_1617_);
lean_inc(v_fst_1616_);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_a_1615_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; lean_object* v_unused_1636_; 
v_unused_1635_ = lean_ctor_get(v_a_1615_, 1);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_a_1615_, 0);
lean_dec(v_unused_1636_);
v___x_1626_ = v_a_1615_;
v_isShared_1627_ = v_isSharedCheck_1634_;
goto v_resetjp_1625_;
}
else
{
lean_dec(v_a_1615_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1634_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = lean_string_utf8_next_fast(v_fst_1616_, v_snd_1617_);
lean_dec(v_snd_1617_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 1, v___x_1628_);
v___x_1630_ = v___x_1626_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_fst_1616_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_1632_ = l_Lean_Json_Parser_strCore(v___x_1631_, v___x_1630_);
return v___x_1632_;
}
}
}
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_box(0);
v___x_1638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_a_1615_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1640_; 
lean_inc_ref(v_a_1639_);
v___x_1640_ = l_Lean_Json_Parser_num(v_a_1639_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_pos_1641_; lean_object* v_res_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v_a_1639_);
v_pos_1641_ = lean_ctor_get(v___x_1640_, 0);
v_res_1642_ = lean_ctor_get(v___x_1640_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1644_ = v___x_1640_;
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_res_1642_);
lean_inc(v_pos_1641_);
lean_dec(v___x_1640_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1650_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_res_1642_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 1, v___x_1646_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_pos_1641_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v_pos_1651_; lean_object* v_err_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1705_; 
v_pos_1651_ = lean_ctor_get(v___x_1640_, 0);
v_err_1652_ = lean_ctor_get(v___x_1640_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1654_ = v___x_1640_;
v_isShared_1655_ = v_isSharedCheck_1705_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_err_1652_);
lean_inc(v_pos_1651_);
lean_dec(v___x_1640_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1705_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_snd_1656_; lean_object* v_snd_1657_; uint8_t v_decide_1658_; 
v_snd_1656_ = lean_ctor_get(v_a_1639_, 1);
lean_inc(v_snd_1656_);
lean_dec_ref(v_a_1639_);
v_snd_1657_ = lean_ctor_get(v_pos_1651_, 1);
v_decide_1658_ = lean_nat_dec_eq(v_snd_1656_, v_snd_1657_);
lean_dec(v_snd_1656_);
if (v_decide_1658_ == 0)
{
lean_object* v___x_1660_; 
if (v_isShared_1655_ == 0)
{
v___x_1660_ = v___x_1654_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_pos_1651_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_err_1652_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
else
{
lean_object* v___x_1662_; 
lean_inc(v_snd_1657_);
lean_del_object(v___x_1654_);
lean_dec(v_err_1652_);
v___x_1662_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v_pos_1651_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_pos_1663_; lean_object* v_res_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_snd_1657_);
v_pos_1663_ = lean_ctor_get(v___x_1662_, 0);
v_res_1664_ = lean_ctor_get(v___x_1662_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1666_ = v___x_1662_;
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_res_1664_);
lean_inc(v_pos_1663_);
lean_dec(v___x_1662_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v_res_1664_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v___x_1668_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_pos_1663_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
else
{
lean_object* v_pos_1673_; lean_object* v_err_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1704_; 
v_pos_1673_ = lean_ctor_get(v___x_1662_, 0);
v_err_1674_ = lean_ctor_get(v___x_1662_, 1);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1676_ = v___x_1662_;
v_isShared_1677_ = v_isSharedCheck_1704_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_err_1674_);
lean_inc(v_pos_1673_);
lean_dec(v___x_1662_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1704_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v_snd_1678_; uint8_t v_decide_1679_; 
v_snd_1678_ = lean_ctor_get(v_pos_1673_, 1);
v_decide_1679_ = lean_nat_dec_eq(v_snd_1657_, v_snd_1678_);
lean_dec(v_snd_1657_);
if (v_decide_1679_ == 0)
{
lean_object* v___x_1681_; 
if (v_isShared_1677_ == 0)
{
v___x_1681_ = v___x_1676_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_pos_1673_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_err_1674_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_del_object(v___x_1676_);
lean_dec(v_err_1674_);
v___x_1683_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___x_1684_ = l_Std_Internal_Parsec_String_pstring(v___x_1683_, v_pos_1673_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_pos_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1693_; 
v_pos_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v___x_1684_, 1);
lean_dec(v_unused_1694_);
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_pos_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = lean_box(2);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 1, v___x_1689_);
v___x_1691_ = v___x_1687_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_pos_1685_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_object* v_pos_1695_; lean_object* v_err_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_pos_1695_ = lean_ctor_get(v___x_1684_, 0);
v_err_1696_ = lean_ctor_get(v___x_1684_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1684_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_err_1696_);
lean_inc(v_pos_1695_);
lean_dec(v___x_1684_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_pos_1695_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_err_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
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
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object* v_j_1706_, lean_object* v_k_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Json_getObjValD(v_j_1706_, v_k_1707_);
switch(lean_obj_tag(v___x_1708_))
{
case 3:
{
lean_object* v_s_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1717_; 
v_s_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_s_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 0);
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_s_1709_);
v___x_1714_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
return v___x_1715_;
}
}
}
case 2:
{
lean_object* v_n_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1726_; 
v_n_1718_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1720_ = v___x_1708_;
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_n_1718_);
lean_dec(v___x_1708_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set_tag(v___x_1720_, 1);
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_n_1718_);
v___x_1723_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
return v___x_1724_;
}
}
}
default: 
{
lean_object* v___x_1727_; 
lean_dec(v___x_1708_);
v___x_1727_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object* v_j_1728_, lean_object* v_k_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_j_1728_, v_k_1729_);
lean_dec_ref(v_k_1729_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object* v_j_1731_, lean_object* v_k_1732_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Json_getObjValD(v_j_1731_, v_k_1732_);
if (lean_obj_tag(v___x_1735_) == 2)
{
lean_object* v_n_1736_; lean_object* v_mantissa_1737_; lean_object* v_exponent_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v_n_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc_ref(v_n_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v_mantissa_1737_ = lean_ctor_get(v_n_1736_, 0);
lean_inc(v_mantissa_1737_);
v_exponent_1738_ = lean_ctor_get(v_n_1736_, 1);
lean_inc(v_exponent_1738_);
lean_dec_ref(v_n_1736_);
v___x_1739_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_1740_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1741_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_1742_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_1744_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_1746_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1747_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_1748_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1749_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_1750_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_1752_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_1754_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_1756_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_1758_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_1760_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_1762_ = lean_int_dec_eq(v_mantissa_1737_, v___x_1761_);
lean_dec(v_mantissa_1737_);
if (v___x_1762_ == 0)
{
lean_dec(v_exponent_1738_);
goto v___jp_1733_;
}
else
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1763_);
lean_dec(v_exponent_1738_);
if (v___x_1764_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1765_; 
v___x_1765_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_1765_;
}
}
}
else
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
lean_dec(v_mantissa_1737_);
v___x_1766_ = lean_unsigned_to_nat(0u);
v___x_1767_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1766_);
lean_dec(v_exponent_1738_);
if (v___x_1767_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1768_; 
v___x_1768_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_1768_;
}
}
}
else
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
lean_dec(v_mantissa_1737_);
v___x_1769_ = lean_unsigned_to_nat(0u);
v___x_1770_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1769_);
lean_dec(v_exponent_1738_);
if (v___x_1770_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1771_; 
v___x_1771_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_1771_;
}
}
}
else
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
lean_dec(v_mantissa_1737_);
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1772_);
lean_dec(v_exponent_1738_);
if (v___x_1773_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1774_; 
v___x_1774_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_1774_;
}
}
}
else
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
lean_dec(v_mantissa_1737_);
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1775_);
lean_dec(v_exponent_1738_);
if (v___x_1776_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_1777_;
}
}
}
else
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
lean_dec(v_mantissa_1737_);
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1778_);
lean_dec(v_exponent_1738_);
if (v___x_1779_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_1780_;
}
}
}
else
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
lean_dec(v_mantissa_1737_);
v___x_1781_ = lean_unsigned_to_nat(0u);
v___x_1782_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1781_);
lean_dec(v_exponent_1738_);
if (v___x_1782_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_1783_;
}
}
}
else
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
lean_dec(v_mantissa_1737_);
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1784_);
lean_dec(v_exponent_1738_);
if (v___x_1785_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1786_; 
v___x_1786_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_1786_;
}
}
}
else
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
lean_dec(v_mantissa_1737_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1787_);
lean_dec(v_exponent_1738_);
if (v___x_1788_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_1789_;
}
}
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
lean_dec(v_mantissa_1737_);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1790_);
lean_dec(v_exponent_1738_);
if (v___x_1791_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1792_; 
v___x_1792_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_1792_;
}
}
}
else
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
lean_dec(v_mantissa_1737_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1793_);
lean_dec(v_exponent_1738_);
if (v___x_1794_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1795_; 
v___x_1795_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_1795_;
}
}
}
else
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
lean_dec(v_mantissa_1737_);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = lean_nat_dec_eq(v_exponent_1738_, v___x_1796_);
lean_dec(v_exponent_1738_);
if (v___x_1797_ == 0)
{
goto v___jp_1733_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_1798_;
}
}
}
else
{
lean_dec(v___x_1735_);
goto v___jp_1733_;
}
v___jp_1733_:
{
lean_object* v___x_1734_; 
v___x_1734_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object* v_j_1799_, lean_object* v_k_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_j_1799_, v_k_1800_);
lean_dec_ref(v_k_1800_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object* v_j_1802_, lean_object* v_k_1803_){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = l_Lean_Json_getObjValD(v_j_1802_, v_k_1803_);
v___x_1805_ = l_Lean_Json_getStr_x3f(v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object* v_j_1806_, lean_object* v_k_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_j_1806_, v_k_1807_);
lean_dec_ref(v_k_1807_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object* v_input_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v_fst_1845_; lean_object* v_snd_1846_; lean_object* v___x_1847_; uint8_t v_decide_1848_; 
v_fst_1845_ = lean_ctor_get(v_a_1819_, 0);
v_snd_1846_ = lean_ctor_get(v_a_1819_, 1);
v___x_1847_ = lean_string_utf8_byte_size(v_fst_1845_);
v_decide_1848_ = lean_nat_dec_eq(v_snd_1846_, v___x_1847_);
if (v_decide_1848_ == 0)
{
lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_2198_; 
lean_inc(v_snd_1846_);
lean_inc(v_fst_1845_);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_a_1819_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; lean_object* v_unused_2200_; 
v_unused_2199_ = lean_ctor_get(v_a_1819_, 1);
lean_dec(v_unused_2199_);
v_unused_2200_ = lean_ctor_get(v_a_1819_, 0);
lean_dec(v_unused_2200_);
v___x_1850_ = v_a_1819_;
v_isShared_1851_ = v_isSharedCheck_2198_;
goto v_resetjp_1849_;
}
else
{
lean_dec(v_a_1819_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_2198_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = lean_string_utf8_next_fast(v_fst_1845_, v_snd_1846_);
lean_dec(v_snd_1846_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_fst_1845_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_2197_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; 
v___x_1855_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1854_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_pos_1856_; lean_object* v_res_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_2187_; 
v_pos_1856_ = lean_ctor_get(v___x_1855_, 0);
v_res_1857_ = lean_ctor_get(v___x_1855_, 1);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_1859_ = v___x_1855_;
v_isShared_1860_ = v_isSharedCheck_2187_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_res_1857_);
lean_inc(v_pos_1856_);
lean_dec(v___x_1855_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_2187_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_fst_1861_; lean_object* v_snd_1862_; lean_object* v___x_1863_; uint8_t v_decide_1864_; 
v_fst_1861_ = lean_ctor_get(v_pos_1856_, 0);
v_snd_1862_ = lean_ctor_get(v_pos_1856_, 1);
v___x_1863_ = lean_string_utf8_byte_size(v_fst_1861_);
v_decide_1864_ = lean_nat_dec_eq(v_snd_1862_, v___x_1863_);
if (v_decide_1864_ == 0)
{
lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_2180_; 
lean_inc(v_snd_1862_);
lean_inc(v_fst_1861_);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_pos_1856_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; lean_object* v_unused_2182_; 
v_unused_2181_ = lean_ctor_get(v_pos_1856_, 1);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_pos_1856_, 0);
lean_dec(v_unused_2182_);
v___x_1866_ = v_pos_1856_;
v_isShared_1867_ = v_isSharedCheck_2180_;
goto v_resetjp_1865_;
}
else
{
lean_dec(v_pos_1856_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_2180_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1868_ = lean_string_utf8_next_fast(v_fst_1861_, v_snd_1862_);
lean_dec(v_snd_1862_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 1, v___x_1868_);
v___x_1870_ = v___x_1866_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_fst_1861_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_2179_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v_id_1872_; uint8_t v_code_1873_; lean_object* v_message_1874_; lean_object* v_data_x3f_1875_; lean_object* v_a_1884_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
v___x_1890_ = lean_string_dec_eq(v_res_1857_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
v___x_1892_ = lean_string_dec_eq(v_res_1857_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1894_ = lean_string_dec_eq(v_res_1857_, v___x_1893_);
lean_dec(v_res_1857_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_del_object(v___x_1859_);
lean_dec_ref(v_input_1818_);
v___x_1895_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3));
v___x_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1870_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_Json_parse(v_input_1818_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1906_; 
lean_del_object(v___x_1859_);
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1900_ = v___x_1897_;
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1897_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1906_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set_tag(v___x_1900_, 1);
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1870_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
return v___x_1904_;
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1908_; 
v_a_1907_ = lean_ctor_get(v___x_1897_, 0);
lean_inc_n(v_a_1907_, 2);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1908_ = l_Lean_Json_getObjVal_x3f(v_a_1907_, v___x_1891_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; 
lean_dec(v_a_1907_);
lean_del_object(v___x_1859_);
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v_a_1884_ = v_a_1909_;
goto v___jp_1883_;
}
else
{
lean_object* v_a_1910_; 
v_a_1910_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1908_, 1);
if (lean_obj_tag(v_a_1910_) == 3)
{
lean_object* v_s_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v_s_1911_ = lean_ctor_get(v_a_1910_, 0);
lean_inc_ref(v_s_1911_);
lean_dec_ref_known(v_a_1910_, 1);
v___x_1912_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1913_ = lean_string_dec_eq(v_s_1911_, v___x_1912_);
lean_dec_ref(v_s_1911_);
if (v___x_1913_ == 0)
{
lean_dec(v_a_1907_);
lean_del_object(v___x_1859_);
goto v___jp_1887_;
}
else
{
lean_object* v___x_1914_; 
lean_inc(v_a_1907_);
v___x_1914_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_1907_, v___x_1889_);
if (lean_obj_tag(v___x_1914_) == 0)
{
goto v___jp_1942_;
}
else
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1907_);
v___x_1948_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1907_, v___x_1947_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_dec_ref_known(v___x_1948_, 1);
goto v___jp_1942_;
}
else
{
lean_dec_ref_known(v___x_1948_, 1);
lean_dec_ref_known(v___x_1914_, 1);
lean_dec(v_a_1907_);
lean_del_object(v___x_1859_);
goto v___jp_1880_;
}
}
v___jp_1915_:
{
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1916_; 
lean_dec(v_a_1907_);
lean_del_object(v___x_1859_);
v_a_1916_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1914_, 1);
v_a_1884_ = v_a_1916_;
goto v___jp_1883_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1914_, 1);
v___x_1918_ = l_Lean_Json_getObjVal_x3f(v_a_1907_, v___x_1893_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; 
lean_dec(v_a_1917_);
lean_del_object(v___x_1859_);
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v_a_1884_ = v_a_1919_;
goto v___jp_1883_;
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1920_ = lean_ctor_get(v___x_1918_, 0);
lean_inc_n(v_a_1920_, 2);
lean_dec_ref_known(v___x_1918_, 1);
v___x_1921_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1922_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_1920_, v___x_1921_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; 
lean_dec(v_a_1920_);
lean_dec(v_a_1917_);
lean_del_object(v___x_1859_);
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
v_a_1884_ = v_a_1923_;
goto v___jp_1883_;
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_a_1924_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1922_, 1);
v___x_1925_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1920_);
v___x_1926_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1920_, v___x_1925_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; 
lean_dec(v_a_1924_);
lean_dec(v_a_1920_);
lean_dec(v_a_1917_);
lean_del_object(v___x_1859_);
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
v_a_1884_ = v_a_1927_;
goto v___jp_1883_;
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_a_1928_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1926_, 1);
v___x_1929_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1930_ = l_Lean_Json_getObjVal_x3f(v_a_1920_, v___x_1929_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v___x_1931_; uint8_t v___x_1932_; 
lean_dec_ref_known(v___x_1930_, 1);
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_unbox(v_a_1924_);
lean_dec(v_a_1924_);
v_id_1872_ = v_a_1917_;
v_code_1873_ = v___x_1932_;
v_message_1874_ = v_a_1928_;
v_data_x3f_1875_ = v___x_1931_;
goto v___jp_1871_;
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1941_; 
v_a_1933_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1935_ = v___x_1930_;
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1930_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
uint8_t v___x_1939_; 
v___x_1939_ = lean_unbox(v_a_1924_);
lean_dec(v_a_1924_);
v_id_1872_ = v_a_1917_;
v_code_1873_ = v___x_1939_;
v_message_1874_ = v_a_1928_;
v_data_x3f_1875_ = v___x_1938_;
goto v___jp_1871_;
}
}
}
}
}
}
}
}
v___jp_1942_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1907_);
v___x_1944_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1907_, v___x_1943_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_dec_ref_known(v___x_1944_, 1);
if (lean_obj_tag(v___x_1914_) == 0)
{
goto v___jp_1915_;
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_1907_);
v___x_1946_ = l_Lean_Json_getObjVal_x3f(v_a_1907_, v___x_1945_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_dec_ref_known(v___x_1946_, 1);
goto v___jp_1915_;
}
else
{
lean_dec_ref_known(v___x_1946_, 1);
lean_dec_ref_known(v___x_1914_, 1);
lean_dec(v_a_1907_);
lean_del_object(v___x_1859_);
goto v___jp_1880_;
}
}
}
else
{
lean_dec_ref_known(v___x_1944_, 1);
lean_dec_ref(v___x_1914_);
lean_dec(v_a_1907_);
lean_del_object(v___x_1859_);
goto v___jp_1880_;
}
}
}
}
else
{
lean_dec(v_a_1910_);
lean_dec(v_a_1907_);
lean_del_object(v___x_1859_);
goto v___jp_1887_;
}
}
}
}
}
else
{
lean_object* v___x_1949_; 
lean_del_object(v___x_1859_);
lean_dec(v_res_1857_);
lean_dec_ref(v_input_1818_);
v___x_1949_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1870_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_pos_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1998_; 
v_pos_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v___x_1949_, 1);
lean_dec(v_unused_1999_);
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1998_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_pos_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1998_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v_fst_1954_; lean_object* v_snd_1955_; uint8_t v___y_1957_; lean_object* v___x_1996_; uint8_t v_decide_1997_; 
v_fst_1954_ = lean_ctor_get(v_pos_1950_, 0);
v_snd_1955_ = lean_ctor_get(v_pos_1950_, 1);
v___x_1996_ = lean_string_utf8_byte_size(v_fst_1954_);
v_decide_1997_ = lean_nat_dec_eq(v_snd_1955_, v___x_1996_);
if (v_decide_1997_ == 0)
{
v___y_1957_ = v___x_1892_;
goto v___jp_1956_;
}
else
{
v___y_1957_ = v___x_1890_;
goto v___jp_1956_;
}
v___jp_1956_:
{
if (v___y_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1958_ = lean_box(0);
if (v_isShared_1953_ == 0)
{
lean_ctor_set_tag(v___x_1952_, 1);
lean_ctor_set(v___x_1952_, 1, v___x_1958_);
v___x_1960_ = v___x_1952_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_pos_1950_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
else
{
lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1993_; 
lean_inc(v_snd_1955_);
lean_inc(v_fst_1954_);
lean_del_object(v___x_1952_);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_pos_1950_);
if (v_isSharedCheck_1993_ == 0)
{
lean_object* v_unused_1994_; lean_object* v_unused_1995_; 
v_unused_1994_ = lean_ctor_get(v_pos_1950_, 1);
lean_dec(v_unused_1994_);
v_unused_1995_ = lean_ctor_get(v_pos_1950_, 0);
lean_dec(v_unused_1995_);
v___x_1963_ = v_pos_1950_;
v_isShared_1964_ = v_isSharedCheck_1993_;
goto v_resetjp_1962_;
}
else
{
lean_dec(v_pos_1950_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1993_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = lean_string_utf8_next_fast(v_fst_1954_, v_snd_1955_);
lean_dec(v_snd_1955_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v___x_1965_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_fst_1954_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1968_; 
v___x_1968_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1967_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_pos_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1981_; 
v_pos_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v___x_1968_, 1);
lean_dec(v_unused_1982_);
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1981_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_pos_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1981_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_fst_1973_; lean_object* v_snd_1974_; lean_object* v___x_1975_; uint8_t v_decide_1976_; 
v_fst_1973_ = lean_ctor_get(v_pos_1969_, 0);
v_snd_1974_ = lean_ctor_get(v_pos_1969_, 1);
v___x_1975_ = lean_string_utf8_byte_size(v_fst_1973_);
v_decide_1976_ = lean_nat_dec_eq(v_snd_1974_, v___x_1975_);
if (v_decide_1976_ == 0)
{
lean_inc(v_snd_1974_);
lean_inc(v_fst_1973_);
lean_del_object(v___x_1971_);
lean_dec(v_pos_1969_);
v___y_1821_ = v_fst_1973_;
v___y_1822_ = v_snd_1974_;
goto v___jp_1820_;
}
else
{
if (v___x_1890_ == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_box(0);
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 1);
lean_ctor_set(v___x_1971_, 1, v___x_1977_);
v___x_1979_ = v___x_1971_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_pos_1969_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
else
{
lean_inc(v_snd_1974_);
lean_inc(v_fst_1973_);
lean_del_object(v___x_1971_);
lean_dec(v_pos_1969_);
v___y_1821_ = v_fst_1973_;
v___y_1822_ = v_snd_1974_;
goto v___jp_1820_;
}
}
}
}
else
{
lean_object* v_pos_1983_; lean_object* v_err_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
v_pos_1983_ = lean_ctor_get(v___x_1968_, 0);
v_err_1984_ = lean_ctor_get(v___x_1968_, 1);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1968_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_err_1984_);
lean_inc(v_pos_1983_);
lean_dec(v___x_1968_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_pos_1983_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_err_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
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
lean_object* v_pos_2000_; lean_object* v_err_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
v_pos_2000_ = lean_ctor_get(v___x_1949_, 0);
v_err_2001_ = lean_ctor_get(v___x_1949_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1949_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_err_2001_);
lean_inc(v_pos_2000_);
lean_dec(v___x_1949_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_pos_2000_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_err_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
else
{
lean_object* v___x_2009_; 
lean_del_object(v___x_1859_);
lean_dec(v_res_1857_);
lean_dec_ref(v_input_1818_);
v___x_2009_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(v___x_1870_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_pos_2010_; lean_object* v_res_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2169_; 
v_pos_2010_ = lean_ctor_get(v___x_2009_, 0);
v_res_2011_ = lean_ctor_get(v___x_2009_, 1);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2013_ = v___x_2009_;
v_isShared_2014_ = v_isSharedCheck_2169_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_res_2011_);
lean_inc(v_pos_2010_);
lean_dec(v___x_2009_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2169_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_fst_2020_; lean_object* v_snd_2021_; lean_object* v___x_2022_; uint8_t v_decide_2023_; 
v_fst_2020_ = lean_ctor_get(v_pos_2010_, 0);
v_snd_2021_ = lean_ctor_get(v_pos_2010_, 1);
v___x_2022_ = lean_string_utf8_byte_size(v_fst_2020_);
v_decide_2023_ = lean_nat_dec_eq(v_snd_2021_, v___x_2022_);
if (v_decide_2023_ == 0)
{
if (v___x_1890_ == 0)
{
lean_dec(v_res_2011_);
goto v___jp_2015_;
}
else
{
lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2166_; 
lean_inc(v_snd_2021_);
lean_inc(v_fst_2020_);
lean_del_object(v___x_2013_);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_pos_2010_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; lean_object* v_unused_2168_; 
v_unused_2167_ = lean_ctor_get(v_pos_2010_, 1);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_pos_2010_, 0);
lean_dec(v_unused_2168_);
v___x_2025_ = v_pos_2010_;
v_isShared_2026_ = v_isSharedCheck_2166_;
goto v_resetjp_2024_;
}
else
{
lean_dec(v_pos_2010_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2166_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = lean_string_utf8_next_fast(v_fst_2020_, v_snd_2021_);
lean_dec(v_snd_2021_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 1, v___x_2027_);
v___x_2029_ = v___x_2025_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_fst_2020_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2029_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_pos_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2154_; 
v_pos_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v___x_2030_, 1);
lean_dec(v_unused_2155_);
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2154_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_pos_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2154_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v_fst_2035_; lean_object* v_snd_2036_; lean_object* v___x_2037_; uint8_t v_decide_2038_; 
v_fst_2035_ = lean_ctor_get(v_pos_2031_, 0);
v_snd_2036_ = lean_ctor_get(v_pos_2031_, 1);
v___x_2037_ = lean_string_utf8_byte_size(v_fst_2035_);
v_decide_2038_ = lean_nat_dec_eq(v_snd_2036_, v___x_2037_);
if (v_decide_2038_ == 0)
{
lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2147_; 
lean_inc(v_snd_2036_);
lean_inc(v_fst_2035_);
lean_del_object(v___x_2033_);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_pos_2031_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; lean_object* v_unused_2149_; 
v_unused_2148_ = lean_ctor_get(v_pos_2031_, 1);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_pos_2031_, 0);
lean_dec(v_unused_2149_);
v___x_2040_ = v_pos_2031_;
v_isShared_2041_ = v_isSharedCheck_2147_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v_pos_2031_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2147_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_string_utf8_next_fast(v_fst_2035_, v_snd_2036_);
lean_dec(v_snd_2036_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 1, v___x_2042_);
v___x_2044_ = v___x_2040_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_fst_2035_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; 
v___x_2045_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2044_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_pos_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2135_; 
v_pos_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; 
v_unused_2136_ = lean_ctor_get(v___x_2045_, 1);
lean_dec(v_unused_2136_);
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2135_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_pos_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2135_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v_fst_2050_; lean_object* v_snd_2051_; lean_object* v___x_2052_; uint8_t v_decide_2053_; 
v_fst_2050_ = lean_ctor_get(v_pos_2046_, 0);
v_snd_2051_ = lean_ctor_get(v_pos_2046_, 1);
v___x_2052_ = lean_string_utf8_byte_size(v_fst_2050_);
v_decide_2053_ = lean_nat_dec_eq(v_snd_2051_, v___x_2052_);
if (v_decide_2053_ == 0)
{
lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2128_; 
lean_inc(v_snd_2051_);
lean_inc(v_fst_2050_);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_pos_2046_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; lean_object* v_unused_2130_; 
v_unused_2129_ = lean_ctor_get(v_pos_2046_, 1);
lean_dec(v_unused_2129_);
v_unused_2130_ = lean_ctor_get(v_pos_2046_, 0);
lean_dec(v_unused_2130_);
v___x_2055_ = v_pos_2046_;
v_isShared_2056_ = v_isSharedCheck_2128_;
goto v_resetjp_2054_;
}
else
{
lean_dec(v_pos_2046_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2128_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2057_ = lean_string_utf8_next_fast(v_fst_2050_, v_snd_2051_);
lean_dec(v_snd_2051_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 1, v___x_2057_);
v___x_2059_ = v___x_2055_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_fst_2050_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2060_; 
v___x_2060_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2059_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_pos_2061_; lean_object* v_res_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2117_; 
v_pos_2061_ = lean_ctor_get(v___x_2060_, 0);
v_res_2062_ = lean_ctor_get(v___x_2060_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2064_ = v___x_2060_;
v_isShared_2065_ = v_isSharedCheck_2117_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_res_2062_);
lean_inc(v_pos_2061_);
lean_dec(v___x_2060_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2117_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2072_ = lean_string_dec_eq(v_res_2062_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
lean_del_object(v___x_2064_);
v___x_2073_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2074_ = lean_string_dec_eq(v_res_2062_, v___x_2073_);
lean_dec(v_res_2062_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
lean_dec(v_res_2011_);
v___x_2075_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5));
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 1);
lean_ctor_set(v___x_2048_, 1, v___x_2075_);
lean_ctor_set(v___x_2048_, 0, v_pos_2061_);
v___x_2077_ = v___x_2048_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_pos_2061_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2079_, 0, v_res_2011_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 1, v___x_2079_);
lean_ctor_set(v___x_2048_, 0, v_pos_2061_);
v___x_2081_ = v___x_2048_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_pos_2061_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_object* v_fst_2083_; lean_object* v_snd_2084_; lean_object* v___x_2085_; uint8_t v_decide_2086_; 
lean_dec(v_res_2062_);
lean_del_object(v___x_2048_);
v_fst_2083_ = lean_ctor_get(v_pos_2061_, 0);
v_snd_2084_ = lean_ctor_get(v_pos_2061_, 1);
v___x_2085_ = lean_string_utf8_byte_size(v_fst_2083_);
v_decide_2086_ = lean_nat_dec_eq(v_snd_2084_, v___x_2085_);
if (v_decide_2086_ == 0)
{
if (v___x_2072_ == 0)
{
lean_dec(v_res_2011_);
goto v___jp_2066_;
}
else
{
lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2114_; 
lean_inc(v_snd_2084_);
lean_inc(v_fst_2083_);
lean_del_object(v___x_2064_);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_pos_2061_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; lean_object* v_unused_2116_; 
v_unused_2115_ = lean_ctor_get(v_pos_2061_, 1);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v_pos_2061_, 0);
lean_dec(v_unused_2116_);
v___x_2088_ = v_pos_2061_;
v_isShared_2089_ = v_isSharedCheck_2114_;
goto v_resetjp_2087_;
}
else
{
lean_dec(v_pos_2061_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2114_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = lean_string_utf8_next_fast(v_fst_2083_, v_snd_2084_);
lean_dec(v_snd_2084_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v___x_2090_);
v___x_2092_ = v___x_2088_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_fst_2083_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; 
v___x_2093_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2092_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_pos_2094_; lean_object* v_res_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
v_pos_2094_ = lean_ctor_get(v___x_2093_, 0);
v_res_2095_ = lean_ctor_get(v___x_2093_, 1);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2097_ = v___x_2093_;
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_res_2095_);
lean_inc(v_pos_2094_);
lean_dec(v___x_2093_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v_res_2011_);
lean_ctor_set(v___x_2099_, 1, v_res_2095_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v___x_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_pos_2094_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
else
{
lean_object* v_pos_2104_; lean_object* v_err_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v_res_2011_);
v_pos_2104_ = lean_ctor_get(v___x_2093_, 0);
v_err_2105_ = lean_ctor_get(v___x_2093_, 1);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2093_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_err_2105_);
lean_inc(v_pos_2104_);
lean_dec(v___x_2093_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_pos_2104_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_err_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2011_);
goto v___jp_2066_;
}
}
v___jp_2066_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_box(0);
if (v_isShared_2065_ == 0)
{
lean_ctor_set_tag(v___x_2064_, 1);
lean_ctor_set(v___x_2064_, 1, v___x_2067_);
v___x_2069_ = v___x_2064_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_pos_2061_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_pos_2118_; lean_object* v_err_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_del_object(v___x_2048_);
lean_dec(v_res_2011_);
v_pos_2118_ = lean_ctor_get(v___x_2060_, 0);
v_err_2119_ = lean_ctor_get(v___x_2060_, 1);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2060_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_err_2119_);
lean_inc(v_pos_2118_);
lean_dec(v___x_2060_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_pos_2118_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_err_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
lean_dec(v_res_2011_);
v___x_2131_ = lean_box(0);
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 1);
lean_ctor_set(v___x_2048_, 1, v___x_2131_);
v___x_2133_ = v___x_2048_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_pos_2046_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_pos_2137_; lean_object* v_err_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v_res_2011_);
v_pos_2137_ = lean_ctor_get(v___x_2045_, 0);
v_err_2138_ = lean_ctor_get(v___x_2045_, 1);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2045_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_err_2138_);
lean_inc(v_pos_2137_);
lean_dec(v___x_2045_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_pos_2137_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_err_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
lean_dec(v_res_2011_);
v___x_2150_ = lean_box(0);
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 1);
lean_ctor_set(v___x_2033_, 1, v___x_2150_);
v___x_2152_ = v___x_2033_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_pos_2031_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v_pos_2156_; lean_object* v_err_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_res_2011_);
v_pos_2156_ = lean_ctor_get(v___x_2030_, 0);
v_err_2157_ = lean_ctor_get(v___x_2030_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2030_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_err_2157_);
lean_inc(v_pos_2156_);
lean_dec(v___x_2030_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_pos_2156_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_err_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2011_);
goto v___jp_2015_;
}
v___jp_2015_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_box(0);
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 1);
lean_ctor_set(v___x_2013_, 1, v___x_2016_);
v___x_2018_ = v___x_2013_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_pos_2010_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
lean_object* v_pos_2170_; lean_object* v_err_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
v_pos_2170_ = lean_ctor_get(v___x_2009_, 0);
v_err_2171_ = lean_ctor_get(v___x_2009_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2009_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_err_2171_);
lean_inc(v_pos_2170_);
lean_dec(v___x_2009_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_pos_2170_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_err_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
v___jp_1871_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1876_, 0, v_id_1872_);
lean_ctor_set(v___x_1876_, 1, v_message_1874_);
lean_ctor_set(v___x_1876_, 2, v_data_x3f_1875_);
lean_ctor_set_uint8(v___x_1876_, sizeof(void*)*3, v_code_1873_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 1, v___x_1876_);
lean_ctor_set(v___x_1859_, 0, v___x_1870_);
v___x_1878_ = v___x_1859_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1870_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
v___jp_1880_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1));
v___x_1882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1870_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
return v___x_1882_;
}
v___jp_1883_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1885_, 0, v_a_1884_);
v___x_1886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1870_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
return v___x_1886_;
}
v___jp_1887_:
{
lean_object* v___x_1888_; 
v___x_1888_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_1884_ = v___x_1888_;
goto v___jp_1883_;
}
}
}
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
lean_dec(v_res_1857_);
lean_dec_ref(v_input_1818_);
v___x_2183_ = lean_box(0);
if (v_isShared_1860_ == 0)
{
lean_ctor_set_tag(v___x_1859_, 1);
lean_ctor_set(v___x_1859_, 1, v___x_2183_);
v___x_2185_ = v___x_1859_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_pos_1856_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_pos_2188_; lean_object* v_err_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec_ref(v_input_1818_);
v_pos_2188_ = lean_ctor_get(v___x_1855_, 0);
v_err_2189_ = lean_ctor_get(v___x_1855_, 1);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_1855_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_err_2189_);
lean_inc(v_pos_2188_);
lean_dec(v___x_1855_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_pos_2188_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_err_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec_ref(v_input_1818_);
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2202_, 0, v_a_1819_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
return v___x_2202_;
}
v___jp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_string_utf8_next_fast(v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___y_1821_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1824_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_pos_1826_; lean_object* v_res_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1835_; 
v_pos_1826_ = lean_ctor_get(v___x_1825_, 0);
v_res_1827_ = lean_ctor_get(v___x_1825_, 1);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1829_ = v___x_1825_;
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_res_1827_);
lean_inc(v_pos_1826_);
lean_dec(v___x_1825_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1831_, 0, v_res_1827_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v___x_1831_);
v___x_1833_ = v___x_1829_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_pos_1826_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
else
{
lean_object* v_pos_1836_; lean_object* v_err_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
v_pos_1836_ = lean_ctor_get(v___x_1825_, 0);
v_err_1837_ = lean_ctor_get(v___x_1825_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1825_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_err_1837_);
lean_inc(v_pos_1836_);
lean_dec(v___x_1825_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_pos_1836_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_err_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object* v_input_2203_){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_inc_ref(v_input_2203_);
v___x_2204_ = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser), 2, 1);
lean_closure_set(v___x_2204_, 0, v_input_2203_);
v___x_2205_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2204_, v_input_2203_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___impl(uint8_t v_x_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_box(v_x_2206_);
v___x_2208_ = lean_obj_tag_nat(v___x_2207_);
lean_dec(v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___impl___boxed(lean_object* v_x_2209_){
_start:
{
uint8_t v_x_4__boxed_2210_; lean_object* v_res_2211_; 
v_x_4__boxed_2210_ = lean_unbox(v_x_2209_);
v_res_2211_ = l_Lean_JsonRpc_MessageDirection_ctorIdx___impl(v_x_4__boxed_2210_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object* v_k_2212_){
_start:
{
lean_inc(v_k_2212_);
return v_k_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object* v_k_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(v_k_2213_);
lean_dec(v_k_2213_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object* v_motive_2215_, lean_object* v_ctorIdx_2216_, uint8_t v_t_2217_, lean_object* v_h_2218_, lean_object* v_k_2219_){
_start:
{
lean_inc(v_k_2219_);
return v_k_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object* v_motive_2220_, lean_object* v_ctorIdx_2221_, lean_object* v_t_2222_, lean_object* v_h_2223_, lean_object* v_k_2224_){
_start:
{
uint8_t v_t_boxed_2225_; lean_object* v_res_2226_; 
v_t_boxed_2225_ = lean_unbox(v_t_2222_);
v_res_2226_ = l_Lean_JsonRpc_MessageDirection_ctorElim(v_motive_2220_, v_ctorIdx_2221_, v_t_boxed_2225_, v_h_2223_, v_k_2224_);
lean_dec(v_k_2224_);
lean_dec(v_ctorIdx_2221_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object* v_clientToServer_2227_){
_start:
{
lean_inc(v_clientToServer_2227_);
return v_clientToServer_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object* v_clientToServer_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(v_clientToServer_2228_);
lean_dec(v_clientToServer_2228_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object* v_motive_2230_, uint8_t v_t_2231_, lean_object* v_h_2232_, lean_object* v_clientToServer_2233_){
_start:
{
lean_inc(v_clientToServer_2233_);
return v_clientToServer_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object* v_motive_2234_, lean_object* v_t_2235_, lean_object* v_h_2236_, lean_object* v_clientToServer_2237_){
_start:
{
uint8_t v_t_boxed_2238_; lean_object* v_res_2239_; 
v_t_boxed_2238_ = lean_unbox(v_t_2235_);
v_res_2239_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(v_motive_2234_, v_t_boxed_2238_, v_h_2236_, v_clientToServer_2237_);
lean_dec(v_clientToServer_2237_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object* v_serverToClient_2240_){
_start:
{
lean_inc(v_serverToClient_2240_);
return v_serverToClient_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object* v_serverToClient_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(v_serverToClient_2241_);
lean_dec(v_serverToClient_2241_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object* v_motive_2243_, uint8_t v_t_2244_, lean_object* v_h_2245_, lean_object* v_serverToClient_2246_){
_start:
{
lean_inc(v_serverToClient_2246_);
return v_serverToClient_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object* v_motive_2247_, lean_object* v_t_2248_, lean_object* v_h_2249_, lean_object* v_serverToClient_2250_){
_start:
{
uint8_t v_t_boxed_2251_; lean_object* v_res_2252_; 
v_t_boxed_2251_ = lean_unbox(v_t_2248_);
v_res_2252_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(v_motive_2247_, v_t_boxed_2251_, v_h_2249_, v_serverToClient_2250_);
lean_dec(v_serverToClient_2250_);
return v_res_2252_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default(void){
_start:
{
uint8_t v___x_2253_; 
v___x_2253_ = 0;
return v___x_2253_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection(void){
_start:
{
uint8_t v___x_2254_; 
v___x_2254_ = 0;
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object* v_json_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Json_getTag_x3f(v_json_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v___x_2271_; 
v___x_2271_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1));
return v___x_2271_;
}
else
{
lean_object* v_val_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_val_2272_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_val_2272_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2273_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2));
v___x_2274_ = lean_string_dec_eq(v_val_2272_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3));
v___x_2276_ = lean_string_dec_eq(v_val_2272_, v___x_2275_);
lean_dec(v_val_2272_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; 
v___x_2277_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5));
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; 
v___x_2278_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6));
return v___x_2278_;
}
}
else
{
lean_object* v___x_2279_; 
lean_dec(v_val_2272_);
v___x_2279_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7));
return v___x_2279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t v_x_2286_){
_start:
{
if (v_x_2286_ == 0)
{
lean_object* v___x_2287_; 
v___x_2287_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0));
return v___x_2287_;
}
else
{
lean_object* v___x_2288_; 
v___x_2288_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1));
return v___x_2288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object* v_x_2289_){
_start:
{
uint8_t v_x_44__boxed_2290_; lean_object* v_res_2291_; 
v_x_44__boxed_2290_ = lean_unbox(v_x_2289_);
v_res_2291_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_x_44__boxed_2290_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___impl(uint8_t v_x_2294_){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_box(v_x_2294_);
v___x_2296_ = lean_obj_tag_nat(v___x_2295_);
lean_dec(v___x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___impl___boxed(lean_object* v_x_2297_){
_start:
{
uint8_t v_x_4__boxed_2298_; lean_object* v_res_2299_; 
v_x_4__boxed_2298_ = lean_unbox(v_x_2297_);
v_res_2299_ = l_Lean_JsonRpc_MessageKind_ctorIdx___impl(v_x_4__boxed_2298_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object* v_k_2300_){
_start:
{
lean_inc(v_k_2300_);
return v_k_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object* v_k_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_JsonRpc_MessageKind_ctorElim___redArg(v_k_2301_);
lean_dec(v_k_2301_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object* v_motive_2303_, lean_object* v_ctorIdx_2304_, uint8_t v_t_2305_, lean_object* v_h_2306_, lean_object* v_k_2307_){
_start:
{
lean_inc(v_k_2307_);
return v_k_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object* v_motive_2308_, lean_object* v_ctorIdx_2309_, lean_object* v_t_2310_, lean_object* v_h_2311_, lean_object* v_k_2312_){
_start:
{
uint8_t v_t_boxed_2313_; lean_object* v_res_2314_; 
v_t_boxed_2313_ = lean_unbox(v_t_2310_);
v_res_2314_ = l_Lean_JsonRpc_MessageKind_ctorElim(v_motive_2308_, v_ctorIdx_2309_, v_t_boxed_2313_, v_h_2311_, v_k_2312_);
lean_dec(v_k_2312_);
lean_dec(v_ctorIdx_2309_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object* v_request_2315_){
_start:
{
lean_inc(v_request_2315_);
return v_request_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object* v_request_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_JsonRpc_MessageKind_request_elim___redArg(v_request_2316_);
lean_dec(v_request_2316_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object* v_motive_2318_, uint8_t v_t_2319_, lean_object* v_h_2320_, lean_object* v_request_2321_){
_start:
{
lean_inc(v_request_2321_);
return v_request_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object* v_motive_2322_, lean_object* v_t_2323_, lean_object* v_h_2324_, lean_object* v_request_2325_){
_start:
{
uint8_t v_t_boxed_2326_; lean_object* v_res_2327_; 
v_t_boxed_2326_ = lean_unbox(v_t_2323_);
v_res_2327_ = l_Lean_JsonRpc_MessageKind_request_elim(v_motive_2322_, v_t_boxed_2326_, v_h_2324_, v_request_2325_);
lean_dec(v_request_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object* v_notification_2328_){
_start:
{
lean_inc(v_notification_2328_);
return v_notification_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object* v_notification_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_JsonRpc_MessageKind_notification_elim___redArg(v_notification_2329_);
lean_dec(v_notification_2329_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object* v_motive_2331_, uint8_t v_t_2332_, lean_object* v_h_2333_, lean_object* v_notification_2334_){
_start:
{
lean_inc(v_notification_2334_);
return v_notification_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object* v_motive_2335_, lean_object* v_t_2336_, lean_object* v_h_2337_, lean_object* v_notification_2338_){
_start:
{
uint8_t v_t_boxed_2339_; lean_object* v_res_2340_; 
v_t_boxed_2339_ = lean_unbox(v_t_2336_);
v_res_2340_ = l_Lean_JsonRpc_MessageKind_notification_elim(v_motive_2335_, v_t_boxed_2339_, v_h_2337_, v_notification_2338_);
lean_dec(v_notification_2338_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object* v_response_2341_){
_start:
{
lean_inc(v_response_2341_);
return v_response_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object* v_response_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_JsonRpc_MessageKind_response_elim___redArg(v_response_2342_);
lean_dec(v_response_2342_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object* v_motive_2344_, uint8_t v_t_2345_, lean_object* v_h_2346_, lean_object* v_response_2347_){
_start:
{
lean_inc(v_response_2347_);
return v_response_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object* v_motive_2348_, lean_object* v_t_2349_, lean_object* v_h_2350_, lean_object* v_response_2351_){
_start:
{
uint8_t v_t_boxed_2352_; lean_object* v_res_2353_; 
v_t_boxed_2352_ = lean_unbox(v_t_2349_);
v_res_2353_ = l_Lean_JsonRpc_MessageKind_response_elim(v_motive_2348_, v_t_boxed_2352_, v_h_2350_, v_response_2351_);
lean_dec(v_response_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object* v_responseError_2354_){
_start:
{
lean_inc(v_responseError_2354_);
return v_responseError_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object* v_responseError_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(v_responseError_2355_);
lean_dec(v_responseError_2355_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object* v_motive_2357_, uint8_t v_t_2358_, lean_object* v_h_2359_, lean_object* v_responseError_2360_){
_start:
{
lean_inc(v_responseError_2360_);
return v_responseError_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object* v_motive_2361_, lean_object* v_t_2362_, lean_object* v_h_2363_, lean_object* v_responseError_2364_){
_start:
{
uint8_t v_t_boxed_2365_; lean_object* v_res_2366_; 
v_t_boxed_2365_ = lean_unbox(v_t_2362_);
v_res_2366_ = l_Lean_JsonRpc_MessageKind_responseError_elim(v_motive_2361_, v_t_boxed_2365_, v_h_2363_, v_responseError_2364_);
lean_dec(v_responseError_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object* v_json_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Json_getTag_x3f(v_json_2387_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v___x_2389_; 
v___x_2389_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0));
return v___x_2389_;
}
else
{
lean_object* v_val_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_val_2390_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_val_2390_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2391_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1));
v___x_2392_ = lean_string_dec_eq(v_val_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2));
v___x_2394_ = lean_string_dec_eq(v_val_2390_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3));
v___x_2396_ = lean_string_dec_eq(v_val_2390_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4));
v___x_2398_ = lean_string_dec_eq(v_val_2390_, v___x_2397_);
lean_dec(v_val_2390_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
v___x_2399_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5));
return v___x_2399_;
}
else
{
lean_object* v___x_2400_; 
v___x_2400_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6));
return v___x_2400_;
}
}
else
{
lean_object* v___x_2401_; 
lean_dec(v_val_2390_);
v___x_2401_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7));
return v___x_2401_;
}
}
else
{
lean_object* v___x_2402_; 
lean_dec(v_val_2390_);
v___x_2402_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8));
return v___x_2402_;
}
}
else
{
lean_object* v___x_2403_; 
lean_dec(v_val_2390_);
v___x_2403_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9));
return v___x_2403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t v_x_2414_){
_start:
{
switch(v_x_2414_)
{
case 0:
{
lean_object* v___x_2415_; 
v___x_2415_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0));
return v___x_2415_;
}
case 1:
{
lean_object* v___x_2416_; 
v___x_2416_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1));
return v___x_2416_;
}
case 2:
{
lean_object* v___x_2417_; 
v___x_2417_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2));
return v___x_2417_;
}
default: 
{
lean_object* v___x_2418_; 
v___x_2418_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3));
return v___x_2418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object* v_x_2419_){
_start:
{
uint8_t v_x_84__boxed_2420_; lean_object* v_res_2421_; 
v_x_84__boxed_2420_ = lean_unbox(v_x_2419_);
v_res_2421_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_x_84__boxed_2420_);
return v_res_2421_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object* v_x_2424_){
_start:
{
switch(lean_obj_tag(v_x_2424_))
{
case 0:
{
uint8_t v___x_2425_; 
v___x_2425_ = 0;
return v___x_2425_;
}
case 1:
{
uint8_t v___x_2426_; 
v___x_2426_ = 1;
return v___x_2426_;
}
case 2:
{
uint8_t v___x_2427_; 
v___x_2427_ = 2;
return v___x_2427_;
}
default: 
{
uint8_t v___x_2428_; 
v___x_2428_ = 3;
return v___x_2428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object* v_x_2429_){
_start:
{
uint8_t v_res_2430_; lean_object* v_r_2431_; 
v_res_2430_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_x_2429_);
lean_dec_ref(v_x_2429_);
v_r_2431_ = lean_box(v_res_2430_);
return v_r_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(lean_object* v_j_2432_, lean_object* v_k_2433_){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = l_Lean_Json_getObjValD(v_j_2432_, v_k_2433_);
v___x_2435_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0___boxed(lean_object* v_j_2436_, lean_object* v_k_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_j_2436_, v_k_2437_);
lean_dec_ref(v_k_2437_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage(lean_object* v_h_2441_, lean_object* v_nBytes_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_IO_FS_Stream_readJson(v_h_2441_, v_nBytes_2442_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2564_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2564_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2564_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___y_2450_; lean_object* v___y_2451_; uint8_t v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v_a_2464_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_a_2445_);
v___x_2476_ = l_Lean_Json_getObjVal_x3f(v_a_2445_, v___x_2475_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; 
lean_del_object(v___x_2447_);
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2476_, 1);
v_a_2464_ = v_a_2477_;
goto v___jp_2463_;
}
else
{
lean_object* v_a_2478_; 
v_a_2478_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2476_, 1);
if (lean_obj_tag(v_a_2478_) == 3)
{
lean_object* v_s_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v_s_2479_ = lean_ctor_get(v_a_2478_, 0);
lean_inc_ref(v_s_2479_);
lean_dec_ref_known(v_a_2478_, 1);
v___x_2480_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_2481_ = lean_string_dec_eq(v_s_2479_, v___x_2480_);
lean_dec_ref(v_s_2479_);
if (v___x_2481_ == 0)
{
lean_del_object(v___x_2447_);
goto v___jp_2473_;
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_a_2445_);
v___x_2483_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_2445_, v___x_2482_);
if (lean_obj_tag(v___x_2483_) == 0)
{
goto v___jp_2512_;
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v_a_2539_ = lean_ctor_get(v___x_2483_, 0);
v___x_2540_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2445_);
v___x_2541_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2445_, v___x_2540_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_dec_ref_known(v___x_2541_, 1);
goto v___jp_2512_;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2563_; 
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2483_, 1);
lean_del_object(v___x_2447_);
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2563_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2563_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___y_2547_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2553_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2445_, v___x_2552_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v___x_2554_; 
lean_dec_ref_known(v___x_2553_, 1);
v___x_2554_ = lean_box(0);
v___y_2547_ = v___x_2554_;
goto v___jp_2546_;
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_a_2555_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2553_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2553_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
v___y_2547_ = v___x_2560_;
goto v___jp_2546_;
}
}
}
v___jp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2548_, 0, v_a_2539_);
lean_ctor_set(v___x_2548_, 1, v_a_2542_);
lean_ctor_set(v___x_2548_, 2, v___y_2547_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set_tag(v___x_2544_, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2548_);
v___x_2550_ = v___x_2544_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
v___jp_2484_:
{
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2485_; 
lean_del_object(v___x_2447_);
v_a_2485_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2485_);
lean_dec_ref_known(v___x_2483_, 1);
v_a_2464_ = v_a_2485_;
goto v___jp_2463_;
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v_a_2486_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2483_, 1);
v___x_2487_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
lean_inc(v_a_2445_);
v___x_2488_ = l_Lean_Json_getObjVal_x3f(v_a_2445_, v___x_2487_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; 
lean_dec(v_a_2486_);
lean_del_object(v___x_2447_);
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v_a_2464_ = v_a_2489_;
goto v___jp_2463_;
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v_a_2490_ = lean_ctor_get(v___x_2488_, 0);
lean_inc_n(v_a_2490_, 2);
lean_dec_ref_known(v___x_2488_, 1);
v___x_2491_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_2492_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_2490_, v___x_2491_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; 
lean_dec(v_a_2490_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2447_);
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2492_, 1);
v_a_2464_ = v_a_2493_;
goto v___jp_2463_;
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v_a_2494_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2492_, 1);
v___x_2495_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_2490_);
v___x_2496_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2490_, v___x_2495_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; 
lean_dec(v_a_2494_);
lean_dec(v_a_2490_);
lean_dec(v_a_2486_);
lean_del_object(v___x_2447_);
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2496_, 1);
v_a_2464_ = v_a_2497_;
goto v___jp_2463_;
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec(v_a_2445_);
v_a_2498_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2496_, 1);
v___x_2499_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2500_ = l_Lean_Json_getObjVal_x3f(v_a_2490_, v___x_2499_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v___x_2501_; uint8_t v___x_2502_; 
lean_dec_ref_known(v___x_2500_, 1);
v___x_2501_ = lean_box(0);
v___x_2502_ = lean_unbox(v_a_2494_);
lean_dec(v_a_2494_);
v___y_2450_ = v_a_2486_;
v___y_2451_ = v_a_2498_;
v___y_2452_ = v___x_2502_;
v___y_2453_ = v___x_2501_;
goto v___jp_2449_;
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2511_; 
v_a_2503_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2505_ = v___x_2500_;
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2500_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2511_;
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
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
uint8_t v___x_2509_; 
v___x_2509_ = lean_unbox(v_a_2494_);
lean_dec(v_a_2494_);
v___y_2450_ = v_a_2486_;
v___y_2451_ = v_a_2498_;
v___y_2452_ = v___x_2509_;
v___y_2453_ = v___x_2508_;
goto v___jp_2449_;
}
}
}
}
}
}
}
}
v___jp_2512_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2445_);
v___x_2514_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2445_, v___x_2513_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_dec_ref_known(v___x_2514_, 1);
if (lean_obj_tag(v___x_2483_) == 0)
{
goto v___jp_2484_;
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_a_2515_ = lean_ctor_get(v___x_2483_, 0);
v___x_2516_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_2445_);
v___x_2517_ = l_Lean_Json_getObjVal_x3f(v_a_2445_, v___x_2516_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_dec_ref_known(v___x_2517_, 1);
goto v___jp_2484_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2526_; 
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2483_, 1);
lean_del_object(v___x_2447_);
lean_dec(v_a_2445_);
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2526_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2522_, 0, v_a_2515_);
lean_ctor_set(v___x_2522_, 1, v_a_2518_);
if (v_isShared_2521_ == 0)
{
lean_ctor_set_tag(v___x_2520_, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2522_);
v___x_2524_ = v___x_2520_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec_ref(v___x_2483_);
lean_del_object(v___x_2447_);
v_a_2527_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2528_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2529_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2445_, v___x_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v___x_2530_; 
lean_dec_ref_known(v___x_2529_, 1);
v___x_2530_ = lean_box(0);
v___y_2459_ = v_a_2527_;
v___y_2460_ = v___x_2530_;
goto v___jp_2458_;
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
v_a_2531_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2529_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2529_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
v___y_2459_ = v_a_2527_;
v___y_2460_ = v___x_2536_;
goto v___jp_2458_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2478_);
lean_del_object(v___x_2447_);
goto v___jp_2473_;
}
}
v___jp_2449_:
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2454_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2454_, 0, v___y_2450_);
lean_ctor_set(v___x_2454_, 1, v___y_2451_);
lean_ctor_set(v___x_2454_, 2, v___y_2453_);
lean_ctor_set_uint8(v___x_2454_, sizeof(void*)*3, v___y_2452_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2454_);
v___x_2456_ = v___x_2447_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
v___jp_2458_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___y_2459_);
lean_ctor_set(v___x_2461_, 1, v___y_2460_);
v___x_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
return v___x_2462_;
}
v___jp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2465_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__0));
v___x_2466_ = l_Lean_Json_compress(v_a_2445_);
v___x_2467_ = lean_string_append(v___x_2465_, v___x_2466_);
lean_dec_ref(v___x_2466_);
v___x_2468_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__1));
v___x_2469_ = lean_string_append(v___x_2467_, v___x_2468_);
v___x_2470_ = lean_string_append(v___x_2469_, v_a_2464_);
lean_dec_ref(v_a_2464_);
v___x_2471_ = lean_mk_io_user_error(v___x_2470_);
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
return v___x_2472_;
}
v___jp_2473_:
{
lean_object* v___x_2474_; 
v___x_2474_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_2464_ = v___x_2474_;
goto v___jp_2463_;
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
v_a_2565_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2444_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2444_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage___boxed(lean_object* v_h_2573_, lean_object* v_nBytes_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_IO_FS_Stream_readMessage(v_h_2573_, v_nBytes_2574_);
lean_dec(v_nBytes_2574_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg(lean_object* v_h_2584_, lean_object* v_nBytes_2585_, lean_object* v_expectedMethod_2586_, lean_object* v_inst_2587_){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2590_ = l_Lean_IO_FS_Stream_readMessage(v_h_2584_, v_nBytes_2585_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2776_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2776_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2776_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
if (lean_obj_tag(v_a_2591_) == 0)
{
lean_object* v_id_2595_; lean_object* v_method_2596_; lean_object* v_params_x3f_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2636_; 
v_id_2595_ = lean_ctor_get(v_a_2591_, 0);
v_method_2596_ = lean_ctor_get(v_a_2591_, 1);
v_params_x3f_2597_ = lean_ctor_get(v_a_2591_, 2);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_a_2591_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2599_ = v_a_2591_;
v_isShared_2600_ = v_isSharedCheck_2636_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_params_x3f_2597_);
lean_inc(v_method_2596_);
lean_inc(v_id_2595_);
lean_dec(v_a_2591_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2636_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
uint8_t v___x_2601_; 
v___x_2601_ = lean_string_dec_eq(v_method_2596_, v_expectedMethod_2586_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
lean_del_object(v___x_2599_);
lean_dec(v_params_x3f_2597_);
lean_dec(v_id_2595_);
lean_dec_ref(v_inst_2587_);
v___x_2602_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2603_ = lean_string_append(v___x_2602_, v_expectedMethod_2586_);
lean_dec_ref(v_expectedMethod_2586_);
v___x_2604_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2605_ = lean_string_append(v___x_2603_, v___x_2604_);
v___x_2606_ = lean_string_append(v___x_2605_, v_method_2596_);
lean_dec_ref(v_method_2596_);
v___x_2607_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2608_ = lean_string_append(v___x_2606_, v___x_2607_);
v___x_2609_ = lean_mk_io_user_error(v___x_2608_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 1);
lean_ctor_set(v___x_2593_, 0, v___x_2609_);
v___x_2611_ = v___x_2593_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
else
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_dec_ref(v_method_2596_);
v___x_2613_ = l_Lean_Option_toJson___redArg(v___x_2589_, v_params_x3f_2597_);
lean_inc(v___x_2613_);
v___x_2614_ = lean_apply_1(v_inst_2587_, v___x_2613_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
lean_del_object(v___x_2599_);
lean_dec(v_id_2595_);
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2617_ = l_Lean_Json_compress(v___x_2613_);
v___x_2618_ = lean_string_append(v___x_2616_, v___x_2617_);
lean_dec_ref(v___x_2617_);
v___x_2619_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2620_ = lean_string_append(v___x_2618_, v___x_2619_);
v___x_2621_ = lean_string_append(v___x_2620_, v_expectedMethod_2586_);
lean_dec_ref(v_expectedMethod_2586_);
v___x_2622_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2623_ = lean_string_append(v___x_2621_, v___x_2622_);
v___x_2624_ = lean_string_append(v___x_2623_, v_a_2615_);
lean_dec(v_a_2615_);
v___x_2625_ = lean_mk_io_user_error(v___x_2624_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 1);
lean_ctor_set(v___x_2593_, 0, v___x_2625_);
v___x_2627_ = v___x_2593_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; 
lean_dec(v___x_2613_);
v_a_2629_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2614_, 1);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 2, v_a_2629_);
lean_ctor_set(v___x_2599_, 1, v_expectedMethod_2586_);
v___x_2631_ = v___x_2599_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_id_2595_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_expectedMethod_2586_);
lean_ctor_set(v_reuseFailAlloc_2635_, 2, v_a_2629_);
v___x_2631_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2633_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2631_);
v___x_2633_ = v___x_2593_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___y_2640_; 
lean_dec_ref(v_inst_2587_);
lean_dec_ref(v_expectedMethod_2586_);
v___x_2637_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__6));
v___x_2638_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2591_))
{
case 0:
{
lean_object* v_id_2651_; lean_object* v_method_2652_; lean_object* v_params_x3f_2653_; lean_object* v___x_2654_; lean_object* v___y_2656_; 
v_id_2651_ = lean_ctor_get(v_a_2591_, 0);
lean_inc(v_id_2651_);
v_method_2652_ = lean_ctor_get(v_a_2591_, 1);
lean_inc_ref(v_method_2652_);
v_params_x3f_2653_ = lean_ctor_get(v_a_2591_, 2);
lean_inc(v_params_x3f_2653_);
lean_dec_ref_known(v_a_2591_, 3);
v___x_2654_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2651_) == 0)
{
lean_object* v_s_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
v_s_2667_ = lean_ctor_get(v_id_2651_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_id_2651_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v_id_2651_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_s_2667_);
lean_dec(v_id_2651_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 3);
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_s_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
v___y_2656_ = v___x_2672_;
goto v___jp_2655_;
}
}
}
else
{
lean_object* v_n_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
v_n_2675_ = lean_ctor_get(v_id_2651_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_id_2651_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v_id_2651_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_n_2675_);
lean_dec(v_id_2651_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 2);
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_n_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
v___y_2656_ = v___x_2680_;
goto v___jp_2655_;
}
}
}
v___jp_2655_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2654_);
lean_ctor_set(v___x_2657_, 1, v___y_2656_);
v___x_2658_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2659_, 0, v_method_2652_);
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
v___x_2661_ = lean_box(0);
v___x_2662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2660_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v___x_2663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2657_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2665_ = l_Lean_Json_opt___redArg(v___x_2589_, v___x_2664_, v_params_x3f_2653_);
v___x_2666_ = l_List_appendTR___redArg(v___x_2663_, v___x_2665_);
v___y_2640_ = v___x_2666_;
goto v___jp_2639_;
}
}
case 1:
{
lean_object* v_method_2683_; lean_object* v_params_x3f_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_method_2683_ = lean_ctor_get(v_a_2591_, 0);
lean_inc_ref(v_method_2683_);
v_params_x3f_2684_ = lean_ctor_get(v_a_2591_, 1);
lean_inc(v_params_x3f_2684_);
lean_dec_ref_known(v_a_2591_, 2);
v___x_2685_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2686_, 0, v_method_2683_);
v___x_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2689_ = l_Lean_Json_opt___redArg(v___x_2589_, v___x_2688_, v_params_x3f_2684_);
v___x_2690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2687_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___y_2640_ = v___x_2690_;
goto v___jp_2639_;
}
case 2:
{
lean_object* v_id_2691_; lean_object* v_result_2692_; lean_object* v___x_2693_; lean_object* v___y_2695_; 
v_id_2691_ = lean_ctor_get(v_a_2591_, 0);
lean_inc(v_id_2691_);
v_result_2692_ = lean_ctor_get(v_a_2591_, 1);
lean_inc(v_result_2692_);
lean_dec_ref_known(v_a_2591_, 2);
v___x_2693_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2691_) == 0)
{
lean_object* v_s_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
v_s_2702_ = lean_ctor_get(v_id_2691_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_id_2691_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v_id_2691_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_s_2702_);
lean_dec(v_id_2691_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set_tag(v___x_2704_, 3);
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_s_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
v___y_2695_ = v___x_2707_;
goto v___jp_2694_;
}
}
}
else
{
lean_object* v_n_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
v_n_2710_ = lean_ctor_get(v_id_2691_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_id_2691_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v_id_2691_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_n_2710_);
lean_dec(v_id_2691_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
lean_ctor_set_tag(v___x_2712_, 2);
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_n_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
v___y_2695_ = v___x_2715_;
goto v___jp_2694_;
}
}
}
v___jp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2693_);
lean_ctor_set(v___x_2696_, 1, v___y_2695_);
v___x_2697_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v_result_2692_);
v___x_2699_ = lean_box(0);
v___x_2700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2696_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___y_2640_ = v___x_2701_;
goto v___jp_2639_;
}
}
default: 
{
lean_object* v_id_2718_; uint8_t v_code_2719_; lean_object* v_message_2720_; lean_object* v_data_x3f_2721_; lean_object* v___x_2722_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___x_2742_; lean_object* v___y_2744_; 
v_id_2718_ = lean_ctor_get(v_a_2591_, 0);
lean_inc(v_id_2718_);
v_code_2719_ = lean_ctor_get_uint8(v_a_2591_, sizeof(void*)*3);
v_message_2720_ = lean_ctor_get(v_a_2591_, 1);
lean_inc_ref(v_message_2720_);
v_data_x3f_2721_ = lean_ctor_get(v_a_2591_, 2);
lean_inc(v_data_x3f_2721_);
lean_dec_ref_known(v_a_2591_, 3);
v___x_2722_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2742_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2718_) == 0)
{
lean_object* v_s_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
v_s_2760_ = lean_ctor_get(v_id_2718_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_id_2718_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v_id_2718_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_s_2760_);
lean_dec(v_id_2718_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
lean_ctor_set_tag(v___x_2762_, 3);
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_s_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
v___y_2744_ = v___x_2765_;
goto v___jp_2743_;
}
}
}
else
{
lean_object* v_n_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
v_n_2768_ = lean_ctor_get(v_id_2718_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_id_2718_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v_id_2718_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_n_2768_);
lean_dec(v_id_2718_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 2);
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_n_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
v___y_2744_ = v___x_2773_;
goto v___jp_2743_;
}
}
}
v___jp_2723_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2725_);
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___y_2725_);
lean_ctor_set(v___x_2728_, 1, v___y_2727_);
v___x_2729_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_message_2720_);
v___x_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2729_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = lean_box(0);
v___x_2733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2731_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
v___x_2734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2728_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2736_ = l_Lean_Json_opt___redArg(v___x_2722_, v___x_2735_, v_data_x3f_2721_);
v___x_2737_ = l_List_appendTR___redArg(v___x_2734_, v___x_2736_);
v___x_2738_ = l_Lean_Json_mkObj(v___x_2737_);
lean_dec(v___x_2737_);
lean_inc_ref(v___y_2726_);
v___x_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___y_2726_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
lean_ctor_set(v___x_2740_, 1, v___x_2732_);
v___x_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___y_2724_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___y_2640_ = v___x_2741_;
goto v___jp_2639_;
}
v___jp_2743_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2742_);
lean_ctor_set(v___x_2745_, 1, v___y_2744_);
v___x_2746_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2747_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2719_)
{
case 0:
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2748_;
goto v___jp_2723_;
}
case 1:
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2749_;
goto v___jp_2723_;
}
case 2:
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2750_;
goto v___jp_2723_;
}
case 3:
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2751_;
goto v___jp_2723_;
}
case 4:
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2752_;
goto v___jp_2723_;
}
case 5:
{
lean_object* v___x_2753_; 
v___x_2753_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2753_;
goto v___jp_2723_;
}
case 6:
{
lean_object* v___x_2754_; 
v___x_2754_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2754_;
goto v___jp_2723_;
}
case 7:
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2755_;
goto v___jp_2723_;
}
case 8:
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2756_;
goto v___jp_2723_;
}
case 9:
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2757_;
goto v___jp_2723_;
}
case 10:
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2758_;
goto v___jp_2723_;
}
default: 
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2724_ = v___x_2745_;
v___y_2725_ = v___x_2747_;
v___y_2726_ = v___x_2746_;
v___y_2727_ = v___x_2759_;
goto v___jp_2723_;
}
}
}
}
}
v___jp_2639_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2638_);
lean_ctor_set(v___x_2641_, 1, v___y_2640_);
v___x_2642_ = l_Lean_Json_mkObj(v___x_2641_);
lean_dec_ref_known(v___x_2641_, 2);
v___x_2643_ = l_Lean_Json_compress(v___x_2642_);
v___x_2644_ = lean_string_append(v___x_2637_, v___x_2643_);
lean_dec_ref(v___x_2643_);
v___x_2645_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2646_ = lean_string_append(v___x_2644_, v___x_2645_);
v___x_2647_ = lean_mk_io_user_error(v___x_2646_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set_tag(v___x_2593_, 1);
lean_ctor_set(v___x_2593_, 0, v___x_2647_);
v___x_2649_ = v___x_2593_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec_ref(v_inst_2587_);
lean_dec_ref(v_expectedMethod_2586_);
v_a_2777_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2590_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2590_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* v_h_2785_, lean_object* v_nBytes_2786_, lean_object* v_expectedMethod_2787_, lean_object* v_inst_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2785_, v_nBytes_2786_, v_expectedMethod_2787_, v_inst_2788_);
lean_dec(v_nBytes_2786_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs(lean_object* v_h_2791_, lean_object* v_nBytes_2792_, lean_object* v_expectedMethod_2793_, lean_object* v_00_u03b1_2794_, lean_object* v_inst_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2791_, v_nBytes_2792_, v_expectedMethod_2793_, v_inst_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___boxed(lean_object* v_h_2798_, lean_object* v_nBytes_2799_, lean_object* v_expectedMethod_2800_, lean_object* v_00_u03b1_2801_, lean_object* v_inst_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_IO_FS_Stream_readRequestAs(v_h_2798_, v_nBytes_2799_, v_expectedMethod_2800_, v_00_u03b1_2801_, v_inst_2802_);
lean_dec(v_nBytes_2799_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg(lean_object* v_h_2806_, lean_object* v_nBytes_2807_, lean_object* v_expectedMethod_2808_, lean_object* v_inst_2809_){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2812_ = l_Lean_IO_FS_Stream_readMessage(v_h_2806_, v_nBytes_2807_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2997_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2997_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2997_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
if (lean_obj_tag(v_a_2813_) == 1)
{
lean_object* v_method_2817_; lean_object* v_params_x3f_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2857_; 
v_method_2817_ = lean_ctor_get(v_a_2813_, 0);
v_params_x3f_2818_ = lean_ctor_get(v_a_2813_, 1);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_a_2813_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2820_ = v_a_2813_;
v_isShared_2821_ = v_isSharedCheck_2857_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_params_x3f_2818_);
lean_inc(v_method_2817_);
lean_dec(v_a_2813_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2857_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
uint8_t v___x_2822_; 
v___x_2822_ = lean_string_dec_eq(v_method_2817_, v_expectedMethod_2808_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; 
lean_del_object(v___x_2820_);
lean_dec(v_params_x3f_2818_);
lean_dec_ref(v_inst_2809_);
v___x_2823_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2824_ = lean_string_append(v___x_2823_, v_expectedMethod_2808_);
lean_dec_ref(v_expectedMethod_2808_);
v___x_2825_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2826_ = lean_string_append(v___x_2824_, v___x_2825_);
v___x_2827_ = lean_string_append(v___x_2826_, v_method_2817_);
lean_dec_ref(v_method_2817_);
v___x_2828_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2829_ = lean_string_append(v___x_2827_, v___x_2828_);
v___x_2830_ = lean_mk_io_user_error(v___x_2829_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 1);
lean_ctor_set(v___x_2815_, 0, v___x_2830_);
v___x_2832_ = v___x_2815_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_dec_ref(v_method_2817_);
v___x_2834_ = l_Lean_Option_toJson___redArg(v___x_2811_, v_params_x3f_2818_);
lean_inc(v___x_2834_);
v___x_2835_ = lean_apply_1(v_inst_2809_, v___x_2834_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
lean_del_object(v___x_2820_);
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v___x_2837_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2838_ = l_Lean_Json_compress(v___x_2834_);
v___x_2839_ = lean_string_append(v___x_2837_, v___x_2838_);
lean_dec_ref(v___x_2838_);
v___x_2840_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2841_ = lean_string_append(v___x_2839_, v___x_2840_);
v___x_2842_ = lean_string_append(v___x_2841_, v_expectedMethod_2808_);
lean_dec_ref(v_expectedMethod_2808_);
v___x_2843_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2844_ = lean_string_append(v___x_2842_, v___x_2843_);
v___x_2845_ = lean_string_append(v___x_2844_, v_a_2836_);
lean_dec(v_a_2836_);
v___x_2846_ = lean_mk_io_user_error(v___x_2845_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 1);
lean_ctor_set(v___x_2815_, 0, v___x_2846_);
v___x_2848_ = v___x_2815_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; 
lean_dec(v___x_2834_);
v_a_2850_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2835_, 1);
if (v_isShared_2821_ == 0)
{
lean_ctor_set_tag(v___x_2820_, 0);
lean_ctor_set(v___x_2820_, 1, v_a_2850_);
lean_ctor_set(v___x_2820_, 0, v_expectedMethod_2808_);
v___x_2852_ = v___x_2820_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_expectedMethod_2808_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_a_2850_);
v___x_2852_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2854_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2852_);
v___x_2854_ = v___x_2815_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
}
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___y_2861_; 
lean_dec_ref(v_inst_2809_);
lean_dec_ref(v_expectedMethod_2808_);
v___x_2858_ = ((lean_object*)(l_Lean_IO_FS_Stream_readNotificationAs___redArg___closed__0));
v___x_2859_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2813_))
{
case 0:
{
lean_object* v_id_2872_; lean_object* v_method_2873_; lean_object* v_params_x3f_2874_; lean_object* v___x_2875_; lean_object* v___y_2877_; 
v_id_2872_ = lean_ctor_get(v_a_2813_, 0);
lean_inc(v_id_2872_);
v_method_2873_ = lean_ctor_get(v_a_2813_, 1);
lean_inc_ref(v_method_2873_);
v_params_x3f_2874_ = lean_ctor_get(v_a_2813_, 2);
lean_inc(v_params_x3f_2874_);
lean_dec_ref_known(v_a_2813_, 3);
v___x_2875_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2872_) == 0)
{
lean_object* v_s_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v_s_2888_ = lean_ctor_get(v_id_2872_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_id_2872_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v_id_2872_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_s_2888_);
lean_dec(v_id_2872_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set_tag(v___x_2890_, 3);
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_s_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
v___y_2877_ = v___x_2893_;
goto v___jp_2876_;
}
}
}
else
{
lean_object* v_n_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v_n_2896_ = lean_ctor_get(v_id_2872_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_id_2872_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v_id_2872_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_n_2896_);
lean_dec(v_id_2872_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set_tag(v___x_2898_, 2);
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_n_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
v___y_2877_ = v___x_2901_;
goto v___jp_2876_;
}
}
}
v___jp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2875_);
lean_ctor_set(v___x_2878_, 1, v___y_2877_);
v___x_2879_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2880_, 0, v_method_2873_);
v___x_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_box(0);
v___x_2883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2878_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2886_ = l_Lean_Json_opt___redArg(v___x_2811_, v___x_2885_, v_params_x3f_2874_);
v___x_2887_ = l_List_appendTR___redArg(v___x_2884_, v___x_2886_);
v___y_2861_ = v___x_2887_;
goto v___jp_2860_;
}
}
case 1:
{
lean_object* v_method_2904_; lean_object* v_params_x3f_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v_method_2904_ = lean_ctor_get(v_a_2813_, 0);
lean_inc_ref(v_method_2904_);
v_params_x3f_2905_ = lean_ctor_get(v_a_2813_, 1);
lean_inc(v_params_x3f_2905_);
lean_dec_ref_known(v_a_2813_, 2);
v___x_2906_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_method_2904_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2910_ = l_Lean_Json_opt___redArg(v___x_2811_, v___x_2909_, v_params_x3f_2905_);
v___x_2911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2908_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___y_2861_ = v___x_2911_;
goto v___jp_2860_;
}
case 2:
{
lean_object* v_id_2912_; lean_object* v_result_2913_; lean_object* v___x_2914_; lean_object* v___y_2916_; 
v_id_2912_ = lean_ctor_get(v_a_2813_, 0);
lean_inc(v_id_2912_);
v_result_2913_ = lean_ctor_get(v_a_2813_, 1);
lean_inc(v_result_2913_);
lean_dec_ref_known(v_a_2813_, 2);
v___x_2914_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2912_) == 0)
{
lean_object* v_s_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
v_s_2923_ = lean_ctor_get(v_id_2912_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_id_2912_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v_id_2912_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_s_2923_);
lean_dec(v_id_2912_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set_tag(v___x_2925_, 3);
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_s_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
v___y_2916_ = v___x_2928_;
goto v___jp_2915_;
}
}
}
else
{
lean_object* v_n_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
v_n_2931_ = lean_ctor_get(v_id_2912_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_id_2912_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v_id_2912_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_n_2931_);
lean_dec(v_id_2912_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set_tag(v___x_2933_, 2);
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_n_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
v___y_2916_ = v___x_2936_;
goto v___jp_2915_;
}
}
}
v___jp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2914_);
lean_ctor_set(v___x_2917_, 1, v___y_2916_);
v___x_2918_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
lean_ctor_set(v___x_2919_, 1, v_result_2913_);
v___x_2920_ = lean_box(0);
v___x_2921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2919_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2917_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___y_2861_ = v___x_2922_;
goto v___jp_2860_;
}
}
default: 
{
lean_object* v_id_2939_; uint8_t v_code_2940_; lean_object* v_message_2941_; lean_object* v_data_x3f_2942_; lean_object* v___x_2943_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___x_2963_; lean_object* v___y_2965_; 
v_id_2939_ = lean_ctor_get(v_a_2813_, 0);
lean_inc(v_id_2939_);
v_code_2940_ = lean_ctor_get_uint8(v_a_2813_, sizeof(void*)*3);
v_message_2941_ = lean_ctor_get(v_a_2813_, 1);
lean_inc_ref(v_message_2941_);
v_data_x3f_2942_ = lean_ctor_get(v_a_2813_, 2);
lean_inc(v_data_x3f_2942_);
lean_dec_ref_known(v_a_2813_, 3);
v___x_2943_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2963_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2939_) == 0)
{
lean_object* v_s_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
v_s_2981_ = lean_ctor_get(v_id_2939_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_id_2939_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v_id_2939_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_s_2981_);
lean_dec(v_id_2939_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set_tag(v___x_2983_, 3);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_s_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
v___y_2965_ = v___x_2986_;
goto v___jp_2964_;
}
}
}
else
{
lean_object* v_n_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
v_n_2989_ = lean_ctor_get(v_id_2939_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_id_2939_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v_id_2939_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_n_2989_);
lean_dec(v_id_2939_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set_tag(v___x_2991_, 2);
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_n_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
v___y_2965_ = v___x_2994_;
goto v___jp_2964_;
}
}
}
v___jp_2944_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2945_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___y_2945_);
lean_ctor_set(v___x_2949_, 1, v___y_2948_);
v___x_2950_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2951_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2951_, 0, v_message_2941_);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2950_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2949_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2957_ = l_Lean_Json_opt___redArg(v___x_2943_, v___x_2956_, v_data_x3f_2942_);
v___x_2958_ = l_List_appendTR___redArg(v___x_2955_, v___x_2957_);
v___x_2959_ = l_Lean_Json_mkObj(v___x_2958_);
lean_dec(v___x_2958_);
lean_inc_ref(v___y_2946_);
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___y_2946_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
lean_ctor_set(v___x_2961_, 1, v___x_2953_);
v___x_2962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___y_2947_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___y_2861_ = v___x_2962_;
goto v___jp_2860_;
}
v___jp_2964_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2963_);
lean_ctor_set(v___x_2966_, 1, v___y_2965_);
v___x_2967_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2968_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2940_)
{
case 0:
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2969_;
goto v___jp_2944_;
}
case 1:
{
lean_object* v___x_2970_; 
v___x_2970_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2970_;
goto v___jp_2944_;
}
case 2:
{
lean_object* v___x_2971_; 
v___x_2971_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2971_;
goto v___jp_2944_;
}
case 3:
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2972_;
goto v___jp_2944_;
}
case 4:
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2973_;
goto v___jp_2944_;
}
case 5:
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2974_;
goto v___jp_2944_;
}
case 6:
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2975_;
goto v___jp_2944_;
}
case 7:
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2976_;
goto v___jp_2944_;
}
case 8:
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2977_;
goto v___jp_2944_;
}
case 9:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2978_;
goto v___jp_2944_;
}
case 10:
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2979_;
goto v___jp_2944_;
}
default: 
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2945_ = v___x_2968_;
v___y_2946_ = v___x_2967_;
v___y_2947_ = v___x_2966_;
v___y_2948_ = v___x_2980_;
goto v___jp_2944_;
}
}
}
}
}
v___jp_2860_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2859_);
lean_ctor_set(v___x_2862_, 1, v___y_2861_);
v___x_2863_ = l_Lean_Json_mkObj(v___x_2862_);
lean_dec_ref_known(v___x_2862_, 2);
v___x_2864_ = l_Lean_Json_compress(v___x_2863_);
v___x_2865_ = lean_string_append(v___x_2858_, v___x_2864_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2867_ = lean_string_append(v___x_2865_, v___x_2866_);
v___x_2868_ = lean_mk_io_user_error(v___x_2867_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 1);
lean_ctor_set(v___x_2815_, 0, v___x_2868_);
v___x_2870_ = v___x_2815_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
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
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref(v_inst_2809_);
lean_dec_ref(v_expectedMethod_2808_);
v_a_2998_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2812_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2812_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* v_h_3006_, lean_object* v_nBytes_3007_, lean_object* v_expectedMethod_3008_, lean_object* v_inst_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3006_, v_nBytes_3007_, v_expectedMethod_3008_, v_inst_3009_);
lean_dec(v_nBytes_3007_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs(lean_object* v_h_3012_, lean_object* v_nBytes_3013_, lean_object* v_expectedMethod_3014_, lean_object* v_00_u03b1_3015_, lean_object* v_inst_3016_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3012_, v_nBytes_3013_, v_expectedMethod_3014_, v_inst_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___boxed(lean_object* v_h_3019_, lean_object* v_nBytes_3020_, lean_object* v_expectedMethod_3021_, lean_object* v_00_u03b1_3022_, lean_object* v_inst_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_IO_FS_Stream_readNotificationAs(v_h_3019_, v_nBytes_3020_, v_expectedMethod_3021_, v_00_u03b1_3022_, v_inst_3023_);
lean_dec(v_nBytes_3020_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg(lean_object* v_h_3030_, lean_object* v_nBytes_3031_, lean_object* v_expectedID_3032_, lean_object* v_inst_3033_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_IO_FS_Stream_readMessage(v_h_3030_, v_nBytes_3031_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3239_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3239_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3239_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___y_3041_; lean_object* v___y_3042_; 
if (lean_obj_tag(v_a_3036_) == 2)
{
lean_object* v_id_3048_; lean_object* v_result_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3100_; 
v_id_3048_ = lean_ctor_get(v_a_3036_, 0);
v_result_3049_ = lean_ctor_get(v_a_3036_, 1);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_a_3036_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3051_ = v_a_3036_;
v_isShared_3052_ = v_isSharedCheck_3100_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_result_3049_);
lean_inc(v_id_3048_);
lean_dec(v_a_3036_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3100_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
uint8_t v___x_3053_; 
v___x_3053_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3048_, v_expectedID_3032_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v___y_3056_; 
lean_del_object(v___x_3051_);
lean_dec(v_result_3049_);
lean_dec_ref(v_inst_3033_);
v___x_3054_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__0));
switch(lean_obj_tag(v_expectedID_3032_))
{
case 0:
{
lean_object* v_s_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_s_3066_ = lean_ctor_get(v_expectedID_3032_, 0);
lean_inc_ref(v_s_3066_);
lean_dec_ref_known(v_expectedID_3032_, 1);
v___x_3067_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3068_ = lean_string_append(v___x_3067_, v_s_3066_);
lean_dec_ref(v_s_3066_);
v___x_3069_ = lean_string_append(v___x_3068_, v___x_3067_);
v___y_3056_ = v___x_3069_;
goto v___jp_3055_;
}
case 1:
{
lean_object* v_n_3070_; lean_object* v___x_3071_; 
v_n_3070_ = lean_ctor_get(v_expectedID_3032_, 0);
lean_inc_ref(v_n_3070_);
lean_dec_ref_known(v_expectedID_3032_, 1);
v___x_3071_ = l_Lean_JsonNumber_toString(v_n_3070_);
v___y_3056_ = v___x_3071_;
goto v___jp_3055_;
}
default: 
{
lean_object* v___x_3072_; 
v___x_3072_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___y_3056_ = v___x_3072_;
goto v___jp_3055_;
}
}
v___jp_3055_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = lean_string_append(v___x_3054_, v___y_3056_);
lean_dec_ref(v___y_3056_);
v___x_3058_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__1));
v___x_3059_ = lean_string_append(v___x_3057_, v___x_3058_);
if (lean_obj_tag(v_id_3048_) == 0)
{
lean_object* v_s_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_s_3060_ = lean_ctor_get(v_id_3048_, 0);
lean_inc_ref(v_s_3060_);
lean_dec_ref_known(v_id_3048_, 1);
v___x_3061_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3062_ = lean_string_append(v___x_3061_, v_s_3060_);
lean_dec_ref(v_s_3060_);
v___x_3063_ = lean_string_append(v___x_3062_, v___x_3061_);
v___y_3041_ = v___x_3059_;
v___y_3042_ = v___x_3063_;
goto v___jp_3040_;
}
else
{
lean_object* v_n_3064_; lean_object* v___x_3065_; 
v_n_3064_ = lean_ctor_get(v_id_3048_, 0);
lean_inc_ref(v_n_3064_);
lean_dec_ref_known(v_id_3048_, 1);
v___x_3065_ = l_Lean_JsonNumber_toString(v_n_3064_);
v___y_3041_ = v___x_3059_;
v___y_3042_ = v___x_3065_;
goto v___jp_3040_;
}
}
}
else
{
lean_object* v___x_3073_; 
lean_dec(v_id_3048_);
lean_del_object(v___x_3038_);
lean_inc(v_result_3049_);
v___x_3073_ = lean_apply_1(v_inst_3033_, v_result_3049_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3088_; 
lean_del_object(v___x_3051_);
lean_dec(v_expectedID_3032_);
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3076_ = v___x_3073_;
v_isShared_3077_ = v_isSharedCheck_3088_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3073_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3088_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3078_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__2));
v___x_3079_ = l_Lean_Json_compress(v_result_3049_);
v___x_3080_ = lean_string_append(v___x_3078_, v___x_3079_);
lean_dec_ref(v___x_3079_);
v___x_3081_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_3082_ = lean_string_append(v___x_3080_, v___x_3081_);
v___x_3083_ = lean_string_append(v___x_3082_, v_a_3074_);
lean_dec(v_a_3074_);
v___x_3084_ = lean_mk_io_user_error(v___x_3083_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set_tag(v___x_3076_, 1);
lean_ctor_set(v___x_3076_, 0, v___x_3084_);
v___x_3086_ = v___x_3076_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_result_3049_);
v_a_3089_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3091_ = v___x_3073_;
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3073_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3099_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set_tag(v___x_3051_, 0);
lean_ctor_set(v___x_3051_, 1, v_a_3089_);
lean_ctor_set(v___x_3051_, 0, v_expectedID_3032_);
v___x_3094_ = v___x_3051_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_expectedID_3032_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3096_; 
if (v_isShared_3092_ == 0)
{
lean_ctor_set_tag(v___x_3091_, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3094_);
v___x_3096_ = v___x_3091_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___y_3105_; 
lean_del_object(v___x_3038_);
lean_dec_ref(v_inst_3033_);
lean_dec(v_expectedID_3032_);
v___x_3101_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__3));
v___x_3102_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_3103_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_3036_))
{
case 0:
{
lean_object* v_id_3114_; lean_object* v_method_3115_; lean_object* v_params_x3f_3116_; lean_object* v___x_3117_; lean_object* v___y_3119_; 
v_id_3114_ = lean_ctor_get(v_a_3036_, 0);
lean_inc(v_id_3114_);
v_method_3115_ = lean_ctor_get(v_a_3036_, 1);
lean_inc_ref(v_method_3115_);
v_params_x3f_3116_ = lean_ctor_get(v_a_3036_, 2);
lean_inc(v_params_x3f_3116_);
lean_dec_ref_known(v_a_3036_, 3);
v___x_3117_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3114_) == 0)
{
lean_object* v_s_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
v_s_3130_ = lean_ctor_get(v_id_3114_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_id_3114_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v_id_3114_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_s_3130_);
lean_dec(v_id_3114_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
lean_ctor_set_tag(v___x_3132_, 3);
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_s_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
v___y_3119_ = v___x_3135_;
goto v___jp_3118_;
}
}
}
else
{
lean_object* v_n_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
v_n_3138_ = lean_ctor_get(v_id_3114_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_id_3114_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v_id_3114_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_n_3138_);
lean_dec(v_id_3114_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set_tag(v___x_3140_, 2);
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_n_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
v___y_3119_ = v___x_3143_;
goto v___jp_3118_;
}
}
}
v___jp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3117_);
lean_ctor_set(v___x_3120_, 1, v___y_3119_);
v___x_3121_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_method_3115_);
v___x_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = lean_box(0);
v___x_3125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3123_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3120_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3128_ = l_Lean_Json_opt___redArg(v___x_3102_, v___x_3127_, v_params_x3f_3116_);
v___x_3129_ = l_List_appendTR___redArg(v___x_3126_, v___x_3128_);
v___y_3105_ = v___x_3129_;
goto v___jp_3104_;
}
}
case 1:
{
lean_object* v_method_3146_; lean_object* v_params_x3f_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v_method_3146_ = lean_ctor_get(v_a_3036_, 0);
lean_inc_ref(v_method_3146_);
v_params_x3f_3147_ = lean_ctor_get(v_a_3036_, 1);
lean_inc(v_params_x3f_3147_);
lean_dec_ref_known(v_a_3036_, 2);
v___x_3148_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3149_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3149_, 0, v_method_3146_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3148_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3152_ = l_Lean_Json_opt___redArg(v___x_3102_, v___x_3151_, v_params_x3f_3147_);
v___x_3153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3150_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___y_3105_ = v___x_3153_;
goto v___jp_3104_;
}
case 2:
{
lean_object* v_id_3154_; lean_object* v_result_3155_; lean_object* v___x_3156_; lean_object* v___y_3158_; 
v_id_3154_ = lean_ctor_get(v_a_3036_, 0);
lean_inc(v_id_3154_);
v_result_3155_ = lean_ctor_get(v_a_3036_, 1);
lean_inc(v_result_3155_);
lean_dec_ref_known(v_a_3036_, 2);
v___x_3156_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3154_) == 0)
{
lean_object* v_s_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
v_s_3165_ = lean_ctor_get(v_id_3154_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_id_3154_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v_id_3154_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_s_3165_);
lean_dec(v_id_3154_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
lean_ctor_set_tag(v___x_3167_, 3);
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_s_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
v___y_3158_ = v___x_3170_;
goto v___jp_3157_;
}
}
}
else
{
lean_object* v_n_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
v_n_3173_ = lean_ctor_get(v_id_3154_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_id_3154_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v_id_3154_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_n_3173_);
lean_dec(v_id_3154_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
lean_ctor_set_tag(v___x_3175_, 2);
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_n_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
v___y_3158_ = v___x_3178_;
goto v___jp_3157_;
}
}
}
v___jp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3156_);
lean_ctor_set(v___x_3159_, 1, v___y_3158_);
v___x_3160_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v_result_3155_);
v___x_3162_ = lean_box(0);
v___x_3163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3159_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___y_3105_ = v___x_3164_;
goto v___jp_3104_;
}
}
default: 
{
lean_object* v_id_3181_; uint8_t v_code_3182_; lean_object* v_message_3183_; lean_object* v_data_x3f_3184_; lean_object* v___x_3185_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___x_3205_; lean_object* v___y_3207_; 
v_id_3181_ = lean_ctor_get(v_a_3036_, 0);
lean_inc(v_id_3181_);
v_code_3182_ = lean_ctor_get_uint8(v_a_3036_, sizeof(void*)*3);
v_message_3183_ = lean_ctor_get(v_a_3036_, 1);
lean_inc_ref(v_message_3183_);
v_data_x3f_3184_ = lean_ctor_get(v_a_3036_, 2);
lean_inc(v_data_x3f_3184_);
lean_dec_ref_known(v_a_3036_, 3);
v___x_3185_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_3205_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3181_) == 0)
{
lean_object* v_s_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
v_s_3223_ = lean_ctor_get(v_id_3181_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v_id_3181_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v_id_3181_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_s_3223_);
lean_dec(v_id_3181_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
lean_ctor_set_tag(v___x_3225_, 3);
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_s_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
v___y_3207_ = v___x_3228_;
goto v___jp_3206_;
}
}
}
else
{
lean_object* v_n_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
v_n_3231_ = lean_ctor_get(v_id_3181_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_id_3181_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v_id_3181_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_n_3231_);
lean_dec(v_id_3181_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 2);
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_n_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
v___y_3207_ = v___x_3236_;
goto v___jp_3206_;
}
}
}
v___jp_3186_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_inc(v___y_3190_);
lean_inc_ref(v___y_3189_);
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___y_3189_);
lean_ctor_set(v___x_3191_, 1, v___y_3190_);
v___x_3192_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3193_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3193_, 0, v_message_3183_);
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3192_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___x_3195_ = lean_box(0);
v___x_3196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3194_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
v___x_3197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3191_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3199_ = l_Lean_Json_opt___redArg(v___x_3185_, v___x_3198_, v_data_x3f_3184_);
v___x_3200_ = l_List_appendTR___redArg(v___x_3197_, v___x_3199_);
v___x_3201_ = l_Lean_Json_mkObj(v___x_3200_);
lean_dec(v___x_3200_);
lean_inc_ref(v___y_3188_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___y_3188_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
v___x_3203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_ctor_set(v___x_3203_, 1, v___x_3195_);
v___x_3204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___y_3187_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___y_3105_ = v___x_3204_;
goto v___jp_3104_;
}
v___jp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3205_);
lean_ctor_set(v___x_3208_, 1, v___y_3207_);
v___x_3209_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3210_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3182_)
{
case 0:
{
lean_object* v___x_3211_; 
v___x_3211_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3211_;
goto v___jp_3186_;
}
case 1:
{
lean_object* v___x_3212_; 
v___x_3212_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3212_;
goto v___jp_3186_;
}
case 2:
{
lean_object* v___x_3213_; 
v___x_3213_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3213_;
goto v___jp_3186_;
}
case 3:
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3214_;
goto v___jp_3186_;
}
case 4:
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3215_;
goto v___jp_3186_;
}
case 5:
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3216_;
goto v___jp_3186_;
}
case 6:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3217_;
goto v___jp_3186_;
}
case 7:
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3218_;
goto v___jp_3186_;
}
case 8:
{
lean_object* v___x_3219_; 
v___x_3219_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3219_;
goto v___jp_3186_;
}
case 9:
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3220_;
goto v___jp_3186_;
}
case 10:
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3221_;
goto v___jp_3186_;
}
default: 
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3187_ = v___x_3208_;
v___y_3188_ = v___x_3209_;
v___y_3189_ = v___x_3210_;
v___y_3190_ = v___x_3222_;
goto v___jp_3186_;
}
}
}
}
}
v___jp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3103_);
lean_ctor_set(v___x_3106_, 1, v___y_3105_);
v___x_3107_ = l_Lean_Json_mkObj(v___x_3106_);
lean_dec_ref_known(v___x_3106_, 2);
v___x_3108_ = l_Lean_Json_compress(v___x_3107_);
v___x_3109_ = lean_string_append(v___x_3101_, v___x_3108_);
lean_dec_ref(v___x_3108_);
v___x_3110_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_3111_ = lean_string_append(v___x_3109_, v___x_3110_);
v___x_3112_ = lean_mk_io_user_error(v___x_3111_);
v___x_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
return v___x_3113_;
}
}
v___jp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3043_ = lean_string_append(v___y_3041_, v___y_3042_);
lean_dec_ref(v___y_3042_);
v___x_3044_ = lean_mk_io_user_error(v___x_3043_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set_tag(v___x_3038_, 1);
lean_ctor_set(v___x_3038_, 0, v___x_3044_);
v___x_3046_ = v___x_3038_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref(v_inst_3033_);
lean_dec(v_expectedID_3032_);
v_a_3240_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3035_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3035_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* v_h_3248_, lean_object* v_nBytes_3249_, lean_object* v_expectedID_3250_, lean_object* v_inst_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3248_, v_nBytes_3249_, v_expectedID_3250_, v_inst_3251_);
lean_dec(v_nBytes_3249_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs(lean_object* v_h_3254_, lean_object* v_nBytes_3255_, lean_object* v_expectedID_3256_, lean_object* v_00_u03b1_3257_, lean_object* v_inst_3258_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3254_, v_nBytes_3255_, v_expectedID_3256_, v_inst_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___boxed(lean_object* v_h_3261_, lean_object* v_nBytes_3262_, lean_object* v_expectedID_3263_, lean_object* v_00_u03b1_3264_, lean_object* v_inst_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Lean_IO_FS_Stream_readResponseAs(v_h_3261_, v_nBytes_3262_, v_expectedID_3263_, v_00_u03b1_3264_, v_inst_3265_);
lean_dec(v_nBytes_3262_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(lean_object* v_k_3268_, lean_object* v_x_3269_){
_start:
{
if (lean_obj_tag(v_x_3269_) == 0)
{
lean_object* v___x_3270_; 
lean_dec_ref(v_k_3268_);
v___x_3270_ = lean_box(0);
return v___x_3270_;
}
else
{
lean_object* v_val_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v_val_3271_ = lean_ctor_get(v_x_3269_, 0);
lean_inc(v_val_3271_);
lean_dec_ref_known(v_x_3269_, 1);
v___x_3272_ = l_Lean_Json_Structured_toJson(v_val_3271_);
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v_k_3268_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3273_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
return v___x_3275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(lean_object* v_k_3276_, lean_object* v_x_3277_){
_start:
{
if (lean_obj_tag(v_x_3277_) == 0)
{
lean_object* v___x_3278_; 
lean_dec_ref(v_k_3276_);
v___x_3278_ = lean_box(0);
return v___x_3278_;
}
else
{
lean_object* v_val_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_val_3279_ = lean_ctor_get(v_x_3277_, 0);
lean_inc(v_val_3279_);
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_k_3276_);
lean_ctor_set(v___x_3280_, 1, v_val_3279_);
v___x_3281_ = lean_box(0);
v___x_3282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
return v___x_3282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* v_k_3283_, lean_object* v_x_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v_k_3283_, v_x_3284_);
lean_dec(v_x_3284_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage(lean_object* v_h_3286_, lean_object* v_m_3287_){
_start:
{
lean_object* v___x_3289_; lean_object* v___y_3291_; 
v___x_3289_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_3287_))
{
case 0:
{
lean_object* v_id_3295_; lean_object* v_method_3296_; lean_object* v_params_x3f_3297_; lean_object* v___x_3298_; lean_object* v___y_3300_; 
v_id_3295_ = lean_ctor_get(v_m_3287_, 0);
lean_inc(v_id_3295_);
v_method_3296_ = lean_ctor_get(v_m_3287_, 1);
lean_inc_ref(v_method_3296_);
v_params_x3f_3297_ = lean_ctor_get(v_m_3287_, 2);
lean_inc(v_params_x3f_3297_);
lean_dec_ref_known(v_m_3287_, 3);
v___x_3298_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3295_))
{
case 0:
{
lean_object* v_s_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
v_s_3311_ = lean_ctor_get(v_id_3295_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_id_3295_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v_id_3295_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_s_3311_);
lean_dec(v_id_3295_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
lean_ctor_set_tag(v___x_3313_, 3);
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_s_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
v___y_3300_ = v___x_3316_;
goto v___jp_3299_;
}
}
}
case 1:
{
lean_object* v_n_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
v_n_3319_ = lean_ctor_get(v_id_3295_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_id_3295_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v_id_3295_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_n_3319_);
lean_dec(v_id_3295_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set_tag(v___x_3321_, 2);
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_n_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
v___y_3300_ = v___x_3324_;
goto v___jp_3299_;
}
}
}
default: 
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_box(0);
v___y_3300_ = v___x_3327_;
goto v___jp_3299_;
}
}
v___jp_3299_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3298_);
lean_ctor_set(v___x_3301_, 1, v___y_3300_);
v___x_3302_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3303_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3303_, 0, v_method_3296_);
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3301_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3309_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3308_, v_params_x3f_3297_);
v___x_3310_ = l_List_appendTR___redArg(v___x_3307_, v___x_3309_);
v___y_3291_ = v___x_3310_;
goto v___jp_3290_;
}
}
case 1:
{
lean_object* v_method_3328_; lean_object* v_params_x3f_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3341_; 
v_method_3328_ = lean_ctor_get(v_m_3287_, 0);
v_params_x3f_3329_ = lean_ctor_get(v_m_3287_, 1);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_m_3287_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3331_ = v_m_3287_;
v_isShared_3332_ = v_isSharedCheck_3341_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_params_x3f_3329_);
lean_inc(v_method_3328_);
lean_dec(v_m_3287_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3341_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3333_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3334_, 0, v_method_3328_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set_tag(v___x_3331_, 0);
lean_ctor_set(v___x_3331_, 1, v___x_3334_);
lean_ctor_set(v___x_3331_, 0, v___x_3333_);
v___x_3336_ = v___x_3331_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3333_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3338_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3337_, v_params_x3f_3329_);
v___x_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3336_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___y_3291_ = v___x_3339_;
goto v___jp_3290_;
}
}
}
case 2:
{
lean_object* v_id_3342_; lean_object* v_result_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3375_; 
v_id_3342_ = lean_ctor_get(v_m_3287_, 0);
v_result_3343_ = lean_ctor_get(v_m_3287_, 1);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_m_3287_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3345_ = v_m_3287_;
v_isShared_3346_ = v_isSharedCheck_3375_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_result_3343_);
lean_inc(v_id_3342_);
lean_dec(v_m_3287_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3375_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v___y_3349_; 
v___x_3347_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3342_))
{
case 0:
{
lean_object* v_s_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
v_s_3358_ = lean_ctor_get(v_id_3342_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v_id_3342_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v_id_3342_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_s_3358_);
lean_dec(v_id_3342_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 3);
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_s_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
v___y_3349_ = v___x_3363_;
goto v___jp_3348_;
}
}
}
case 1:
{
lean_object* v_n_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
v_n_3366_ = lean_ctor_get(v_id_3342_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v_id_3342_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v_id_3342_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_n_3366_);
lean_dec(v_id_3342_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set_tag(v___x_3368_, 2);
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_n_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
v___y_3349_ = v___x_3371_;
goto v___jp_3348_;
}
}
}
default: 
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_box(0);
v___y_3349_ = v___x_3374_;
goto v___jp_3348_;
}
}
v___jp_3348_:
{
lean_object* v___x_3351_; 
if (v_isShared_3346_ == 0)
{
lean_ctor_set_tag(v___x_3345_, 0);
lean_ctor_set(v___x_3345_, 1, v___y_3349_);
lean_ctor_set(v___x_3345_, 0, v___x_3347_);
v___x_3351_ = v___x_3345_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v___y_3349_);
v___x_3351_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3352_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
lean_ctor_set(v___x_3353_, 1, v_result_3343_);
v___x_3354_ = lean_box(0);
v___x_3355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3351_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___y_3291_ = v___x_3356_;
goto v___jp_3290_;
}
}
}
}
default: 
{
lean_object* v_id_3376_; uint8_t v_code_3377_; lean_object* v_message_3378_; lean_object* v_data_x3f_3379_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___x_3399_; lean_object* v___y_3401_; 
v_id_3376_ = lean_ctor_get(v_m_3287_, 0);
lean_inc(v_id_3376_);
v_code_3377_ = lean_ctor_get_uint8(v_m_3287_, sizeof(void*)*3);
v_message_3378_ = lean_ctor_get(v_m_3287_, 1);
lean_inc_ref(v_message_3378_);
v_data_x3f_3379_ = lean_ctor_get(v_m_3287_, 2);
lean_inc(v_data_x3f_3379_);
lean_dec_ref_known(v_m_3287_, 3);
v___x_3399_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3376_))
{
case 0:
{
lean_object* v_s_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
v_s_3417_ = lean_ctor_get(v_id_3376_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_id_3376_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v_id_3376_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_s_3417_);
lean_dec(v_id_3376_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set_tag(v___x_3419_, 3);
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_s_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
v___y_3401_ = v___x_3422_;
goto v___jp_3400_;
}
}
}
case 1:
{
lean_object* v_n_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
v_n_3425_ = lean_ctor_get(v_id_3376_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_id_3376_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v_id_3376_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_n_3425_);
lean_dec(v_id_3376_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set_tag(v___x_3427_, 2);
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_n_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
v___y_3401_ = v___x_3430_;
goto v___jp_3400_;
}
}
}
default: 
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_box(0);
v___y_3401_ = v___x_3433_;
goto v___jp_3400_;
}
}
v___jp_3380_:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_inc(v___y_3384_);
lean_inc_ref(v___y_3383_);
v___x_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___y_3383_);
lean_ctor_set(v___x_3385_, 1, v___y_3384_);
v___x_3386_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3387_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3387_, 0, v_message_3378_);
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = lean_box(0);
v___x_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3388_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3385_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3393_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v___x_3392_, v_data_x3f_3379_);
lean_dec(v_data_x3f_3379_);
v___x_3394_ = l_List_appendTR___redArg(v___x_3391_, v___x_3393_);
v___x_3395_ = l_Lean_Json_mkObj(v___x_3394_);
lean_dec(v___x_3394_);
lean_inc_ref(v___y_3381_);
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___y_3381_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v___x_3397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
lean_ctor_set(v___x_3397_, 1, v___x_3389_);
v___x_3398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___y_3382_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___y_3291_ = v___x_3398_;
goto v___jp_3290_;
}
v___jp_3400_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3399_);
lean_ctor_set(v___x_3402_, 1, v___y_3401_);
v___x_3403_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3404_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3377_)
{
case 0:
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3405_;
goto v___jp_3380_;
}
case 1:
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3406_;
goto v___jp_3380_;
}
case 2:
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3407_;
goto v___jp_3380_;
}
case 3:
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3408_;
goto v___jp_3380_;
}
case 4:
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3409_;
goto v___jp_3380_;
}
case 5:
{
lean_object* v___x_3410_; 
v___x_3410_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3410_;
goto v___jp_3380_;
}
case 6:
{
lean_object* v___x_3411_; 
v___x_3411_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3411_;
goto v___jp_3380_;
}
case 7:
{
lean_object* v___x_3412_; 
v___x_3412_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3412_;
goto v___jp_3380_;
}
case 8:
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3413_;
goto v___jp_3380_;
}
case 9:
{
lean_object* v___x_3414_; 
v___x_3414_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3414_;
goto v___jp_3380_;
}
case 10:
{
lean_object* v___x_3415_; 
v___x_3415_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3415_;
goto v___jp_3380_;
}
default: 
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3381_ = v___x_3403_;
v___y_3382_ = v___x_3402_;
v___y_3383_ = v___x_3404_;
v___y_3384_ = v___x_3416_;
goto v___jp_3380_;
}
}
}
}
}
v___jp_3290_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3289_);
lean_ctor_set(v___x_3292_, 1, v___y_3291_);
v___x_3293_ = l_Lean_Json_mkObj(v___x_3292_);
lean_dec_ref_known(v___x_3292_, 2);
v___x_3294_ = l_Lean_IO_FS_Stream_writeJson(v_h_3286_, v___x_3293_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage___boxed(lean_object* v_h_3434_, lean_object* v_m_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3434_, v_m_3435_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg(lean_object* v_inst_3438_, lean_object* v_h_3439_, lean_object* v_r_3440_){
_start:
{
lean_object* v_id_3442_; lean_object* v_method_3443_; lean_object* v_param_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3464_; 
v_id_3442_ = lean_ctor_get(v_r_3440_, 0);
v_method_3443_ = lean_ctor_get(v_r_3440_, 1);
v_param_3444_ = lean_ctor_get(v_r_3440_, 2);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_r_3440_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3446_ = v_r_3440_;
v_isShared_3447_ = v_isSharedCheck_3464_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_param_3444_);
lean_inc(v_method_3443_);
lean_inc(v_id_3442_);
lean_dec(v_r_3440_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3464_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___y_3449_; lean_object* v___x_3454_; 
v___x_3454_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3438_, v_param_3444_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v___x_3455_; 
lean_dec_ref_known(v___x_3454_, 1);
v___x_3455_ = lean_box(0);
v___y_3449_ = v___x_3455_;
goto v___jp_3448_;
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
v_a_3456_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3454_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3454_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
v___y_3449_ = v___x_3461_;
goto v___jp_3448_;
}
}
}
v___jp_3448_:
{
lean_object* v___x_3451_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 2, v___y_3449_);
v___x_3451_ = v___x_3446_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_id_3442_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_method_3443_);
lean_ctor_set(v_reuseFailAlloc_3453_, 2, v___y_3449_);
v___x_3451_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3439_, v___x_3451_);
return v___x_3452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg___boxed(lean_object* v_inst_3465_, lean_object* v_h_3466_, lean_object* v_r_3467_, lean_object* v_a_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3465_, v_h_3466_, v_r_3467_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest(lean_object* v_00_u03b1_3470_, lean_object* v_inst_3471_, lean_object* v_h_3472_, lean_object* v_r_3473_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3471_, v_h_3472_, v_r_3473_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___boxed(lean_object* v_00_u03b1_3476_, lean_object* v_inst_3477_, lean_object* v_h_3478_, lean_object* v_r_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_IO_FS_Stream_writeRequest(v_00_u03b1_3476_, v_inst_3477_, v_h_3478_, v_r_3479_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg(lean_object* v_inst_3482_, lean_object* v_h_3483_, lean_object* v_n_3484_){
_start:
{
lean_object* v_method_3486_; lean_object* v_param_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3507_; 
v_method_3486_ = lean_ctor_get(v_n_3484_, 0);
v_param_3487_ = lean_ctor_get(v_n_3484_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_n_3484_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3489_ = v_n_3484_;
v_isShared_3490_ = v_isSharedCheck_3507_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_param_3487_);
lean_inc(v_method_3486_);
lean_dec(v_n_3484_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3507_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___y_3492_; lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3482_, v_param_3487_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v___x_3498_; 
lean_dec_ref_known(v___x_3497_, 1);
v___x_3498_ = lean_box(0);
v___y_3492_ = v___x_3498_;
goto v___jp_3491_;
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
v_a_3499_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3497_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3497_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
v___y_3492_ = v___x_3504_;
goto v___jp_3491_;
}
}
}
v___jp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3490_ == 0)
{
lean_ctor_set_tag(v___x_3489_, 1);
lean_ctor_set(v___x_3489_, 1, v___y_3492_);
v___x_3494_ = v___x_3489_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_method_3486_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v___y_3492_);
v___x_3494_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3483_, v___x_3494_);
return v___x_3495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg___boxed(lean_object* v_inst_3508_, lean_object* v_h_3509_, lean_object* v_n_3510_, lean_object* v_a_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3508_, v_h_3509_, v_n_3510_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification(lean_object* v_00_u03b1_3513_, lean_object* v_inst_3514_, lean_object* v_h_3515_, lean_object* v_n_3516_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3514_, v_h_3515_, v_n_3516_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___boxed(lean_object* v_00_u03b1_3519_, lean_object* v_inst_3520_, lean_object* v_h_3521_, lean_object* v_n_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lean_IO_FS_Stream_writeNotification(v_00_u03b1_3519_, v_inst_3520_, v_h_3521_, v_n_3522_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg(lean_object* v_inst_3525_, lean_object* v_h_3526_, lean_object* v_r_3527_){
_start:
{
lean_object* v_id_3529_; lean_object* v_result_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3539_; 
v_id_3529_ = lean_ctor_get(v_r_3527_, 0);
v_result_3530_ = lean_ctor_get(v_r_3527_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_r_3527_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3532_ = v_r_3527_;
v_isShared_3533_ = v_isSharedCheck_3539_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_result_3530_);
lean_inc(v_id_3529_);
lean_dec(v_r_3527_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3539_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3534_ = lean_apply_1(v_inst_3525_, v_result_3530_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set_tag(v___x_3532_, 2);
lean_ctor_set(v___x_3532_, 1, v___x_3534_);
v___x_3536_ = v___x_3532_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_id_3529_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3526_, v___x_3536_);
return v___x_3537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg___boxed(lean_object* v_inst_3540_, lean_object* v_h_3541_, lean_object* v_r_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3540_, v_h_3541_, v_r_3542_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse(lean_object* v_00_u03b1_3545_, lean_object* v_inst_3546_, lean_object* v_h_3547_, lean_object* v_r_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3546_, v_h_3547_, v_r_3548_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___boxed(lean_object* v_00_u03b1_3551_, lean_object* v_inst_3552_, lean_object* v_h_3553_, lean_object* v_r_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_IO_FS_Stream_writeResponse(v_00_u03b1_3551_, v_inst_3552_, v_h_3553_, v_r_3554_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError(lean_object* v_h_3557_, lean_object* v_e_3558_){
_start:
{
lean_object* v_id_3560_; uint8_t v_code_3561_; lean_object* v_message_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3571_; 
v_id_3560_ = lean_ctor_get(v_e_3558_, 0);
v_code_3561_ = lean_ctor_get_uint8(v_e_3558_, sizeof(void*)*3);
v_message_3562_ = lean_ctor_get(v_e_3558_, 1);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_e_3558_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; 
v_unused_3572_ = lean_ctor_get(v_e_3558_, 2);
lean_dec(v_unused_3572_);
v___x_3564_ = v_e_3558_;
v_isShared_3565_ = v_isSharedCheck_3571_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_message_3562_);
lean_inc(v_id_3560_);
lean_dec(v_e_3558_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3571_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
v___x_3566_ = lean_box(0);
if (v_isShared_3565_ == 0)
{
lean_ctor_set_tag(v___x_3564_, 3);
lean_ctor_set(v___x_3564_, 2, v___x_3566_);
v___x_3568_ = v___x_3564_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_id_3560_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_message_3562_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v___x_3566_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*3, v_code_3561_);
v___x_3568_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
lean_object* v___x_3569_; 
v___x_3569_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3557_, v___x_3568_);
return v___x_3569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError___boxed(lean_object* v_h_3573_, lean_object* v_e_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_IO_FS_Stream_writeResponseError(v_h_3573_, v_e_3574_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* v_inst_3577_, lean_object* v_h_3578_, lean_object* v_e_3579_){
_start:
{
lean_object* v_id_3581_; uint8_t v_code_3582_; lean_object* v_message_3583_; lean_object* v_data_x3f_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3604_; 
v_id_3581_ = lean_ctor_get(v_e_3579_, 0);
v_code_3582_ = lean_ctor_get_uint8(v_e_3579_, sizeof(void*)*3);
v_message_3583_ = lean_ctor_get(v_e_3579_, 1);
v_data_x3f_3584_ = lean_ctor_get(v_e_3579_, 2);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_e_3579_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3586_ = v_e_3579_;
v_isShared_3587_ = v_isSharedCheck_3604_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_data_x3f_3584_);
lean_inc(v_message_3583_);
lean_inc(v_id_3581_);
lean_dec(v_e_3579_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3604_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___y_3589_; 
if (lean_obj_tag(v_data_x3f_3584_) == 0)
{
lean_object* v___x_3594_; 
lean_dec_ref(v_inst_3577_);
v___x_3594_ = lean_box(0);
v___y_3589_ = v___x_3594_;
goto v___jp_3588_;
}
else
{
lean_object* v_val_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3603_; 
v_val_3595_ = lean_ctor_get(v_data_x3f_3584_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v_data_x3f_3584_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3597_ = v_data_x3f_3584_;
v_isShared_3598_ = v_isSharedCheck_3603_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_val_3595_);
lean_dec(v_data_x3f_3584_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3603_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3599_ = lean_apply_1(v_inst_3577_, v_val_3595_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v___x_3599_);
v___x_3601_ = v___x_3597_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
v___y_3589_ = v___x_3601_;
goto v___jp_3588_;
}
}
}
v___jp_3588_:
{
lean_object* v___x_3591_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 3);
lean_ctor_set(v___x_3586_, 2, v___y_3589_);
v___x_3591_ = v___x_3586_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_id_3581_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_message_3583_);
lean_ctor_set(v_reuseFailAlloc_3593_, 2, v___y_3589_);
lean_ctor_set_uint8(v_reuseFailAlloc_3593_, sizeof(void*)*3, v_code_3582_);
v___x_3591_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3592_; 
v___x_3592_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3578_, v___x_3591_);
return v___x_3592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object* v_inst_3605_, lean_object* v_h_3606_, lean_object* v_e_3607_, lean_object* v_a_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3605_, v_h_3606_, v_e_3607_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData(lean_object* v_00_u03b1_3610_, lean_object* v_inst_3611_, lean_object* v_h_3612_, lean_object* v_e_3613_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3611_, v_h_3612_, v_e_3613_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object* v_00_u03b1_3616_, lean_object* v_inst_3617_, lean_object* v_h_3618_, lean_object* v_e_3619_, lean_object* v_a_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData(v_00_u03b1_3616_, v_inst_3617_, v_h_3618_, v_e_3619_);
return v_res_3621_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Stream(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_JsonRpc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Json_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_JsonRpc_instInhabitedErrorCode_default = _init_l_Lean_JsonRpc_instInhabitedErrorCode_default();
l_Lean_JsonRpc_instInhabitedErrorCode = _init_l_Lean_JsonRpc_instInhabitedErrorCode();
l_Lean_JsonRpc_RequestID_ltProp = _init_l_Lean_JsonRpc_RequestID_ltProp();
lean_mark_persistent(l_Lean_JsonRpc_RequestID_ltProp);
l_Lean_JsonRpc_instLTRequestID = _init_l_Lean_JsonRpc_instLTRequestID();
lean_mark_persistent(l_Lean_JsonRpc_instLTRequestID);
l_Lean_JsonRpc_instInhabitedMessageDirection_default = _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default();
l_Lean_JsonRpc_instInhabitedMessageDirection = _init_l_Lean_JsonRpc_instInhabitedMessageDirection();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_JsonRpc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Data_JsonRpc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_JsonRpc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_JsonRpc(builtin);
}
#ifdef __cplusplus
}
#endif
