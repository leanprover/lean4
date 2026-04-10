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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_Parser_num(lean_object*);
lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
uint8_t l_Lean_instDecidableEqJsonNumber_decEq(lean_object*, lean_object*);
lean_object* l_Option_toJson___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readJson(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t l_Lean_instHashableJsonNumber_hash(lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
lean_object* l_IO_FS_Stream_writeJson(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object*);
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
static const lean_ctor_object l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__1_value),((lean_object*)&l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0 = (const lean_object*)&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object*);
static lean_once_cell_t l_Lean_JsonRpc_instInhabitedResponseError___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_JsonRpc_instInhabitedResponseError___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "JSON '"};
static const lean_object* l_IO_FS_Stream_readMessage___closed__0 = (const lean_object*)&l_IO_FS_Stream_readMessage___closed__0_value;
static const lean_string_object l_IO_FS_Stream_readMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "' did not have the format of a JSON-RPC message.\n"};
static const lean_object* l_IO_FS_Stream_readMessage___closed__1 = (const lean_object*)&l_IO_FS_Stream_readMessage___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readRequestAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Expected method '"};
static const lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__0 = (const lean_object*)&l_IO_FS_Stream_readRequestAs___redArg___closed__0_value;
static const lean_string_object l_IO_FS_Stream_readRequestAs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "', got method '"};
static const lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__1 = (const lean_object*)&l_IO_FS_Stream_readRequestAs___redArg___closed__1_value;
static const lean_string_object l_IO_FS_Stream_readRequestAs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__2 = (const lean_object*)&l_IO_FS_Stream_readRequestAs___redArg___closed__2_value;
static const lean_string_object l_IO_FS_Stream_readRequestAs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unexpected param '"};
static const lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__3 = (const lean_object*)&l_IO_FS_Stream_readRequestAs___redArg___closed__3_value;
static const lean_string_object l_IO_FS_Stream_readRequestAs___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "' for method '"};
static const lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__4 = (const lean_object*)&l_IO_FS_Stream_readRequestAs___redArg___closed__4_value;
static const lean_string_object l_IO_FS_Stream_readRequestAs___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "'\n"};
static const lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__5 = (const lean_object*)&l_IO_FS_Stream_readRequestAs___redArg___closed__5_value;
static const lean_string_object l_IO_FS_Stream_readRequestAs___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Expected JSON-RPC request, got: '"};
static const lean_object* l_IO_FS_Stream_readRequestAs___redArg___closed__6 = (const lean_object*)&l_IO_FS_Stream_readRequestAs___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readNotificationAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Expected JSON-RPC notification, got: '"};
static const lean_object* l_IO_FS_Stream_readNotificationAs___redArg___closed__0 = (const lean_object*)&l_IO_FS_Stream_readNotificationAs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readResponseAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Expected id "};
static const lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__0 = (const lean_object*)&l_IO_FS_Stream_readResponseAs___redArg___closed__0_value;
static const lean_string_object l_IO_FS_Stream_readResponseAs___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", got id "};
static const lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__1 = (const lean_object*)&l_IO_FS_Stream_readResponseAs___redArg___closed__1_value;
static const lean_string_object l_IO_FS_Stream_readResponseAs___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unexpected result '"};
static const lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__2 = (const lean_object*)&l_IO_FS_Stream_readResponseAs___redArg___closed__2_value;
static const lean_string_object l_IO_FS_Stream_readResponseAs___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Expected JSON-RPC response, got: '"};
static const lean_object* l_IO_FS_Stream_readResponseAs___redArg___closed__3 = (const lean_object*)&l_IO_FS_Stream_readResponseAs___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_JsonRpc_RequestID_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 2)
{
return v_k_8_;
}
else
{
lean_object* v_s_9_; lean_object* v___x_10_; 
v_s_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc_ref(v_s_9_);
lean_dec(v_t_7_);
v___x_10_ = lean_apply_1(v_k_8_, v_s_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_JsonRpc_RequestID_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_str_elim___redArg(lean_object* v_t_23_, lean_object* v_str_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_23_, v_str_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_str_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_str_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_27_, v_str_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim___redArg(lean_object* v_t_31_, lean_object* v_num_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_31_, v_num_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_num_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_num_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_35_, v_num_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim___redArg(lean_object* v_t_39_, lean_object* v_null_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_39_, v_null_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_null_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_null_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_JsonRpc_RequestID_ctorElim___redArg(v_t_43_, v_null_45_);
return v___x_46_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequestID_beq(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
switch(lean_obj_tag(v_x_52_))
{
case 0:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_object* v_s_54_; lean_object* v_s_55_; uint8_t v___x_56_; 
v_s_54_ = lean_ctor_get(v_x_52_, 0);
v_s_55_ = lean_ctor_get(v_x_53_, 0);
v___x_56_ = lean_string_dec_eq(v_s_54_, v_s_55_);
return v___x_56_;
}
else
{
uint8_t v___x_57_; 
v___x_57_ = 0;
return v___x_57_;
}
}
case 1:
{
if (lean_obj_tag(v_x_53_) == 1)
{
lean_object* v_n_58_; lean_object* v_n_59_; uint8_t v___x_60_; 
v_n_58_ = lean_ctor_get(v_x_52_, 0);
v_n_59_ = lean_ctor_get(v_x_53_, 0);
v___x_60_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_58_, v_n_59_);
return v___x_60_;
}
else
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
default: 
{
if (lean_obj_tag(v_x_53_) == 2)
{
uint8_t v___x_62_; 
v___x_62_ = 1;
return v___x_62_;
}
else
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequestID_beq___boxed(lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_x_64_, v_x_65_);
lean_dec(v_x_65_);
lean_dec(v_x_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint64_t l_Lean_JsonRpc_instHashableRequestID_hash(lean_object* v_x_70_){
_start:
{
switch(lean_obj_tag(v_x_70_))
{
case 0:
{
lean_object* v_s_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; 
v_s_71_ = lean_ctor_get(v_x_70_, 0);
v___x_72_ = 0ULL;
v___x_73_ = lean_string_hash(v_s_71_);
v___x_74_ = lean_uint64_mix_hash(v___x_72_, v___x_73_);
return v___x_74_;
}
case 1:
{
lean_object* v_n_75_; uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v___x_78_; 
v_n_75_ = lean_ctor_get(v_x_70_, 0);
v___x_76_ = 1ULL;
v___x_77_ = l_Lean_instHashableJsonNumber_hash(v_n_75_);
v___x_78_ = lean_uint64_mix_hash(v___x_76_, v___x_77_);
return v___x_78_;
}
default: 
{
uint64_t v___x_79_; 
v___x_79_ = 2ULL;
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instHashableRequestID_hash___boxed(lean_object* v_x_80_){
_start:
{
uint64_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Lean_JsonRpc_instHashableRequestID_hash(v_x_80_);
lean_dec(v_x_80_);
v_r_82_ = lean_box_uint64(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instOrdRequestID_ord(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
switch(lean_obj_tag(v_x_85_))
{
case 0:
{
switch(lean_obj_tag(v_x_86_))
{
case 0:
{
lean_object* v_s_87_; lean_object* v_s_88_; uint8_t v___x_89_; 
v_s_87_ = lean_ctor_get(v_x_85_, 0);
lean_inc_ref(v_s_87_);
lean_dec_ref(v_x_85_);
v_s_88_ = lean_ctor_get(v_x_86_, 0);
lean_inc_ref(v_s_88_);
lean_dec_ref(v_x_86_);
v___x_89_ = lean_string_dec_lt(v_s_87_, v_s_88_);
if (v___x_89_ == 0)
{
uint8_t v___x_90_; 
v___x_90_ = lean_string_dec_eq(v_s_87_, v_s_88_);
lean_dec_ref(v_s_88_);
lean_dec_ref(v_s_87_);
if (v___x_90_ == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 2;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 1;
return v___x_92_;
}
}
else
{
uint8_t v___x_93_; 
lean_dec_ref(v_s_88_);
lean_dec_ref(v_s_87_);
v___x_93_ = 0;
return v___x_93_;
}
}
case 1:
{
uint8_t v___x_94_; 
lean_dec_ref(v_x_86_);
lean_dec_ref(v_x_85_);
v___x_94_ = 0;
return v___x_94_;
}
default: 
{
uint8_t v___x_95_; 
lean_dec_ref(v_x_85_);
lean_dec(v_x_86_);
v___x_95_ = 0;
return v___x_95_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_86_))
{
case 0:
{
uint8_t v___x_96_; 
lean_dec_ref(v_x_86_);
lean_dec_ref(v_x_85_);
v___x_96_ = 2;
return v___x_96_;
}
case 1:
{
lean_object* v_n_97_; lean_object* v_n_98_; uint8_t v___x_99_; 
v_n_97_ = lean_ctor_get(v_x_85_, 0);
lean_inc_ref_n(v_n_97_, 2);
lean_dec_ref(v_x_85_);
v_n_98_ = lean_ctor_get(v_x_86_, 0);
lean_inc_ref_n(v_n_98_, 2);
lean_dec_ref(v_x_86_);
v___x_99_ = l_Lean_JsonNumber_lt(v_n_97_, v_n_98_);
if (v___x_99_ == 0)
{
uint8_t v___x_100_; 
v___x_100_ = l_Lean_JsonNumber_lt(v_n_98_, v_n_97_);
if (v___x_100_ == 0)
{
uint8_t v___x_101_; 
v___x_101_ = 1;
return v___x_101_;
}
else
{
uint8_t v___x_102_; 
v___x_102_ = 2;
return v___x_102_;
}
}
else
{
uint8_t v___x_103_; 
lean_dec_ref(v_n_98_);
lean_dec_ref(v_n_97_);
v___x_103_ = 0;
return v___x_103_;
}
}
default: 
{
uint8_t v___x_104_; 
lean_dec_ref(v_x_85_);
lean_dec(v_x_86_);
v___x_104_ = 0;
return v___x_104_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_86_) == 2)
{
uint8_t v___x_105_; 
v___x_105_ = 1;
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
lean_dec(v_x_86_);
v___x_106_ = 2;
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID_ord___boxed(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Lean_JsonRpc_instOrdRequestID_ord(v_x_107_, v_x_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOfNatRequestID(lean_object* v_n_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = l_Lean_JsonNumber_fromNat(v_n_113_);
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0(lean_object* v_x_118_){
_start:
{
switch(lean_obj_tag(v_x_118_))
{
case 0:
{
lean_object* v_s_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_s_119_ = lean_ctor_get(v_x_118_, 0);
lean_inc_ref(v_s_119_);
lean_dec_ref(v_x_118_);
v___x_120_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_121_ = lean_string_append(v___x_120_, v_s_119_);
lean_dec_ref(v_s_119_);
v___x_122_ = lean_string_append(v___x_121_, v___x_120_);
return v___x_122_;
}
case 1:
{
lean_object* v_n_123_; lean_object* v___x_124_; 
v_n_123_ = lean_ctor_get(v_x_118_, 0);
lean_inc_ref(v_n_123_);
lean_dec_ref(v_x_118_);
v___x_124_ = l_Lean_JsonNumber_toString(v_n_123_);
return v___x_124_;
}
default: 
{
lean_object* v___x_125_; 
v___x_125_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx(uint8_t v_x_128_){
_start:
{
switch(v_x_128_)
{
case 0:
{
lean_object* v___x_129_; 
v___x_129_ = lean_unsigned_to_nat(0u);
return v___x_129_;
}
case 1:
{
lean_object* v___x_130_; 
v___x_130_ = lean_unsigned_to_nat(1u);
return v___x_130_;
}
case 2:
{
lean_object* v___x_131_; 
v___x_131_ = lean_unsigned_to_nat(2u);
return v___x_131_;
}
case 3:
{
lean_object* v___x_132_; 
v___x_132_ = lean_unsigned_to_nat(3u);
return v___x_132_;
}
case 4:
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(4u);
return v___x_133_;
}
case 5:
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(5u);
return v___x_134_;
}
case 6:
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(6u);
return v___x_135_;
}
case 7:
{
lean_object* v___x_136_; 
v___x_136_ = lean_unsigned_to_nat(7u);
return v___x_136_;
}
case 8:
{
lean_object* v___x_137_; 
v___x_137_ = lean_unsigned_to_nat(8u);
return v___x_137_;
}
case 9:
{
lean_object* v___x_138_; 
v___x_138_ = lean_unsigned_to_nat(9u);
return v___x_138_;
}
case 10:
{
lean_object* v___x_139_; 
v___x_139_ = lean_unsigned_to_nat(10u);
return v___x_139_;
}
default: 
{
lean_object* v___x_140_; 
v___x_140_ = lean_unsigned_to_nat(11u);
return v___x_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___boxed(lean_object* v_x_141_){
_start:
{
uint8_t v_x_boxed_142_; lean_object* v_res_143_; 
v_x_boxed_142_ = lean_unbox(v_x_141_);
v_res_143_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_boxed_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx(uint8_t v_x_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(lean_object* v_x_146_){
_start:
{
uint8_t v_x_4__boxed_147_; lean_object* v_res_148_; 
v_x_4__boxed_147_ = lean_unbox(v_x_146_);
v_res_148_ = l_Lean_JsonRpc_ErrorCode_toCtorIdx(v_x_4__boxed_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(lean_object* v_k_149_){
_start:
{
lean_inc(v_k_149_);
return v_k_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg___boxed(lean_object* v_k_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(v_k_150_);
lean_dec(v_k_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim(lean_object* v_motive_152_, lean_object* v_ctorIdx_153_, uint8_t v_t_154_, lean_object* v_h_155_, lean_object* v_k_156_){
_start:
{
lean_inc(v_k_156_);
return v_k_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___boxed(lean_object* v_motive_157_, lean_object* v_ctorIdx_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_k_161_){
_start:
{
uint8_t v_t_boxed_162_; lean_object* v_res_163_; 
v_t_boxed_162_ = lean_unbox(v_t_159_);
v_res_163_ = l_Lean_JsonRpc_ErrorCode_ctorElim(v_motive_157_, v_ctorIdx_158_, v_t_boxed_162_, v_h_160_, v_k_161_);
lean_dec(v_k_161_);
lean_dec(v_ctorIdx_158_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(lean_object* v_parseError_164_){
_start:
{
lean_inc(v_parseError_164_);
return v_parseError_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg___boxed(lean_object* v_parseError_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(v_parseError_165_);
lean_dec(v_parseError_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_object* v_motive_167_, uint8_t v_t_168_, lean_object* v_h_169_, lean_object* v_parseError_170_){
_start:
{
lean_inc(v_parseError_170_);
return v_parseError_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___boxed(lean_object* v_motive_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_parseError_174_){
_start:
{
uint8_t v_t_boxed_175_; lean_object* v_res_176_; 
v_t_boxed_175_ = lean_unbox(v_t_172_);
v_res_176_ = l_Lean_JsonRpc_ErrorCode_parseError_elim(v_motive_171_, v_t_boxed_175_, v_h_173_, v_parseError_174_);
lean_dec(v_parseError_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(lean_object* v_invalidRequest_177_){
_start:
{
lean_inc(v_invalidRequest_177_);
return v_invalidRequest_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg___boxed(lean_object* v_invalidRequest_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(v_invalidRequest_178_);
lean_dec(v_invalidRequest_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_object* v_motive_180_, uint8_t v_t_181_, lean_object* v_h_182_, lean_object* v_invalidRequest_183_){
_start:
{
lean_inc(v_invalidRequest_183_);
return v_invalidRequest_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___boxed(lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_invalidRequest_187_){
_start:
{
uint8_t v_t_boxed_188_; lean_object* v_res_189_; 
v_t_boxed_188_ = lean_unbox(v_t_185_);
v_res_189_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(v_motive_184_, v_t_boxed_188_, v_h_186_, v_invalidRequest_187_);
lean_dec(v_invalidRequest_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(lean_object* v_methodNotFound_190_){
_start:
{
lean_inc(v_methodNotFound_190_);
return v_methodNotFound_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg___boxed(lean_object* v_methodNotFound_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(v_methodNotFound_191_);
lean_dec(v_methodNotFound_191_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(lean_object* v_motive_193_, uint8_t v_t_194_, lean_object* v_h_195_, lean_object* v_methodNotFound_196_){
_start:
{
lean_inc(v_methodNotFound_196_);
return v_methodNotFound_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___boxed(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_methodNotFound_200_){
_start:
{
uint8_t v_t_boxed_201_; lean_object* v_res_202_; 
v_t_boxed_201_ = lean_unbox(v_t_198_);
v_res_202_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(v_motive_197_, v_t_boxed_201_, v_h_199_, v_methodNotFound_200_);
lean_dec(v_methodNotFound_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(lean_object* v_invalidParams_203_){
_start:
{
lean_inc(v_invalidParams_203_);
return v_invalidParams_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg___boxed(lean_object* v_invalidParams_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(v_invalidParams_204_);
lean_dec(v_invalidParams_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_object* v_motive_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_invalidParams_209_){
_start:
{
lean_inc(v_invalidParams_209_);
return v_invalidParams_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___boxed(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_invalidParams_213_){
_start:
{
uint8_t v_t_boxed_214_; lean_object* v_res_215_; 
v_t_boxed_214_ = lean_unbox(v_t_211_);
v_res_215_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim(v_motive_210_, v_t_boxed_214_, v_h_212_, v_invalidParams_213_);
lean_dec(v_invalidParams_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(lean_object* v_internalError_216_){
_start:
{
lean_inc(v_internalError_216_);
return v_internalError_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg___boxed(lean_object* v_internalError_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(v_internalError_217_);
lean_dec(v_internalError_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_object* v_motive_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_internalError_222_){
_start:
{
lean_inc(v_internalError_222_);
return v_internalError_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___boxed(lean_object* v_motive_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_internalError_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Lean_JsonRpc_ErrorCode_internalError_elim(v_motive_223_, v_t_boxed_227_, v_h_225_, v_internalError_226_);
lean_dec(v_internalError_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(lean_object* v_serverNotInitialized_229_){
_start:
{
lean_inc(v_serverNotInitialized_229_);
return v_serverNotInitialized_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg___boxed(lean_object* v_serverNotInitialized_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(v_serverNotInitialized_230_);
lean_dec(v_serverNotInitialized_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_object* v_motive_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_serverNotInitialized_235_){
_start:
{
lean_inc(v_serverNotInitialized_235_);
return v_serverNotInitialized_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___boxed(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_serverNotInitialized_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(v_motive_236_, v_t_boxed_240_, v_h_238_, v_serverNotInitialized_239_);
lean_dec(v_serverNotInitialized_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(lean_object* v_unknownErrorCode_242_){
_start:
{
lean_inc(v_unknownErrorCode_242_);
return v_unknownErrorCode_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg___boxed(lean_object* v_unknownErrorCode_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(v_unknownErrorCode_243_);
lean_dec(v_unknownErrorCode_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_object* v_motive_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_unknownErrorCode_248_){
_start:
{
lean_inc(v_unknownErrorCode_248_);
return v_unknownErrorCode_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___boxed(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_unknownErrorCode_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(v_motive_249_, v_t_boxed_253_, v_h_251_, v_unknownErrorCode_252_);
lean_dec(v_unknownErrorCode_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(lean_object* v_contentModified_255_){
_start:
{
lean_inc(v_contentModified_255_);
return v_contentModified_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg___boxed(lean_object* v_contentModified_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(v_contentModified_256_);
lean_dec(v_contentModified_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_contentModified_261_){
_start:
{
lean_inc(v_contentModified_261_);
return v_contentModified_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_contentModified_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_contentModified_265_);
lean_dec(v_contentModified_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(lean_object* v_requestCancelled_268_){
_start:
{
lean_inc(v_requestCancelled_268_);
return v_requestCancelled_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg___boxed(lean_object* v_requestCancelled_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(v_requestCancelled_269_);
lean_dec(v_requestCancelled_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_object* v_motive_271_, uint8_t v_t_272_, lean_object* v_h_273_, lean_object* v_requestCancelled_274_){
_start:
{
lean_inc(v_requestCancelled_274_);
return v_requestCancelled_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___boxed(lean_object* v_motive_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_requestCancelled_278_){
_start:
{
uint8_t v_t_boxed_279_; lean_object* v_res_280_; 
v_t_boxed_279_ = lean_unbox(v_t_276_);
v_res_280_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(v_motive_275_, v_t_boxed_279_, v_h_277_, v_requestCancelled_278_);
lean_dec(v_requestCancelled_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(lean_object* v_rpcNeedsReconnect_281_){
_start:
{
lean_inc(v_rpcNeedsReconnect_281_);
return v_rpcNeedsReconnect_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg___boxed(lean_object* v_rpcNeedsReconnect_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(v_rpcNeedsReconnect_282_);
lean_dec(v_rpcNeedsReconnect_282_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(lean_object* v_motive_284_, uint8_t v_t_285_, lean_object* v_h_286_, lean_object* v_rpcNeedsReconnect_287_){
_start:
{
lean_inc(v_rpcNeedsReconnect_287_);
return v_rpcNeedsReconnect_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___boxed(lean_object* v_motive_288_, lean_object* v_t_289_, lean_object* v_h_290_, lean_object* v_rpcNeedsReconnect_291_){
_start:
{
uint8_t v_t_boxed_292_; lean_object* v_res_293_; 
v_t_boxed_292_ = lean_unbox(v_t_289_);
v_res_293_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(v_motive_288_, v_t_boxed_292_, v_h_290_, v_rpcNeedsReconnect_291_);
lean_dec(v_rpcNeedsReconnect_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(lean_object* v_workerExited_294_){
_start:
{
lean_inc(v_workerExited_294_);
return v_workerExited_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg___boxed(lean_object* v_workerExited_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(v_workerExited_295_);
lean_dec(v_workerExited_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim(lean_object* v_motive_297_, uint8_t v_t_298_, lean_object* v_h_299_, lean_object* v_workerExited_300_){
_start:
{
lean_inc(v_workerExited_300_);
return v_workerExited_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___boxed(lean_object* v_motive_301_, lean_object* v_t_302_, lean_object* v_h_303_, lean_object* v_workerExited_304_){
_start:
{
uint8_t v_t_boxed_305_; lean_object* v_res_306_; 
v_t_boxed_305_ = lean_unbox(v_t_302_);
v_res_306_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim(v_motive_301_, v_t_boxed_305_, v_h_303_, v_workerExited_304_);
lean_dec(v_workerExited_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(lean_object* v_workerCrashed_307_){
_start:
{
lean_inc(v_workerCrashed_307_);
return v_workerCrashed_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg___boxed(lean_object* v_workerCrashed_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(v_workerCrashed_308_);
lean_dec(v_workerCrashed_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_object* v_motive_310_, uint8_t v_t_311_, lean_object* v_h_312_, lean_object* v_workerCrashed_313_){
_start:
{
lean_inc(v_workerCrashed_313_);
return v_workerCrashed_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___boxed(lean_object* v_motive_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_workerCrashed_317_){
_start:
{
uint8_t v_t_boxed_318_; lean_object* v_res_319_; 
v_t_boxed_318_ = lean_unbox(v_t_315_);
v_res_319_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(v_motive_314_, v_t_boxed_318_, v_h_316_, v_workerCrashed_317_);
lean_dec(v_workerCrashed_317_);
return v_res_319_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode_default(void){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = 0;
return v___x_320_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode(void){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = 0;
return v___x_321_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqErrorCode_beq(uint8_t v_x_322_, uint8_t v_y_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_324_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_322_);
v___x_325_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_y_323_);
v___x_326_ = lean_nat_dec_eq(v___x_324_, v___x_325_);
lean_dec(v___x_325_);
lean_dec(v___x_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode_beq___boxed(lean_object* v_x_327_, lean_object* v_y_328_){
_start:
{
uint8_t v_x_17__boxed_329_; uint8_t v_y_18__boxed_330_; uint8_t v_res_331_; lean_object* v_r_332_; 
v_x_17__boxed_329_ = lean_unbox(v_x_327_);
v_y_18__boxed_330_ = lean_unbox(v_y_328_);
v_res_331_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_x_17__boxed_329_, v_y_18__boxed_330_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(32700u);
v___x_339_ = lean_nat_to_int(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2);
v___x_341_ = lean_int_neg(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(32600u);
v___x_343_ = lean_nat_to_int(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4);
v___x_345_ = lean_int_neg(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(32601u);
v___x_347_ = lean_nat_to_int(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6);
v___x_349_ = lean_int_neg(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(32602u);
v___x_351_ = lean_nat_to_int(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8);
v___x_353_ = lean_int_neg(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(32603u);
v___x_355_ = lean_nat_to_int(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10);
v___x_357_ = lean_int_neg(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(32002u);
v___x_359_ = lean_nat_to_int(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12);
v___x_361_ = lean_int_neg(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_unsigned_to_nat(32001u);
v___x_363_ = lean_nat_to_int(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14);
v___x_365_ = lean_int_neg(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(32801u);
v___x_367_ = lean_nat_to_int(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16);
v___x_369_ = lean_int_neg(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_unsigned_to_nat(32800u);
v___x_371_ = lean_nat_to_int(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18);
v___x_373_ = lean_int_neg(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_unsigned_to_nat(32900u);
v___x_375_ = lean_nat_to_int(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20);
v___x_377_ = lean_int_neg(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_unsigned_to_nat(32901u);
v___x_379_ = lean_nat_to_int(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22);
v___x_381_ = lean_int_neg(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(32902u);
v___x_383_ = lean_nat_to_int(v___x_382_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24);
v___x_385_ = lean_int_neg(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_422_) == 2)
{
lean_object* v_n_425_; lean_object* v_mantissa_426_; lean_object* v_exponent_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_n_425_ = lean_ctor_get(v_x_422_, 0);
v_mantissa_426_ = lean_ctor_get(v_n_425_, 0);
v_exponent_427_ = lean_ctor_get(v_n_425_, 1);
v___x_428_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_429_ = lean_int_dec_eq(v_mantissa_426_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_431_ = lean_int_dec_eq(v_mantissa_426_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_433_ = lean_int_dec_eq(v_mantissa_426_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_435_ = lean_int_dec_eq(v_mantissa_426_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_437_ = lean_int_dec_eq(v_mantissa_426_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_439_ = lean_int_dec_eq(v_mantissa_426_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_441_ = lean_int_dec_eq(v_mantissa_426_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_443_ = lean_int_dec_eq(v_mantissa_426_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_445_ = lean_int_dec_eq(v_mantissa_426_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_447_ = lean_int_dec_eq(v_mantissa_426_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_449_ = lean_int_dec_eq(v_mantissa_426_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_451_ = lean_int_dec_eq(v_mantissa_426_, v___x_450_);
if (v___x_451_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_nat_dec_eq(v_exponent_427_, v___x_452_);
if (v___x_453_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_454_; 
v___x_454_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_454_;
}
}
}
else
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_nat_dec_eq(v_exponent_427_, v___x_455_);
if (v___x_456_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_457_;
}
}
}
else
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_nat_dec_eq(v_exponent_427_, v___x_458_);
if (v___x_459_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_460_;
}
}
}
else
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_nat_dec_eq(v_exponent_427_, v___x_461_);
if (v___x_462_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_463_; 
v___x_463_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_463_;
}
}
}
else
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_nat_dec_eq(v_exponent_427_, v___x_464_);
if (v___x_465_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_466_; 
v___x_466_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_466_;
}
}
}
else
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_nat_dec_eq(v_exponent_427_, v___x_467_);
if (v___x_468_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_469_; 
v___x_469_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_469_;
}
}
}
else
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_nat_dec_eq(v_exponent_427_, v___x_470_);
if (v___x_471_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_472_;
}
}
}
else
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_nat_dec_eq(v_exponent_427_, v___x_473_);
if (v___x_474_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_475_;
}
}
}
else
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_nat_dec_eq(v_exponent_427_, v___x_476_);
if (v___x_477_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_478_;
}
}
}
else
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = lean_nat_dec_eq(v_exponent_427_, v___x_479_);
if (v___x_480_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_481_;
}
}
}
else
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_nat_dec_eq(v_exponent_427_, v___x_482_);
if (v___x_483_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_484_; 
v___x_484_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_484_;
}
}
}
else
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_nat_dec_eq(v_exponent_427_, v___x_485_);
if (v___x_486_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_487_; 
v___x_487_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_487_;
}
}
}
else
{
goto v___jp_423_;
}
v___jp_423_:
{
lean_object* v___x_424_; 
v___x_424_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed(lean_object* v_x_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(v_x_488_);
lean_dec(v_x_488_);
return v_res_489_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_493_ = l_Lean_JsonNumber_fromInt(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0);
v___x_495_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_497_ = l_Lean_JsonNumber_fromInt(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2);
v___x_499_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_501_ = l_Lean_JsonNumber_fromInt(v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4);
v___x_503_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_505_ = l_Lean_JsonNumber_fromInt(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6);
v___x_507_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_509_ = l_Lean_JsonNumber_fromInt(v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8);
v___x_511_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_513_ = l_Lean_JsonNumber_fromInt(v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10);
v___x_515_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_517_ = l_Lean_JsonNumber_fromInt(v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12);
v___x_519_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_521_ = l_Lean_JsonNumber_fromInt(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14);
v___x_523_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_525_ = l_Lean_JsonNumber_fromInt(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16);
v___x_527_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_529_ = l_Lean_JsonNumber_fromInt(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18);
v___x_531_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_533_ = l_Lean_JsonNumber_fromInt(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20);
v___x_535_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_537_ = l_Lean_JsonNumber_fromInt(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22);
v___x_539_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t v_x_540_){
_start:
{
switch(v_x_540_)
{
case 0:
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
return v___x_541_;
}
case 1:
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
return v___x_542_;
}
case 2:
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
return v___x_543_;
}
case 3:
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
return v___x_544_;
}
case 4:
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
return v___x_545_;
}
case 5:
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
return v___x_546_;
}
case 6:
{
lean_object* v___x_547_; 
v___x_547_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
return v___x_547_;
}
case 7:
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
return v___x_548_;
}
case 8:
{
lean_object* v___x_549_; 
v___x_549_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
return v___x_549_;
}
case 9:
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
return v___x_550_;
}
case 10:
{
lean_object* v___x_551_; 
v___x_551_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
return v___x_551_;
}
default: 
{
lean_object* v___x_552_; 
v___x_552_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object* v_x_553_){
_start:
{
uint8_t v_x_474__boxed_554_; lean_object* v_res_555_; 
v_x_474__boxed_554_ = lean_unbox(v_x_553_);
v_res_555_ = l_Lean_JsonRpc_instToJsonErrorCode___lam__0(v_x_474__boxed_554_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx(lean_object* v_x_558_){
_start:
{
switch(lean_obj_tag(v_x_558_))
{
case 0:
{
lean_object* v___x_559_; 
v___x_559_ = lean_unsigned_to_nat(0u);
return v___x_559_;
}
case 1:
{
lean_object* v___x_560_; 
v___x_560_ = lean_unsigned_to_nat(1u);
return v___x_560_;
}
case 2:
{
lean_object* v___x_561_; 
v___x_561_ = lean_unsigned_to_nat(2u);
return v___x_561_;
}
default: 
{
lean_object* v___x_562_; 
v___x_562_ = lean_unsigned_to_nat(3u);
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___boxed(lean_object* v_x_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_JsonRpc_Message_ctorIdx(v_x_563_);
lean_dec_ref(v_x_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___redArg(lean_object* v_t_565_, lean_object* v_k_566_){
_start:
{
switch(lean_obj_tag(v_t_565_))
{
case 0:
{
lean_object* v_id_567_; lean_object* v_method_568_; lean_object* v_params_x3f_569_; lean_object* v___x_570_; 
v_id_567_ = lean_ctor_get(v_t_565_, 0);
lean_inc(v_id_567_);
v_method_568_ = lean_ctor_get(v_t_565_, 1);
lean_inc_ref(v_method_568_);
v_params_x3f_569_ = lean_ctor_get(v_t_565_, 2);
lean_inc(v_params_x3f_569_);
lean_dec_ref(v_t_565_);
v___x_570_ = lean_apply_3(v_k_566_, v_id_567_, v_method_568_, v_params_x3f_569_);
return v___x_570_;
}
case 1:
{
lean_object* v_method_571_; lean_object* v_params_x3f_572_; lean_object* v___x_573_; 
v_method_571_ = lean_ctor_get(v_t_565_, 0);
lean_inc_ref(v_method_571_);
v_params_x3f_572_ = lean_ctor_get(v_t_565_, 1);
lean_inc(v_params_x3f_572_);
lean_dec_ref(v_t_565_);
v___x_573_ = lean_apply_2(v_k_566_, v_method_571_, v_params_x3f_572_);
return v___x_573_;
}
case 2:
{
lean_object* v_id_574_; lean_object* v_result_575_; lean_object* v___x_576_; 
v_id_574_ = lean_ctor_get(v_t_565_, 0);
lean_inc(v_id_574_);
v_result_575_ = lean_ctor_get(v_t_565_, 1);
lean_inc(v_result_575_);
lean_dec_ref(v_t_565_);
v___x_576_ = lean_apply_2(v_k_566_, v_id_574_, v_result_575_);
return v___x_576_;
}
default: 
{
lean_object* v_id_577_; uint8_t v_code_578_; lean_object* v_message_579_; lean_object* v_data_x3f_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_id_577_ = lean_ctor_get(v_t_565_, 0);
lean_inc(v_id_577_);
v_code_578_ = lean_ctor_get_uint8(v_t_565_, sizeof(void*)*3);
v_message_579_ = lean_ctor_get(v_t_565_, 1);
lean_inc_ref(v_message_579_);
v_data_x3f_580_ = lean_ctor_get(v_t_565_, 2);
lean_inc(v_data_x3f_580_);
lean_dec_ref(v_t_565_);
v___x_581_ = lean_box(v_code_578_);
v___x_582_ = lean_apply_4(v_k_566_, v_id_577_, v___x_581_, v_message_579_, v_data_x3f_580_);
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim(lean_object* v_motive_583_, lean_object* v_ctorIdx_584_, lean_object* v_t_585_, lean_object* v_h_586_, lean_object* v_k_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_585_, v_k_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___boxed(lean_object* v_motive_589_, lean_object* v_ctorIdx_590_, lean_object* v_t_591_, lean_object* v_h_592_, lean_object* v_k_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_JsonRpc_Message_ctorElim(v_motive_589_, v_ctorIdx_590_, v_t_591_, v_h_592_, v_k_593_);
lean_dec(v_ctorIdx_590_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim___redArg(lean_object* v_t_595_, lean_object* v_request_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_595_, v_request_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim(lean_object* v_motive_598_, lean_object* v_t_599_, lean_object* v_h_600_, lean_object* v_request_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_599_, v_request_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim___redArg(lean_object* v_t_603_, lean_object* v_notification_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_603_, v_notification_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim(lean_object* v_motive_606_, lean_object* v_t_607_, lean_object* v_h_608_, lean_object* v_notification_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_607_, v_notification_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim___redArg(lean_object* v_t_611_, lean_object* v_response_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_611_, v_response_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim(lean_object* v_motive_614_, lean_object* v_t_615_, lean_object* v_h_616_, lean_object* v_response_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_615_, v_response_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim___redArg(lean_object* v_t_619_, lean_object* v_responseError_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_619_, v_responseError_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim(lean_object* v_motive_622_, lean_object* v_t_623_, lean_object* v_h_624_, lean_object* v_responseError_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_623_, v_responseError_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default___redArg(lean_object* v_inst_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default));
v___x_635_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
lean_ctor_set(v___x_636_, 2, v_inst_633_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default(lean_object* v_00_u03b1_637_, lean_object* v_inst_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___redArg(lean_object* v_inst_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object* v_a_642_, lean_object* v_inst_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_643_);
return v___x_644_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq___redArg(lean_object* v_inst_645_, lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
lean_object* v_id_648_; lean_object* v_method_649_; lean_object* v_param_650_; lean_object* v_id_651_; lean_object* v_method_652_; lean_object* v_param_653_; uint8_t v___x_654_; 
v_id_648_ = lean_ctor_get(v_x_646_, 0);
lean_inc(v_id_648_);
v_method_649_ = lean_ctor_get(v_x_646_, 1);
lean_inc_ref(v_method_649_);
v_param_650_ = lean_ctor_get(v_x_646_, 2);
lean_inc(v_param_650_);
lean_dec_ref(v_x_646_);
v_id_651_ = lean_ctor_get(v_x_647_, 0);
lean_inc(v_id_651_);
v_method_652_ = lean_ctor_get(v_x_647_, 1);
lean_inc_ref(v_method_652_);
v_param_653_ = lean_ctor_get(v_x_647_, 2);
lean_inc(v_param_653_);
lean_dec_ref(v_x_647_);
v___x_654_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_648_, v_id_651_);
lean_dec(v_id_651_);
lean_dec(v_id_648_);
if (v___x_654_ == 0)
{
lean_dec(v_param_653_);
lean_dec_ref(v_method_652_);
lean_dec(v_param_650_);
lean_dec_ref(v_method_649_);
lean_dec_ref(v_inst_645_);
return v___x_654_;
}
else
{
uint8_t v___x_655_; 
v___x_655_ = lean_string_dec_eq(v_method_649_, v_method_652_);
lean_dec_ref(v_method_652_);
lean_dec_ref(v_method_649_);
if (v___x_655_ == 0)
{
lean_dec(v_param_653_);
lean_dec(v_param_650_);
lean_dec_ref(v_inst_645_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = lean_apply_2(v_inst_645_, v_param_650_, v_param_653_);
v___x_657_ = lean_unbox(v___x_656_);
return v___x_657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___redArg___boxed(lean_object* v_inst_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_658_, v_x_659_, v_x_660_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq(lean_object* v_00_u03b1_663_, lean_object* v_inst_664_, lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
uint8_t v___x_667_; 
v___x_667_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_664_, v_x_665_, v_x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___boxed(lean_object* v_00_u03b1_668_, lean_object* v_inst_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l_Lean_JsonRpc_instBEqRequest_beq(v_00_u03b1_668_, v_inst_669_, v_x_670_, v_x_671_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object* v_inst_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_675_, 0, lean_box(0));
lean_closure_set(v___x_675_, 1, v_inst_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object* v_00_u03b1_676_, lean_object* v_inst_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_678_, 0, lean_box(0));
lean_closure_set(v___x_678_, 1, v_inst_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object* v_inst_679_, lean_object* v_r_680_){
_start:
{
lean_object* v_id_681_; lean_object* v_method_682_; lean_object* v_param_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_703_; 
v_id_681_ = lean_ctor_get(v_r_680_, 0);
v_method_682_ = lean_ctor_get(v_r_680_, 1);
v_param_683_ = lean_ctor_get(v_r_680_, 2);
v_isSharedCheck_703_ = !lean_is_exclusive(v_r_680_);
if (v_isSharedCheck_703_ == 0)
{
v___x_685_ = v_r_680_;
v_isShared_686_ = v_isSharedCheck_703_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_param_683_);
lean_inc(v_method_682_);
lean_inc(v_id_681_);
lean_dec(v_r_680_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_703_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_679_, v_param_683_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v___x_688_; lean_object* v___x_690_; 
lean_dec_ref(v___x_687_);
v___x_688_ = lean_box(0);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 2, v___x_688_);
v___x_690_ = v___x_685_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_id_681_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_method_682_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_702_; 
v_a_692_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_702_ == 0)
{
v___x_694_ = v___x_687_;
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_687_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 2, v___x_697_);
v___x_699_ = v___x_685_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_id_681_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_method_682_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object* v_inst_704_){
_start:
{
lean_object* v___f_705_; 
v___f_705_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_705_, 0, v_inst_704_);
return v___f_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object* v_00_u03b1_706_, lean_object* v_inst_707_){
_start:
{
lean_object* v___f_708_; 
v___f_708_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_708_, 0, v_inst_707_);
return v___f_708_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_709_) == 0)
{
lean_object* v___x_710_; 
v___x_710_ = lean_box(0);
return v___x_710_;
}
else
{
lean_object* v_val_711_; lean_object* v___x_712_; 
v_val_711_ = lean_ctor_get(v_x_709_, 0);
lean_inc(v_val_711_);
lean_dec_ref(v_x_709_);
v___x_712_ = l_Lean_Json_Structured_toJson(v_val_711_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ofMessage_x3f(lean_object* v_x_713_){
_start:
{
if (lean_obj_tag(v_x_713_) == 0)
{
lean_object* v_id_714_; lean_object* v_method_715_; lean_object* v_params_x3f_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_725_; 
v_id_714_ = lean_ctor_get(v_x_713_, 0);
v_method_715_ = lean_ctor_get(v_x_713_, 1);
v_params_x3f_716_ = lean_ctor_get(v_x_713_, 2);
v_isSharedCheck_725_ = !lean_is_exclusive(v_x_713_);
if (v_isSharedCheck_725_ == 0)
{
v___x_718_ = v_x_713_;
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_params_x3f_716_);
lean_inc(v_method_715_);
lean_inc(v_id_714_);
lean_dec(v_x_713_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 2, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_id_714_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_method_715_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v___x_720_);
v___x_722_ = v_reuseFailAlloc_724_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; 
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
}
else
{
lean_object* v___x_726_; 
lean_dec_ref(v_x_713_);
v___x_726_ = lean_box(0);
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default___redArg(lean_object* v_inst_727_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v_inst_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default(lean_object* v_00_u03b1_730_, lean_object* v_inst_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___redArg(lean_object* v_inst_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object* v_a_735_, lean_object* v_inst_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_736_);
return v___x_737_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq___redArg(lean_object* v_inst_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v_method_741_; lean_object* v_param_742_; lean_object* v_method_743_; lean_object* v_param_744_; uint8_t v___x_745_; 
v_method_741_ = lean_ctor_get(v_x_739_, 0);
lean_inc_ref(v_method_741_);
v_param_742_ = lean_ctor_get(v_x_739_, 1);
lean_inc(v_param_742_);
lean_dec_ref(v_x_739_);
v_method_743_ = lean_ctor_get(v_x_740_, 0);
lean_inc_ref(v_method_743_);
v_param_744_ = lean_ctor_get(v_x_740_, 1);
lean_inc(v_param_744_);
lean_dec_ref(v_x_740_);
v___x_745_ = lean_string_dec_eq(v_method_741_, v_method_743_);
lean_dec_ref(v_method_743_);
lean_dec_ref(v_method_741_);
if (v___x_745_ == 0)
{
lean_dec(v_param_744_);
lean_dec(v_param_742_);
lean_dec_ref(v_inst_738_);
return v___x_745_;
}
else
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_apply_2(v_inst_738_, v_param_742_, v_param_744_);
v___x_747_ = lean_unbox(v___x_746_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___redArg___boxed(lean_object* v_inst_748_, lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
uint8_t v_res_751_; lean_object* v_r_752_; 
v_res_751_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_748_, v_x_749_, v_x_750_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq(lean_object* v_00_u03b1_753_, lean_object* v_inst_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_754_, v_x_755_, v_x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___boxed(lean_object* v_00_u03b1_758_, lean_object* v_inst_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_Lean_JsonRpc_instBEqNotification_beq(v_00_u03b1_758_, v_inst_759_, v_x_760_, v_x_761_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___redArg(lean_object* v_inst_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(v___x_765_, 0, lean_box(0));
lean_closure_set(v___x_765_, 1, v_inst_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object* v_00_u03b1_766_, lean_object* v_inst_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(v___x_768_, 0, lean_box(0));
lean_closure_set(v___x_768_, 1, v_inst_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(lean_object* v_inst_769_, lean_object* v_r_770_){
_start:
{
lean_object* v_method_771_; lean_object* v_param_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_792_; 
v_method_771_ = lean_ctor_get(v_r_770_, 0);
v_param_772_ = lean_ctor_get(v_r_770_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_r_770_);
if (v_isSharedCheck_792_ == 0)
{
v___x_774_ = v_r_770_;
v_isShared_775_ = v_isSharedCheck_792_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_param_772_);
lean_inc(v_method_771_);
lean_dec(v_r_770_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_792_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_769_, v_param_772_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; lean_object* v___x_779_; 
lean_dec_ref(v___x_776_);
v___x_777_ = lean_box(0);
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 1);
lean_ctor_set(v___x_774_, 1, v___x_777_);
v___x_779_ = v___x_774_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_method_771_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_791_; 
v_a_781_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_791_ == 0)
{
v___x_783_ = v___x_776_;
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_776_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 1);
lean_ctor_set(v___x_774_, 1, v___x_786_);
v___x_788_ = v___x_774_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_method_771_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(lean_object* v_inst_793_){
_start:
{
lean_object* v___f_794_; 
v___f_794_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_794_, 0, v_inst_793_);
return v___f_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object* v_00_u03b1_795_, lean_object* v_inst_796_){
_start:
{
lean_object* v___f_797_; 
v___f_797_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_797_, 0, v_inst_796_);
return v___f_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ofMessage_x3f(lean_object* v_x_798_){
_start:
{
if (lean_obj_tag(v_x_798_) == 1)
{
lean_object* v_method_799_; lean_object* v_params_x3f_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_809_; 
v_method_799_ = lean_ctor_get(v_x_798_, 0);
v_params_x3f_800_ = lean_ctor_get(v_x_798_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_x_798_);
if (v_isSharedCheck_809_ == 0)
{
v___x_802_ = v_x_798_;
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_params_x3f_800_);
lean_inc(v_method_799_);
lean_dec(v_x_798_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_809_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_800_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 0);
lean_ctor_set(v___x_802_, 1, v___x_804_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_method_799_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_804_);
v___x_806_ = v_reuseFailAlloc_808_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
}
else
{
lean_object* v___x_810_; 
lean_dec_ref(v_x_798_);
v___x_810_ = lean_box(0);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default___redArg(lean_object* v_inst_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default));
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v_inst_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default(lean_object* v_00_u03b1_814_, lean_object* v_inst_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___redArg(lean_object* v_inst_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object* v_a_819_, lean_object* v_inst_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_820_);
return v___x_821_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq___redArg(lean_object* v_inst_822_, lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_id_825_; lean_object* v_result_826_; lean_object* v_id_827_; lean_object* v_result_828_; uint8_t v___x_829_; 
v_id_825_ = lean_ctor_get(v_x_823_, 0);
lean_inc(v_id_825_);
v_result_826_ = lean_ctor_get(v_x_823_, 1);
lean_inc(v_result_826_);
lean_dec_ref(v_x_823_);
v_id_827_ = lean_ctor_get(v_x_824_, 0);
lean_inc(v_id_827_);
v_result_828_ = lean_ctor_get(v_x_824_, 1);
lean_inc(v_result_828_);
lean_dec_ref(v_x_824_);
v___x_829_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_825_, v_id_827_);
lean_dec(v_id_827_);
lean_dec(v_id_825_);
if (v___x_829_ == 0)
{
lean_dec(v_result_828_);
lean_dec(v_result_826_);
lean_dec_ref(v_inst_822_);
return v___x_829_;
}
else
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = lean_apply_2(v_inst_822_, v_result_826_, v_result_828_);
v___x_831_ = lean_unbox(v___x_830_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___redArg___boxed(lean_object* v_inst_832_, lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_832_, v_x_833_, v_x_834_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq(lean_object* v_00_u03b1_837_, lean_object* v_inst_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_838_, v_x_839_, v_x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___boxed(lean_object* v_00_u03b1_842_, lean_object* v_inst_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Lean_JsonRpc_instBEqResponse_beq(v_00_u03b1_842_, v_inst_843_, v_x_844_, v_x_845_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object* v_inst_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_849_, 0, lean_box(0));
lean_closure_set(v___x_849_, 1, v_inst_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object* v_00_u03b1_850_, lean_object* v_inst_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_852_, 0, lean_box(0));
lean_closure_set(v___x_852_, 1, v_inst_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(lean_object* v_inst_853_, lean_object* v_r_854_){
_start:
{
lean_object* v_id_855_; lean_object* v_result_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_864_; 
v_id_855_ = lean_ctor_get(v_r_854_, 0);
v_result_856_ = lean_ctor_get(v_r_854_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_r_854_);
if (v_isSharedCheck_864_ == 0)
{
v___x_858_ = v_r_854_;
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_result_856_);
lean_inc(v_id_855_);
lean_dec(v_r_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_860_ = lean_apply_1(v_inst_853_, v_result_856_);
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 2);
lean_ctor_set(v___x_858_, 1, v___x_860_);
v___x_862_ = v___x_858_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_id_855_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object* v_inst_865_){
_start:
{
lean_object* v___f_866_; 
v___f_866_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_866_, 0, v_inst_865_);
return v___f_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object* v_00_u03b1_867_, lean_object* v_inst_868_){
_start:
{
lean_object* v___f_869_; 
v___f_869_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_869_, 0, v_inst_868_);
return v___f_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ofMessage_x3f(lean_object* v_x_870_){
_start:
{
if (lean_obj_tag(v_x_870_) == 2)
{
lean_object* v_id_871_; lean_object* v_result_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_880_; 
v_id_871_ = lean_ctor_get(v_x_870_, 0);
v_result_872_ = lean_ctor_get(v_x_870_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_x_870_);
if (v_isSharedCheck_880_ == 0)
{
v___x_874_ = v_x_870_;
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_result_872_);
lean_inc(v_id_871_);
lean_dec(v_x_870_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set_tag(v___x_874_, 0);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_id_871_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_result_872_);
v___x_877_ = v_reuseFailAlloc_879_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; 
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
}
else
{
lean_object* v___x_881_; 
lean_dec_ref(v_x_870_);
v___x_881_ = lean_box(0);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object* v_00_u03b1_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0));
return v___x_888_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__0(void){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_JsonRpc_instInhabitedResponseError_default(lean_box(0));
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object* v_a_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__0);
return v___x_891_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq___redArg(lean_object* v_inst_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
lean_object* v_id_895_; uint8_t v_code_896_; lean_object* v_message_897_; lean_object* v_data_x3f_898_; lean_object* v_id_899_; uint8_t v_code_900_; lean_object* v_message_901_; lean_object* v_data_x3f_902_; uint8_t v___x_903_; 
v_id_895_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_id_895_);
v_code_896_ = lean_ctor_get_uint8(v_x_893_, sizeof(void*)*3);
v_message_897_ = lean_ctor_get(v_x_893_, 1);
lean_inc_ref(v_message_897_);
v_data_x3f_898_ = lean_ctor_get(v_x_893_, 2);
lean_inc(v_data_x3f_898_);
lean_dec_ref(v_x_893_);
v_id_899_ = lean_ctor_get(v_x_894_, 0);
lean_inc(v_id_899_);
v_code_900_ = lean_ctor_get_uint8(v_x_894_, sizeof(void*)*3);
v_message_901_ = lean_ctor_get(v_x_894_, 1);
lean_inc_ref(v_message_901_);
v_data_x3f_902_ = lean_ctor_get(v_x_894_, 2);
lean_inc(v_data_x3f_902_);
lean_dec_ref(v_x_894_);
v___x_903_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_895_, v_id_899_);
lean_dec(v_id_899_);
lean_dec(v_id_895_);
if (v___x_903_ == 0)
{
lean_dec(v_data_x3f_902_);
lean_dec_ref(v_message_901_);
lean_dec(v_data_x3f_898_);
lean_dec_ref(v_message_897_);
lean_dec_ref(v_inst_892_);
return v___x_903_;
}
else
{
uint8_t v___x_904_; 
v___x_904_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_code_896_, v_code_900_);
if (v___x_904_ == 0)
{
lean_dec(v_data_x3f_902_);
lean_dec_ref(v_message_901_);
lean_dec(v_data_x3f_898_);
lean_dec_ref(v_message_897_);
lean_dec_ref(v_inst_892_);
return v___x_904_;
}
else
{
uint8_t v___x_905_; 
v___x_905_ = lean_string_dec_eq(v_message_897_, v_message_901_);
lean_dec_ref(v_message_901_);
lean_dec_ref(v_message_897_);
if (v___x_905_ == 0)
{
lean_dec(v_data_x3f_902_);
lean_dec(v_data_x3f_898_);
lean_dec_ref(v_inst_892_);
return v___x_905_;
}
else
{
uint8_t v___x_906_; 
v___x_906_ = l_Option_instBEq_beq___redArg(v_inst_892_, v_data_x3f_898_, v_data_x3f_902_);
return v___x_906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(lean_object* v_inst_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
uint8_t v_res_910_; lean_object* v_r_911_; 
v_res_910_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_907_, v_x_908_, v_x_909_);
v_r_911_ = lean_box(v_res_910_);
return v_r_911_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object* v_00_u03b1_912_, lean_object* v_inst_913_, lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_913_, v_x_914_, v_x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___boxed(lean_object* v_00_u03b1_917_, lean_object* v_inst_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
uint8_t v_res_921_; lean_object* v_r_922_; 
v_res_921_ = l_Lean_JsonRpc_instBEqResponseError_beq(v_00_u03b1_917_, v_inst_918_, v_x_919_, v_x_920_);
v_r_922_ = lean_box(v_res_921_);
return v_r_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object* v_inst_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_924_, 0, lean_box(0));
lean_closure_set(v___x_924_, 1, v_inst_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object* v_00_u03b1_925_, lean_object* v_inst_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_927_, 0, lean_box(0));
lean_closure_set(v___x_927_, 1, v_inst_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object* v_inst_928_, lean_object* v_r_929_){
_start:
{
lean_object* v_data_x3f_930_; 
v_data_x3f_930_ = lean_ctor_get(v_r_929_, 2);
lean_inc(v_data_x3f_930_);
if (lean_obj_tag(v_data_x3f_930_) == 0)
{
lean_object* v_id_931_; uint8_t v_code_932_; lean_object* v_message_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v_inst_928_);
v_id_931_ = lean_ctor_get(v_r_929_, 0);
v_code_932_ = lean_ctor_get_uint8(v_r_929_, sizeof(void*)*3);
v_message_933_ = lean_ctor_get(v_r_929_, 1);
v_isSharedCheck_941_ = !lean_is_exclusive(v_r_929_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v_r_929_, 2);
lean_dec(v_unused_942_);
v___x_935_ = v_r_929_;
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_message_933_);
lean_inc(v_id_931_);
lean_dec(v_r_929_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_941_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = lean_box(0);
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 3);
lean_ctor_set(v___x_935_, 2, v___x_937_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_id_931_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_message_933_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v___x_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*3, v_code_932_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
else
{
lean_object* v_id_943_; uint8_t v_code_944_; lean_object* v_message_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_961_; 
v_id_943_ = lean_ctor_get(v_r_929_, 0);
v_code_944_ = lean_ctor_get_uint8(v_r_929_, sizeof(void*)*3);
v_message_945_ = lean_ctor_get(v_r_929_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_r_929_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v_r_929_, 2);
lean_dec(v_unused_962_);
v___x_947_ = v_r_929_;
v_isShared_948_ = v_isSharedCheck_961_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_message_945_);
lean_inc(v_id_943_);
lean_dec(v_r_929_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_961_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_val_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_960_; 
v_val_949_ = lean_ctor_get(v_data_x3f_930_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_data_x3f_930_);
if (v_isSharedCheck_960_ == 0)
{
v___x_951_ = v_data_x3f_930_;
v_isShared_952_ = v_isSharedCheck_960_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_val_949_);
lean_dec(v_data_x3f_930_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_960_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = lean_apply_1(v_inst_928_, v_val_949_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_953_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_957_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 3);
lean_ctor_set(v___x_947_, 2, v___x_955_);
v___x_957_ = v___x_947_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_id_943_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_message_945_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v___x_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*3, v_code_944_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object* v_inst_963_){
_start:
{
lean_object* v___f_964_; 
v___f_964_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_964_, 0, v_inst_963_);
return v___f_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object* v_00_u03b1_965_, lean_object* v_inst_966_){
_start:
{
lean_object* v___f_967_; 
v___f_967_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_967_, 0, v_inst_966_);
return v___f_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object* v_r_968_){
_start:
{
lean_object* v_id_969_; uint8_t v_code_970_; lean_object* v_message_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_979_; 
v_id_969_ = lean_ctor_get(v_r_968_, 0);
v_code_970_ = lean_ctor_get_uint8(v_r_968_, sizeof(void*)*3);
v_message_971_ = lean_ctor_get(v_r_968_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_r_968_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v_r_968_, 2);
lean_dec(v_unused_980_);
v___x_973_ = v_r_968_;
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_message_971_);
lean_inc(v_id_969_);
lean_dec(v_r_968_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_975_ = lean_box(0);
if (v_isShared_974_ == 0)
{
lean_ctor_set_tag(v___x_973_, 3);
lean_ctor_set(v___x_973_, 2, v___x_975_);
v___x_977_ = v___x_973_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_id_969_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_message_971_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v___x_975_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, sizeof(void*)*3, v_code_970_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ofMessage_x3f(lean_object* v_x_983_){
_start:
{
if (lean_obj_tag(v_x_983_) == 3)
{
lean_object* v_id_984_; uint8_t v_code_985_; lean_object* v_message_986_; lean_object* v_data_x3f_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_995_; 
v_id_984_ = lean_ctor_get(v_x_983_, 0);
v_code_985_ = lean_ctor_get_uint8(v_x_983_, sizeof(void*)*3);
v_message_986_ = lean_ctor_get(v_x_983_, 1);
v_data_x3f_987_ = lean_ctor_get(v_x_983_, 2);
v_isSharedCheck_995_ = !lean_is_exclusive(v_x_983_);
if (v_isSharedCheck_995_ == 0)
{
v___x_989_ = v_x_983_;
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_data_x3f_987_);
lean_inc(v_message_986_);
lean_inc(v_id_984_);
lean_dec(v_x_983_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 0);
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_id_984_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_message_986_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_data_x3f_987_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*3, v_code_985_);
v___x_992_ = v_reuseFailAlloc_994_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
}
else
{
lean_object* v___x_996_; 
lean_dec_ref(v_x_983_);
v___x_996_ = lean_box(0);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object* v_s_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v_s_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object* v_n_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1002_, 0, v_n_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_RequestID_lt(lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
switch(lean_obj_tag(v_x_1005_))
{
case 0:
{
if (lean_obj_tag(v_x_1006_) == 0)
{
lean_object* v_s_1007_; lean_object* v_s_1008_; uint8_t v___x_1009_; 
v_s_1007_ = lean_ctor_get(v_x_1005_, 0);
lean_inc_ref(v_s_1007_);
lean_dec_ref(v_x_1005_);
v_s_1008_ = lean_ctor_get(v_x_1006_, 0);
lean_inc_ref(v_s_1008_);
lean_dec_ref(v_x_1006_);
v___x_1009_ = lean_string_dec_lt(v_s_1007_, v_s_1008_);
lean_dec_ref(v_s_1008_);
lean_dec_ref(v_s_1007_);
return v___x_1009_;
}
else
{
uint8_t v___x_1010_; 
lean_dec_ref(v_x_1005_);
lean_dec(v_x_1006_);
v___x_1010_ = 0;
return v___x_1010_;
}
}
case 1:
{
switch(lean_obj_tag(v_x_1006_))
{
case 1:
{
lean_object* v_n_1011_; lean_object* v_n_1012_; uint8_t v___x_1013_; 
v_n_1011_ = lean_ctor_get(v_x_1005_, 0);
lean_inc_ref(v_n_1011_);
lean_dec_ref(v_x_1005_);
v_n_1012_ = lean_ctor_get(v_x_1006_, 0);
lean_inc_ref(v_n_1012_);
lean_dec_ref(v_x_1006_);
v___x_1013_ = l_Lean_JsonNumber_lt(v_n_1011_, v_n_1012_);
return v___x_1013_;
}
case 0:
{
uint8_t v___x_1014_; 
lean_dec_ref(v_x_1006_);
lean_dec_ref(v_x_1005_);
v___x_1014_ = 1;
return v___x_1014_;
}
default: 
{
uint8_t v___x_1015_; 
lean_dec_ref(v_x_1005_);
lean_dec(v_x_1006_);
v___x_1015_ = 0;
return v___x_1015_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_1006_))
{
case 1:
{
uint8_t v___x_1016_; 
lean_dec_ref(v_x_1006_);
v___x_1016_ = 1;
return v___x_1016_;
}
case 0:
{
uint8_t v___x_1017_; 
lean_dec_ref(v_x_1006_);
v___x_1017_ = 1;
return v___x_1017_;
}
default: 
{
uint8_t v___x_1018_; 
lean_dec(v_x_1006_);
v___x_1018_ = 0;
return v___x_1018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_lt___boxed(lean_object* v_x_1019_, lean_object* v_x_1020_){
_start:
{
uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_res_1021_ = l_Lean_JsonRpc_RequestID_lt(v_x_1019_, v_x_1020_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
static lean_object* _init_l_Lean_JsonRpc_RequestID_ltProp(void){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_box(0);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instLTRequestID(void){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_box(0);
return v___x_1024_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object* v_a_1025_, lean_object* v_b_1026_){
_start:
{
uint8_t v___x_1027_; 
v___x_1027_ = l_Lean_JsonRpc_RequestID_lt(v_a_1025_, v_b_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object* v_a_1028_, lean_object* v_b_1029_){
_start:
{
uint8_t v_res_1030_; lean_object* v_r_1031_; 
v_res_1030_ = l_Lean_JsonRpc_instDecidableLtRequestID(v_a_1028_, v_b_1029_);
v_r_1031_ = lean_box(v_res_1030_);
return v_r_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object* v_j_1035_){
_start:
{
switch(lean_obj_tag(v_j_1035_))
{
case 3:
{
lean_object* v_s_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1044_; 
v_s_1036_ = lean_ctor_get(v_j_1035_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_j_1035_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1038_ = v_j_1035_;
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_s_1036_);
lean_dec(v_j_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 0);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_s_1036_);
v___x_1041_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
}
case 2:
{
lean_object* v_n_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1053_; 
v_n_1045_ = lean_ctor_get(v_j_1035_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_j_1035_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1047_ = v_j_1035_;
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_n_1045_);
lean_dec(v_j_1035_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 1);
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_n_1045_);
v___x_1050_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
}
default: 
{
lean_object* v___x_1054_; 
lean_dec(v_j_1035_);
v___x_1054_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object* v_rid_1057_){
_start:
{
switch(lean_obj_tag(v_rid_1057_))
{
case 0:
{
lean_object* v_s_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v_s_1058_ = lean_ctor_get(v_rid_1057_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_rid_1057_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v_rid_1057_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_s_1058_);
lean_dec(v_rid_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set_tag(v___x_1060_, 3);
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_s_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
case 1:
{
lean_object* v_n_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
v_n_1066_ = lean_ctor_get(v_rid_1057_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_rid_1057_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v_rid_1057_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_n_1066_);
lean_dec(v_rid_1057_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set_tag(v___x_1068_, 2);
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_n_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
default: 
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_box(0);
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v_m_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___y_1097_; 
v___x_1095_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_1094_))
{
case 0:
{
lean_object* v_id_1100_; lean_object* v_method_1101_; lean_object* v_params_x3f_1102_; lean_object* v___x_1103_; lean_object* v___y_1105_; 
lean_dec_ref(v___x_1093_);
v_id_1100_ = lean_ctor_get(v_m_1094_, 0);
lean_inc(v_id_1100_);
v_method_1101_ = lean_ctor_get(v_m_1094_, 1);
lean_inc_ref(v_method_1101_);
v_params_x3f_1102_ = lean_ctor_get(v_m_1094_, 2);
lean_inc(v_params_x3f_1102_);
lean_dec_ref(v_m_1094_);
v___x_1103_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1100_))
{
case 0:
{
lean_object* v_s_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_s_1116_ = lean_ctor_get(v_id_1100_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_id_1100_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v_id_1100_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_s_1116_);
lean_dec(v_id_1100_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 3);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_s_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
v___y_1105_ = v___x_1121_;
goto v___jp_1104_;
}
}
}
case 1:
{
lean_object* v_n_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
v_n_1124_ = lean_ctor_get(v_id_1100_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_id_1100_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v_id_1100_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_n_1124_);
lean_dec(v_id_1100_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set_tag(v___x_1126_, 2);
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_n_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
v___y_1105_ = v___x_1129_;
goto v___jp_1104_;
}
}
}
default: 
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_box(0);
v___y_1105_ = v___x_1132_;
goto v___jp_1104_;
}
}
v___jp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1103_);
lean_ctor_set(v___x_1106_, 1, v___y_1105_);
v___x_1107_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_method_1101_);
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1106_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1114_ = l_Lean_Json_opt___redArg(v___x_1092_, v___x_1113_, v_params_x3f_1102_);
v___x_1115_ = l_List_appendTR___redArg(v___x_1112_, v___x_1114_);
v___y_1097_ = v___x_1115_;
goto v___jp_1096_;
}
}
case 1:
{
lean_object* v_method_1133_; lean_object* v_params_x3f_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v___x_1093_);
v_method_1133_ = lean_ctor_get(v_m_1094_, 0);
v_params_x3f_1134_ = lean_ctor_get(v_m_1094_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_m_1094_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1136_ = v_m_1094_;
v_isShared_1137_ = v_isSharedCheck_1146_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_params_x3f_1134_);
lean_inc(v_method_1133_);
lean_dec(v_m_1094_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1146_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1138_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_method_1133_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 0);
lean_ctor_set(v___x_1136_, 1, v___x_1139_);
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1141_ = v___x_1136_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1143_ = l_Lean_Json_opt___redArg(v___x_1092_, v___x_1142_, v_params_x3f_1134_);
v___x_1144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1141_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___y_1097_ = v___x_1144_;
goto v___jp_1096_;
}
}
}
case 2:
{
lean_object* v_id_1147_; lean_object* v_result_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v___x_1093_);
lean_dec_ref(v___x_1092_);
v_id_1147_ = lean_ctor_get(v_m_1094_, 0);
v_result_1148_ = lean_ctor_get(v_m_1094_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_m_1094_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1150_ = v_m_1094_;
v_isShared_1151_ = v_isSharedCheck_1180_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_result_1148_);
lean_inc(v_id_1147_);
lean_dec(v_m_1094_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1180_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___y_1154_; 
v___x_1152_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1147_))
{
case 0:
{
lean_object* v_s_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_s_1163_ = lean_ctor_get(v_id_1147_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_id_1147_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v_id_1147_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_s_1163_);
lean_dec(v_id_1147_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 3);
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_s_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
v___y_1154_ = v___x_1168_;
goto v___jp_1153_;
}
}
}
case 1:
{
lean_object* v_n_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_n_1171_ = lean_ctor_get(v_id_1147_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_id_1147_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v_id_1147_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_n_1171_);
lean_dec(v_id_1147_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 2);
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_n_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
v___y_1154_ = v___x_1176_;
goto v___jp_1153_;
}
}
}
default: 
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_box(0);
v___y_1154_ = v___x_1179_;
goto v___jp_1153_;
}
}
v___jp_1153_:
{
lean_object* v___x_1156_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 0);
lean_ctor_set(v___x_1150_, 1, v___y_1154_);
lean_ctor_set(v___x_1150_, 0, v___x_1152_);
v___x_1156_ = v___x_1150_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___y_1154_);
v___x_1156_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1157_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v_result_1148_);
v___x_1159_ = lean_box(0);
v___x_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1156_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___y_1097_ = v___x_1161_;
goto v___jp_1096_;
}
}
}
}
default: 
{
lean_object* v_id_1181_; uint8_t v_code_1182_; lean_object* v_message_1183_; lean_object* v_data_x3f_1184_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___x_1204_; lean_object* v___y_1206_; 
lean_dec_ref(v___x_1092_);
v_id_1181_ = lean_ctor_get(v_m_1094_, 0);
lean_inc(v_id_1181_);
v_code_1182_ = lean_ctor_get_uint8(v_m_1094_, sizeof(void*)*3);
v_message_1183_ = lean_ctor_get(v_m_1094_, 1);
lean_inc_ref(v_message_1183_);
v_data_x3f_1184_ = lean_ctor_get(v_m_1094_, 2);
lean_inc(v_data_x3f_1184_);
lean_dec_ref(v_m_1094_);
v___x_1204_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1181_))
{
case 0:
{
lean_object* v_s_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v_s_1222_ = lean_ctor_get(v_id_1181_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_id_1181_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v_id_1181_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_s_1222_);
lean_dec(v_id_1181_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 3);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_s_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
v___y_1206_ = v___x_1227_;
goto v___jp_1205_;
}
}
}
case 1:
{
lean_object* v_n_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
v_n_1230_ = lean_ctor_get(v_id_1181_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_id_1181_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v_id_1181_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_n_1230_);
lean_dec(v_id_1181_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set_tag(v___x_1232_, 2);
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_n_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
v___y_1206_ = v___x_1235_;
goto v___jp_1205_;
}
}
}
default: 
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_box(0);
v___y_1206_ = v___x_1238_;
goto v___jp_1205_;
}
}
v___jp_1185_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
lean_inc(v___y_1189_);
lean_inc_ref(v___y_1187_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___y_1187_);
lean_ctor_set(v___x_1190_, 1, v___y_1189_);
v___x_1191_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_message_1183_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1190_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1198_ = l_Lean_Json_opt___redArg(v___x_1093_, v___x_1197_, v_data_x3f_1184_);
v___x_1199_ = l_List_appendTR___redArg(v___x_1196_, v___x_1198_);
v___x_1200_ = l_Lean_Json_mkObj(v___x_1199_);
lean_inc_ref(v___y_1188_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___y_1188_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___x_1194_);
v___x_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___y_1186_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___y_1097_ = v___x_1203_;
goto v___jp_1096_;
}
v___jp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1204_);
lean_ctor_set(v___x_1207_, 1, v___y_1206_);
v___x_1208_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1209_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_1182_)
{
case 0:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1210_;
goto v___jp_1185_;
}
case 1:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1211_;
goto v___jp_1185_;
}
case 2:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1212_;
goto v___jp_1185_;
}
case 3:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1213_;
goto v___jp_1185_;
}
case 4:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1214_;
goto v___jp_1185_;
}
case 5:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1215_;
goto v___jp_1185_;
}
case 6:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1216_;
goto v___jp_1185_;
}
case 7:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1217_;
goto v___jp_1185_;
}
case 8:
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1218_;
goto v___jp_1185_;
}
case 9:
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1219_;
goto v___jp_1185_;
}
case 10:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1220_;
goto v___jp_1185_;
}
default: 
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_1186_ = v___x_1207_;
v___y_1187_ = v___x_1209_;
v___y_1188_ = v___x_1208_;
v___y_1189_ = v___x_1221_;
goto v___jp_1185_;
}
}
}
}
}
v___jp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1095_);
lean_ctor_set(v___x_1098_, 1, v___y_1097_);
v___x_1099_ = l_Lean_Json_mkObj(v___x_1098_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object* v___f_1248_, lean_object* v___f_1249_, lean_object* v___x_1250_, lean_object* v___x_1251_, lean_object* v_j_1252_){
_start:
{
lean_object* v___y_1256_; uint8_t v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1252_);
v___x_1268_ = l_Lean_Json_getObjVal_x3f(v_j_1252_, v___x_1267_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v_j_1252_);
lean_dec_ref(v___x_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___f_1249_);
lean_dec_ref(v___f_1248_);
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
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
lean_object* v_a_1277_; 
v_a_1277_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1277_);
lean_dec_ref(v___x_1268_);
if (lean_obj_tag(v_a_1277_) == 3)
{
lean_object* v_s_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_s_1278_ = lean_ctor_get(v_a_1277_, 0);
lean_inc_ref(v_s_1278_);
lean_dec_ref(v_a_1277_);
v___x_1279_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1280_ = lean_string_dec_eq(v_s_1278_, v___x_1279_);
lean_dec_ref(v_s_1278_);
if (v___x_1280_ == 0)
{
lean_dec(v_j_1252_);
lean_dec_ref(v___x_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___f_1249_);
lean_dec_ref(v___f_1248_);
goto v___jp_1253_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1252_);
v___x_1282_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1252_, v___f_1248_, v___x_1281_);
if (lean_obj_tag(v___x_1282_) == 0)
{
goto v___jp_1339_;
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_a_1366_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1366_);
v___x_1367_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1250_);
lean_inc(v_j_1252_);
v___x_1368_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1252_, v___x_1250_, v___x_1367_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_dec_ref(v___x_1368_);
lean_dec(v_a_1366_);
goto v___jp_1339_;
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v___x_1282_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___f_1249_);
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1390_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1390_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___y_1374_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1380_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1252_, v___x_1251_, v___x_1379_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v___x_1381_; 
lean_dec_ref(v___x_1380_);
v___x_1381_ = lean_box(0);
v___y_1374_ = v___x_1381_;
goto v___jp_1373_;
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
v_a_1382_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1380_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1380_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
v___y_1374_ = v___x_1387_;
goto v___jp_1373_;
}
}
}
v___jp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1375_, 0, v_a_1366_);
lean_ctor_set(v___x_1375_, 1, v_a_1369_);
lean_ctor_set(v___x_1375_, 2, v___y_1374_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1375_);
v___x_1377_ = v___x_1371_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
v___jp_1283_:
{
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_j_1252_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___f_1249_);
v_a_1284_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1282_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1282_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_a_1292_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1292_);
lean_dec_ref(v___x_1282_);
v___x_1293_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1294_ = l_Lean_Json_getObjVal_x3f(v_j_1252_, v___x_1293_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_a_1292_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___f_1249_);
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1294_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1294_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v_a_1303_ = lean_ctor_get(v___x_1294_, 0);
lean_inc_n(v_a_1303_, 2);
lean_dec_ref(v___x_1294_);
v___x_1304_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1305_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1303_, v___f_1249_, v___x_1304_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_a_1303_);
lean_dec(v_a_1292_);
lean_dec_ref(v___x_1250_);
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_a_1314_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1305_);
v___x_1315_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1303_);
v___x_1316_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1303_, v___x_1250_, v___x_1315_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_a_1314_);
lean_dec(v_a_1303_);
lean_dec(v_a_1292_);
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_a_1325_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1325_);
lean_dec_ref(v___x_1316_);
v___x_1326_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1327_ = l_Lean_Json_getObjVal_x3f(v_a_1303_, v___x_1326_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
lean_dec_ref(v___x_1327_);
v___x_1328_ = lean_box(0);
v___x_1329_ = lean_unbox(v_a_1314_);
lean_dec(v_a_1314_);
v___y_1256_ = v_a_1325_;
v___y_1257_ = v___x_1329_;
v___y_1258_ = v_a_1292_;
v___y_1259_ = v___x_1328_;
goto v___jp_1255_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1338_; 
v_a_1330_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1332_ = v___x_1327_;
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1327_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1338_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_unbox(v_a_1314_);
lean_dec(v_a_1314_);
v___y_1256_ = v_a_1325_;
v___y_1257_ = v___x_1336_;
v___y_1258_ = v_a_1292_;
v___y_1259_ = v___x_1335_;
goto v___jp_1255_;
}
}
}
}
}
}
}
}
v___jp_1339_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1250_);
lean_inc(v_j_1252_);
v___x_1341_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1252_, v___x_1250_, v___x_1340_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec_ref(v___x_1341_);
lean_dec_ref(v___x_1251_);
if (lean_obj_tag(v___x_1282_) == 0)
{
goto v___jp_1283_;
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v_a_1342_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1342_);
v___x_1343_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1252_);
v___x_1344_ = l_Lean_Json_getObjVal_x3f(v_j_1252_, v___x_1343_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_dec_ref(v___x_1344_);
lean_dec(v_a_1342_);
goto v___jp_1283_;
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v___x_1282_);
lean_dec(v_j_1252_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___f_1249_);
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_a_1342_);
lean_ctor_set(v___x_1349_, 1, v_a_1345_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1349_);
v___x_1351_ = v___x_1347_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec_ref(v___x_1282_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___f_1249_);
v_a_1354_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1354_);
lean_dec_ref(v___x_1341_);
v___x_1355_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1356_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1252_, v___x_1251_, v___x_1355_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v___x_1357_; 
lean_dec_ref(v___x_1356_);
v___x_1357_ = lean_box(0);
v___y_1263_ = v_a_1354_;
v___y_1264_ = v___x_1357_;
goto v___jp_1262_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
v_a_1358_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1356_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1356_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
v___y_1263_ = v_a_1354_;
v___y_1264_ = v___x_1363_;
goto v___jp_1262_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1277_);
lean_dec(v_j_1252_);
lean_dec_ref(v___x_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___f_1249_);
lean_dec_ref(v___f_1248_);
goto v___jp_1253_;
}
}
v___jp_1253_:
{
lean_object* v___x_1254_; 
v___x_1254_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1));
return v___x_1254_;
}
v___jp_1255_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1260_, 0, v___y_1258_);
lean_ctor_set(v___x_1260_, 1, v___y_1256_);
lean_ctor_set(v___x_1260_, 2, v___y_1259_);
lean_ctor_set_uint8(v___x_1260_, sizeof(void*)*3, v___y_1257_);
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
v___jp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___y_1263_);
lean_ctor_set(v___x_1265_, 1, v___y_1264_);
v___x_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object* v___x_1404_, lean_object* v_inst_1405_, lean_object* v_j_1406_){
_start:
{
lean_object* v_method_1410_; lean_object* v_params_x3f_1411_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1406_);
v___x_1434_ = l_Lean_Json_getObjVal_x3f(v_j_1406_, v___x_1433_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_j_1406_);
lean_dec_ref(v_inst_1405_);
lean_dec_ref(v___x_1404_);
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
else
{
lean_object* v_a_1443_; 
v_a_1443_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1443_);
lean_dec_ref(v___x_1434_);
if (lean_obj_tag(v_a_1443_) == 3)
{
lean_object* v_s_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v_s_1444_ = lean_ctor_get(v_a_1443_, 0);
lean_inc_ref(v_s_1444_);
lean_dec_ref(v_a_1443_);
v___x_1445_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1446_ = lean_string_dec_eq(v_s_1444_, v___x_1445_);
lean_dec_ref(v_s_1444_);
if (v___x_1446_ == 0)
{
lean_dec(v_j_1406_);
lean_dec_ref(v_inst_1405_);
lean_dec_ref(v___x_1404_);
goto v___jp_1431_;
}
else
{
lean_object* v___f_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___f_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___f_1447_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___closed__0));
v___x_1448_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__0));
v___x_1449_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__1));
v___f_1450_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___closed__0));
v___x_1451_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1406_);
v___x_1452_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1406_, v___f_1447_, v___x_1451_);
if (lean_obj_tag(v___x_1452_) == 0)
{
goto v___jp_1493_;
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1406_);
v___x_1511_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1406_, v___x_1448_, v___x_1510_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_dec_ref(v___x_1511_);
goto v___jp_1493_;
}
else
{
lean_dec_ref(v___x_1511_);
lean_dec_ref(v___x_1452_);
lean_dec(v_j_1406_);
lean_dec_ref(v_inst_1405_);
lean_dec_ref(v___x_1404_);
goto v___jp_1407_;
}
}
v___jp_1453_:
{
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_j_1406_);
v_a_1454_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1452_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1452_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec_ref(v___x_1452_);
v___x_1462_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1463_ = l_Lean_Json_getObjVal_x3f(v_j_1406_, v___x_1462_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_a_1472_ = lean_ctor_get(v___x_1463_, 0);
lean_inc_n(v_a_1472_, 2);
lean_dec_ref(v___x_1463_);
v___x_1473_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1474_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1472_, v___f_1450_, v___x_1473_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_a_1472_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec_ref(v___x_1474_);
v___x_1483_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1484_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1472_, v___x_1448_, v___x_1483_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
lean_dec_ref(v___x_1484_);
goto v___jp_1407_;
}
}
}
}
}
v___jp_1493_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1406_);
v___x_1495_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1406_, v___x_1448_, v___x_1494_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_dec_ref(v___x_1495_);
lean_dec_ref(v_inst_1405_);
lean_dec_ref(v___x_1404_);
if (lean_obj_tag(v___x_1452_) == 0)
{
goto v___jp_1453_;
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1406_);
v___x_1497_ = l_Lean_Json_getObjVal_x3f(v_j_1406_, v___x_1496_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_dec_ref(v___x_1497_);
goto v___jp_1453_;
}
else
{
lean_dec_ref(v___x_1497_);
lean_dec_ref(v___x_1452_);
lean_dec(v_j_1406_);
goto v___jp_1407_;
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec_ref(v___x_1452_);
v_a_1498_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1498_);
lean_dec_ref(v___x_1495_);
v___x_1499_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1500_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1406_, v___x_1449_, v___x_1499_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v___x_1501_; 
lean_dec_ref(v___x_1500_);
v___x_1501_ = lean_box(0);
v_method_1410_ = v_a_1498_;
v_params_x3f_1411_ = v___x_1501_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_a_1502_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1500_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1500_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
v_method_1410_ = v_a_1498_;
v_params_x3f_1411_ = v___x_1507_;
goto v___jp_1409_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1443_);
lean_dec(v_j_1406_);
lean_dec_ref(v_inst_1405_);
lean_dec_ref(v___x_1404_);
goto v___jp_1431_;
}
}
v___jp_1407_:
{
lean_object* v___x_1408_; 
v___x_1408_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1));
return v___x_1408_;
}
v___jp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = l_Option_toJson___redArg(v___x_1404_, v_params_x3f_1411_);
v___x_1413_ = lean_apply_1(v_inst_1405_, v___x_1412_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v_method_1410_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1430_; 
v_a_1422_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1424_ = v___x_1413_;
v_isShared_1425_ = v_isSharedCheck_1430_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1413_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1430_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v_method_1410_);
lean_ctor_set(v___x_1426_, 1, v_a_1422_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1426_);
v___x_1428_ = v___x_1424_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
v___jp_1431_:
{
lean_object* v___x_1432_; 
v___x_1432_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2));
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object* v_inst_1512_){
_start:
{
lean_object* v___x_1513_; lean_object* v___f_1514_; 
v___x_1513_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___f_1514_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1514_, 0, v___x_1513_);
lean_closure_set(v___f_1514_, 1, v_inst_1512_);
return v___f_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object* v_00_u03b1_1515_, lean_object* v_inst_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_JsonRpc_instFromJsonNotification___redArg(v_inst_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx(lean_object* v_x_1518_){
_start:
{
switch(lean_obj_tag(v_x_1518_))
{
case 0:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_unsigned_to_nat(0u);
return v___x_1519_;
}
case 1:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_unsigned_to_nat(1u);
return v___x_1520_;
}
case 2:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_unsigned_to_nat(2u);
return v___x_1521_;
}
default: 
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_unsigned_to_nat(3u);
return v___x_1522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___boxed(lean_object* v_x_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_JsonRpc_MessageMetaData_ctorIdx(v_x_1523_);
lean_dec_ref(v_x_1523_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(lean_object* v_t_1525_, lean_object* v_k_1526_){
_start:
{
switch(lean_obj_tag(v_t_1525_))
{
case 0:
{
lean_object* v_id_1527_; lean_object* v_method_1528_; lean_object* v___x_1529_; 
v_id_1527_ = lean_ctor_get(v_t_1525_, 0);
lean_inc(v_id_1527_);
v_method_1528_ = lean_ctor_get(v_t_1525_, 1);
lean_inc_ref(v_method_1528_);
lean_dec_ref(v_t_1525_);
v___x_1529_ = lean_apply_2(v_k_1526_, v_id_1527_, v_method_1528_);
return v___x_1529_;
}
case 1:
{
lean_object* v_method_1530_; lean_object* v___x_1531_; 
v_method_1530_ = lean_ctor_get(v_t_1525_, 0);
lean_inc_ref(v_method_1530_);
lean_dec_ref(v_t_1525_);
v___x_1531_ = lean_apply_1(v_k_1526_, v_method_1530_);
return v___x_1531_;
}
case 2:
{
lean_object* v_id_1532_; lean_object* v___x_1533_; 
v_id_1532_ = lean_ctor_get(v_t_1525_, 0);
lean_inc(v_id_1532_);
lean_dec_ref(v_t_1525_);
v___x_1533_ = lean_apply_1(v_k_1526_, v_id_1532_);
return v___x_1533_;
}
default: 
{
lean_object* v_id_1534_; uint8_t v_code_1535_; lean_object* v_message_1536_; lean_object* v_data_x3f_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_id_1534_ = lean_ctor_get(v_t_1525_, 0);
lean_inc(v_id_1534_);
v_code_1535_ = lean_ctor_get_uint8(v_t_1525_, sizeof(void*)*3);
v_message_1536_ = lean_ctor_get(v_t_1525_, 1);
lean_inc_ref(v_message_1536_);
v_data_x3f_1537_ = lean_ctor_get(v_t_1525_, 2);
lean_inc(v_data_x3f_1537_);
lean_dec_ref(v_t_1525_);
v___x_1538_ = lean_box(v_code_1535_);
v___x_1539_ = lean_apply_4(v_k_1526_, v_id_1534_, v___x_1538_, v_message_1536_, v_data_x3f_1537_);
return v___x_1539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim(lean_object* v_motive_1540_, lean_object* v_ctorIdx_1541_, lean_object* v_t_1542_, lean_object* v_h_1543_, lean_object* v_k_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1542_, v_k_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(lean_object* v_motive_1546_, lean_object* v_ctorIdx_1547_, lean_object* v_t_1548_, lean_object* v_h_1549_, lean_object* v_k_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_JsonRpc_MessageMetaData_ctorElim(v_motive_1546_, v_ctorIdx_1547_, v_t_1548_, v_h_1549_, v_k_1550_);
lean_dec(v_ctorIdx_1547_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim___redArg(lean_object* v_t_1552_, lean_object* v_request_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1552_, v_request_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim(lean_object* v_motive_1555_, lean_object* v_t_1556_, lean_object* v_h_1557_, lean_object* v_request_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1556_, v_request_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(lean_object* v_t_1560_, lean_object* v_notification_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1560_, v_notification_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim(lean_object* v_motive_1563_, lean_object* v_t_1564_, lean_object* v_h_1565_, lean_object* v_notification_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1564_, v_notification_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(lean_object* v_t_1568_, lean_object* v_response_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1568_, v_response_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim(lean_object* v_motive_1571_, lean_object* v_t_1572_, lean_object* v_h_1573_, lean_object* v_response_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1572_, v_response_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim___redArg(lean_object* v_t_1576_, lean_object* v_responseError_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1576_, v_responseError_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim(lean_object* v_motive_1579_, lean_object* v_t_1580_, lean_object* v_h_1581_, lean_object* v_responseError_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1580_, v_responseError_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_metaData(lean_object* v_x_1589_){
_start:
{
switch(lean_obj_tag(v_x_1589_))
{
case 0:
{
lean_object* v_id_1590_; lean_object* v_method_1591_; lean_object* v___x_1592_; 
v_id_1590_ = lean_ctor_get(v_x_1589_, 0);
lean_inc(v_id_1590_);
v_method_1591_ = lean_ctor_get(v_x_1589_, 1);
lean_inc_ref(v_method_1591_);
lean_dec_ref(v_x_1589_);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v_id_1590_);
lean_ctor_set(v___x_1592_, 1, v_method_1591_);
return v___x_1592_;
}
case 1:
{
lean_object* v_method_1593_; lean_object* v___x_1594_; 
v_method_1593_ = lean_ctor_get(v_x_1589_, 0);
lean_inc_ref(v_method_1593_);
lean_dec_ref(v_x_1589_);
v___x_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_method_1593_);
return v___x_1594_;
}
case 2:
{
lean_object* v_id_1595_; lean_object* v___x_1596_; 
v_id_1595_ = lean_ctor_get(v_x_1589_, 0);
lean_inc(v_id_1595_);
lean_dec_ref(v_x_1589_);
v___x_1596_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1596_, 0, v_id_1595_);
return v___x_1596_;
}
default: 
{
lean_object* v_id_1597_; uint8_t v_code_1598_; lean_object* v_message_1599_; lean_object* v_data_x3f_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_id_1597_ = lean_ctor_get(v_x_1589_, 0);
v_code_1598_ = lean_ctor_get_uint8(v_x_1589_, sizeof(void*)*3);
v_message_1599_ = lean_ctor_get(v_x_1589_, 1);
v_data_x3f_1600_ = lean_ctor_get(v_x_1589_, 2);
v_isSharedCheck_1607_ = !lean_is_exclusive(v_x_1589_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v_x_1589_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_data_x3f_1600_);
lean_inc(v_message_1599_);
lean_inc(v_id_1597_);
lean_dec(v_x_1589_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_id_1597_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_message_1599_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_data_x3f_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*3, v_code_1598_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_toMessage(lean_object* v_x_1608_){
_start:
{
switch(lean_obj_tag(v_x_1608_))
{
case 0:
{
lean_object* v_id_1609_; lean_object* v_method_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_id_1609_ = lean_ctor_get(v_x_1608_, 0);
lean_inc(v_id_1609_);
v_method_1610_ = lean_ctor_get(v_x_1608_, 1);
lean_inc_ref(v_method_1610_);
lean_dec_ref(v_x_1608_);
v___x_1611_ = lean_box(0);
v___x_1612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1612_, 0, v_id_1609_);
lean_ctor_set(v___x_1612_, 1, v_method_1610_);
lean_ctor_set(v___x_1612_, 2, v___x_1611_);
return v___x_1612_;
}
case 1:
{
lean_object* v_method_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v_method_1613_ = lean_ctor_get(v_x_1608_, 0);
lean_inc_ref(v_method_1613_);
lean_dec_ref(v_x_1608_);
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1615_, 0, v_method_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
return v___x_1615_;
}
case 2:
{
lean_object* v_id_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_id_1616_ = lean_ctor_get(v_x_1608_, 0);
lean_inc(v_id_1616_);
lean_dec_ref(v_x_1608_);
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_id_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
return v___x_1618_;
}
default: 
{
lean_object* v_id_1619_; uint8_t v_code_1620_; lean_object* v_message_1621_; lean_object* v_data_x3f_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_id_1619_ = lean_ctor_get(v_x_1608_, 0);
v_code_1620_ = lean_ctor_get_uint8(v_x_1608_, sizeof(void*)*3);
v_message_1621_ = lean_ctor_get(v_x_1608_, 1);
v_data_x3f_1622_ = lean_ctor_get(v_x_1608_, 2);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v_x_1608_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_data_x3f_1622_);
lean_inc(v_message_1621_);
lean_inc(v_id_1619_);
lean_dec(v_x_1608_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_id_1619_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_message_1621_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_data_x3f_1622_);
lean_ctor_set_uint8(v_reuseFailAlloc_1628_, sizeof(void*)*3, v_code_1620_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(lean_object* v_a_1633_){
_start:
{
lean_object* v_fst_1634_; lean_object* v_snd_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; 
v_fst_1634_ = lean_ctor_get(v_a_1633_, 0);
v_snd_1635_ = lean_ctor_get(v_a_1633_, 1);
v___x_1636_ = lean_string_utf8_byte_size(v_fst_1634_);
v___x_1637_ = lean_nat_dec_eq(v_snd_1635_, v___x_1636_);
if (v___x_1637_ == 0)
{
uint32_t v___x_1638_; uint32_t v___x_1639_; uint8_t v___x_1640_; 
v___x_1638_ = lean_string_utf8_get_fast(v_fst_1634_, v_snd_1635_);
v___x_1639_ = 34;
v___x_1640_ = lean_uint32_dec_eq(v___x_1638_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1));
v___x_1642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_a_1633_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
return v___x_1642_;
}
else
{
if (v___x_1637_ == 0)
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1652_; 
lean_inc(v_snd_1635_);
lean_inc(v_fst_1634_);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_a_1633_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; lean_object* v_unused_1654_; 
v_unused_1653_ = lean_ctor_get(v_a_1633_, 1);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_a_1633_, 0);
lean_dec(v_unused_1654_);
v___x_1644_ = v_a_1633_;
v_isShared_1645_ = v_isSharedCheck_1652_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v_a_1633_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1652_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = lean_string_utf8_next_fast(v_fst_1634_, v_snd_1635_);
lean_dec(v_snd_1635_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 1, v___x_1646_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_fst_1634_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_1650_ = l_Lean_Json_Parser_strCore(v___x_1649_, v___x_1648_);
return v___x_1650_;
}
}
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_box(0);
v___x_1656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1656_, 0, v_a_1633_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
return v___x_1656_;
}
}
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1658_, 0, v_a_1633_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(lean_object* v_a_1659_){
_start:
{
lean_object* v___x_1660_; 
lean_inc_ref(v_a_1659_);
v___x_1660_ = l_Lean_Json_Parser_num(v_a_1659_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_pos_1661_; lean_object* v_res_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1670_; 
lean_dec_ref(v_a_1659_);
v_pos_1661_ = lean_ctor_get(v___x_1660_, 0);
v_res_1662_ = lean_ctor_get(v___x_1660_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1664_ = v___x_1660_;
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_res_1662_);
lean_inc(v_pos_1661_);
lean_dec(v___x_1660_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1666_, 0, v_res_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v___x_1666_);
v___x_1668_ = v___x_1664_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_pos_1661_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
else
{
lean_object* v_pos_1671_; lean_object* v_err_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1725_; 
v_pos_1671_ = lean_ctor_get(v___x_1660_, 0);
v_err_1672_ = lean_ctor_get(v___x_1660_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1674_ = v___x_1660_;
v_isShared_1675_ = v_isSharedCheck_1725_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_err_1672_);
lean_inc(v_pos_1671_);
lean_dec(v___x_1660_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1725_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v_snd_1676_; lean_object* v_snd_1677_; uint8_t v___x_1678_; 
v_snd_1676_ = lean_ctor_get(v_a_1659_, 1);
lean_inc(v_snd_1676_);
lean_dec_ref(v_a_1659_);
v_snd_1677_ = lean_ctor_get(v_pos_1671_, 1);
v___x_1678_ = lean_nat_dec_eq(v_snd_1676_, v_snd_1677_);
lean_dec(v_snd_1676_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1680_; 
if (v_isShared_1675_ == 0)
{
v___x_1680_ = v___x_1674_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_pos_1671_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_err_1672_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
else
{
lean_object* v___x_1682_; 
lean_inc(v_snd_1677_);
lean_del_object(v___x_1674_);
lean_dec(v_err_1672_);
v___x_1682_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v_pos_1671_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_pos_1683_; lean_object* v_res_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_snd_1677_);
v_pos_1683_ = lean_ctor_get(v___x_1682_, 0);
v_res_1684_ = lean_ctor_get(v___x_1682_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1686_ = v___x_1682_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_res_1684_);
lean_inc(v_pos_1683_);
lean_dec(v___x_1682_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v_res_1684_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_pos_1683_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
else
{
lean_object* v_pos_1693_; lean_object* v_err_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1724_; 
v_pos_1693_ = lean_ctor_get(v___x_1682_, 0);
v_err_1694_ = lean_ctor_get(v___x_1682_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1696_ = v___x_1682_;
v_isShared_1697_ = v_isSharedCheck_1724_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_err_1694_);
lean_inc(v_pos_1693_);
lean_dec(v___x_1682_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1724_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_snd_1698_; uint8_t v___x_1699_; 
v_snd_1698_ = lean_ctor_get(v_pos_1693_, 1);
v___x_1699_ = lean_nat_dec_eq(v_snd_1677_, v_snd_1698_);
lean_dec(v_snd_1677_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1701_; 
if (v_isShared_1697_ == 0)
{
v___x_1701_ = v___x_1696_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_pos_1693_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_err_1694_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_del_object(v___x_1696_);
lean_dec(v_err_1694_);
v___x_1703_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___x_1704_ = l_Std_Internal_Parsec_String_pstring(v___x_1703_, v_pos_1693_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_pos_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
v_pos_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1713_ == 0)
{
lean_object* v_unused_1714_; 
v_unused_1714_ = lean_ctor_get(v___x_1704_, 1);
lean_dec(v_unused_1714_);
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_pos_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = lean_box(2);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v___x_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_pos_1705_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
else
{
lean_object* v_pos_1715_; lean_object* v_err_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
v_pos_1715_ = lean_ctor_get(v___x_1704_, 0);
v_err_1716_ = lean_ctor_get(v___x_1704_, 1);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1704_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_err_1716_);
lean_inc(v_pos_1715_);
lean_dec(v___x_1704_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_pos_1715_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_err_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object* v_j_1726_, lean_object* v_k_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Json_getObjValD(v_j_1726_, v_k_1727_);
switch(lean_obj_tag(v___x_1728_))
{
case 3:
{
lean_object* v_s_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
v_s_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_s_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set_tag(v___x_1731_, 0);
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_s_1729_);
v___x_1734_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
}
case 2:
{
lean_object* v_n_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1746_; 
v_n_1738_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1740_ = v___x_1728_;
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_n_1738_);
lean_dec(v___x_1728_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set_tag(v___x_1740_, 1);
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_n_1738_);
v___x_1743_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
}
default: 
{
lean_object* v___x_1747_; 
lean_dec(v___x_1728_);
v___x_1747_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object* v_j_1748_, lean_object* v_k_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_j_1748_, v_k_1749_);
lean_dec_ref(v_k_1749_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object* v_j_1751_, lean_object* v_k_1752_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Json_getObjValD(v_j_1751_, v_k_1752_);
if (lean_obj_tag(v___x_1755_) == 2)
{
lean_object* v_n_1756_; lean_object* v_mantissa_1757_; lean_object* v_exponent_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_n_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc_ref(v_n_1756_);
lean_dec_ref(v___x_1755_);
v_mantissa_1757_ = lean_ctor_get(v_n_1756_, 0);
lean_inc(v_mantissa_1757_);
v_exponent_1758_ = lean_ctor_get(v_n_1756_, 1);
lean_inc(v_exponent_1758_);
lean_dec_ref(v_n_1756_);
v___x_1759_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_1760_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_1762_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_1764_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_1766_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_1768_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_1770_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_1772_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_1774_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_1776_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_1778_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_1780_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_1782_ = lean_int_dec_eq(v_mantissa_1757_, v___x_1781_);
lean_dec(v_mantissa_1757_);
if (v___x_1782_ == 0)
{
lean_dec(v_exponent_1758_);
goto v___jp_1753_;
}
else
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1783_);
lean_dec(v_exponent_1758_);
if (v___x_1784_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1785_; 
v___x_1785_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_1785_;
}
}
}
else
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
lean_dec(v_mantissa_1757_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1786_);
lean_dec(v_exponent_1758_);
if (v___x_1787_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1788_; 
v___x_1788_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_1788_;
}
}
}
else
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
lean_dec(v_mantissa_1757_);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1789_);
lean_dec(v_exponent_1758_);
if (v___x_1790_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1791_; 
v___x_1791_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_1791_;
}
}
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
lean_dec(v_mantissa_1757_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1792_);
lean_dec(v_exponent_1758_);
if (v___x_1793_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1794_; 
v___x_1794_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_1794_;
}
}
}
else
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
lean_dec(v_mantissa_1757_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1795_);
lean_dec(v_exponent_1758_);
if (v___x_1796_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1797_; 
v___x_1797_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_1797_;
}
}
}
else
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
lean_dec(v_mantissa_1757_);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1798_);
lean_dec(v_exponent_1758_);
if (v___x_1799_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_1800_;
}
}
}
else
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
lean_dec(v_mantissa_1757_);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1801_);
lean_dec(v_exponent_1758_);
if (v___x_1802_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1803_; 
v___x_1803_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_1803_;
}
}
}
else
{
lean_object* v___x_1804_; uint8_t v___x_1805_; 
lean_dec(v_mantissa_1757_);
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1804_);
lean_dec(v_exponent_1758_);
if (v___x_1805_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1806_; 
v___x_1806_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_1806_;
}
}
}
else
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
lean_dec(v_mantissa_1757_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1807_);
lean_dec(v_exponent_1758_);
if (v___x_1808_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1809_; 
v___x_1809_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_1809_;
}
}
}
else
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
lean_dec(v_mantissa_1757_);
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1810_);
lean_dec(v_exponent_1758_);
if (v___x_1811_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1812_; 
v___x_1812_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_1812_;
}
}
}
else
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
lean_dec(v_mantissa_1757_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1813_);
lean_dec(v_exponent_1758_);
if (v___x_1814_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1815_; 
v___x_1815_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_1815_;
}
}
}
else
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
lean_dec(v_mantissa_1757_);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_nat_dec_eq(v_exponent_1758_, v___x_1816_);
lean_dec(v_exponent_1758_);
if (v___x_1817_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1818_; 
v___x_1818_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_1818_;
}
}
}
else
{
lean_dec(v___x_1755_);
goto v___jp_1753_;
}
v___jp_1753_:
{
lean_object* v___x_1754_; 
v___x_1754_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object* v_j_1819_, lean_object* v_k_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_j_1819_, v_k_1820_);
lean_dec_ref(v_k_1820_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object* v_j_1822_, lean_object* v_k_1823_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = l_Lean_Json_getObjValD(v_j_1822_, v_k_1823_);
v___x_1825_ = l_Lean_Json_getStr_x3f(v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object* v_j_1826_, lean_object* v_k_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_j_1826_, v_k_1827_);
lean_dec_ref(v_k_1827_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object* v_input_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v_fst_1865_; lean_object* v_snd_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v_fst_1865_ = lean_ctor_get(v_a_1839_, 0);
v_snd_1866_ = lean_ctor_get(v_a_1839_, 1);
v___x_1867_ = lean_string_utf8_byte_size(v_fst_1865_);
v___x_1868_ = lean_nat_dec_eq(v_snd_1866_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_2218_; 
lean_inc(v_snd_1866_);
lean_inc(v_fst_1865_);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_a_1839_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; lean_object* v_unused_2220_; 
v_unused_2219_ = lean_ctor_get(v_a_1839_, 1);
lean_dec(v_unused_2219_);
v_unused_2220_ = lean_ctor_get(v_a_1839_, 0);
lean_dec(v_unused_2220_);
v___x_1870_ = v_a_1839_;
v_isShared_1871_ = v_isSharedCheck_2218_;
goto v_resetjp_1869_;
}
else
{
lean_dec(v_a_1839_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_2218_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = lean_string_utf8_next_fast(v_fst_1865_, v_snd_1866_);
lean_dec(v_snd_1866_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 1, v___x_1872_);
v___x_1874_ = v___x_1870_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_fst_1865_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_2217_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; 
v___x_1875_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1874_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_pos_1876_; lean_object* v_res_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_2207_; 
v_pos_1876_ = lean_ctor_get(v___x_1875_, 0);
v_res_1877_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_1879_ = v___x_1875_;
v_isShared_1880_ = v_isSharedCheck_2207_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_res_1877_);
lean_inc(v_pos_1876_);
lean_dec(v___x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_2207_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_fst_1881_; lean_object* v_snd_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v_fst_1881_ = lean_ctor_get(v_pos_1876_, 0);
v_snd_1882_ = lean_ctor_get(v_pos_1876_, 1);
v___x_1883_ = lean_string_utf8_byte_size(v_fst_1881_);
v___x_1884_ = lean_nat_dec_eq(v_snd_1882_, v___x_1883_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_2200_; 
lean_inc(v_snd_1882_);
lean_inc(v_fst_1881_);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_pos_1876_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; lean_object* v_unused_2202_; 
v_unused_2201_ = lean_ctor_get(v_pos_1876_, 1);
lean_dec(v_unused_2201_);
v_unused_2202_ = lean_ctor_get(v_pos_1876_, 0);
lean_dec(v_unused_2202_);
v___x_1886_ = v_pos_1876_;
v_isShared_1887_ = v_isSharedCheck_2200_;
goto v_resetjp_1885_;
}
else
{
lean_dec(v_pos_1876_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_2200_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1888_ = lean_string_utf8_next_fast(v_fst_1881_, v_snd_1882_);
lean_dec(v_snd_1882_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 1, v___x_1888_);
v___x_1890_ = v___x_1886_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_fst_1881_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_2199_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v_id_1892_; uint8_t v_code_1893_; lean_object* v_message_1894_; lean_object* v_data_x3f_1895_; lean_object* v_a_1904_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
v___x_1910_ = lean_string_dec_eq(v_res_1877_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1911_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
v___x_1912_ = lean_string_dec_eq(v_res_1877_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1913_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1914_ = lean_string_dec_eq(v_res_1877_, v___x_1913_);
lean_dec(v_res_1877_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_del_object(v___x_1879_);
lean_dec_ref(v_input_1838_);
v___x_1915_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3));
v___x_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1890_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_Json_parse(v_input_1838_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1926_; 
lean_del_object(v___x_1879_);
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 1);
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1890_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
return v___x_1924_;
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1917_, 0);
lean_inc_n(v_a_1927_, 2);
lean_dec_ref(v___x_1917_);
v___x_1928_ = l_Lean_Json_getObjVal_x3f(v_a_1927_, v___x_1911_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; 
lean_dec(v_a_1927_);
lean_del_object(v___x_1879_);
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
v_a_1904_ = v_a_1929_;
goto v___jp_1903_;
}
else
{
lean_object* v_a_1930_; 
v_a_1930_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___x_1928_);
if (lean_obj_tag(v_a_1930_) == 3)
{
lean_object* v_s_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v_s_1931_ = lean_ctor_get(v_a_1930_, 0);
lean_inc_ref(v_s_1931_);
lean_dec_ref(v_a_1930_);
v___x_1932_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1933_ = lean_string_dec_eq(v_s_1931_, v___x_1932_);
lean_dec_ref(v_s_1931_);
if (v___x_1933_ == 0)
{
lean_dec(v_a_1927_);
lean_del_object(v___x_1879_);
goto v___jp_1907_;
}
else
{
lean_object* v___x_1934_; 
lean_inc(v_a_1927_);
v___x_1934_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_1927_, v___x_1909_);
if (lean_obj_tag(v___x_1934_) == 0)
{
goto v___jp_1962_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1927_);
v___x_1968_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1927_, v___x_1967_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_dec_ref(v___x_1968_);
goto v___jp_1962_;
}
else
{
lean_dec_ref(v___x_1968_);
lean_dec_ref(v___x_1934_);
lean_dec(v_a_1927_);
lean_del_object(v___x_1879_);
goto v___jp_1900_;
}
}
v___jp_1935_:
{
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1936_; 
lean_dec(v_a_1927_);
lean_del_object(v___x_1879_);
v_a_1936_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1934_);
v_a_1904_ = v_a_1936_;
goto v___jp_1903_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1938_; 
v_a_1937_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1937_);
lean_dec_ref(v___x_1934_);
v___x_1938_ = l_Lean_Json_getObjVal_x3f(v_a_1927_, v___x_1913_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; 
lean_dec(v_a_1937_);
lean_del_object(v___x_1879_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref(v___x_1938_);
v_a_1904_ = v_a_1939_;
goto v___jp_1903_;
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_a_1940_ = lean_ctor_get(v___x_1938_, 0);
lean_inc_n(v_a_1940_, 2);
lean_dec_ref(v___x_1938_);
v___x_1941_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1942_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_1940_, v___x_1941_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; 
lean_dec(v_a_1940_);
lean_dec(v_a_1937_);
lean_del_object(v___x_1879_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref(v___x_1942_);
v_a_1904_ = v_a_1943_;
goto v___jp_1903_;
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_a_1944_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1942_);
v___x_1945_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1940_);
v___x_1946_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1940_, v___x_1945_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; 
lean_dec(v_a_1944_);
lean_dec(v_a_1940_);
lean_dec(v_a_1937_);
lean_del_object(v___x_1879_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref(v___x_1946_);
v_a_1904_ = v_a_1947_;
goto v___jp_1903_;
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_a_1948_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1946_);
v___x_1949_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1950_ = l_Lean_Json_getObjVal_x3f(v_a_1940_, v___x_1949_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v___x_1951_; uint8_t v___x_1952_; 
lean_dec_ref(v___x_1950_);
v___x_1951_ = lean_box(0);
v___x_1952_ = lean_unbox(v_a_1944_);
lean_dec(v_a_1944_);
v_id_1892_ = v_a_1937_;
v_code_1893_ = v___x_1952_;
v_message_1894_ = v_a_1948_;
v_data_x3f_1895_ = v___x_1951_;
goto v___jp_1891_;
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1961_; 
v_a_1953_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1955_ = v___x_1950_;
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1950_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
uint8_t v___x_1959_; 
v___x_1959_ = lean_unbox(v_a_1944_);
lean_dec(v_a_1944_);
v_id_1892_ = v_a_1937_;
v_code_1893_ = v___x_1959_;
v_message_1894_ = v_a_1948_;
v_data_x3f_1895_ = v___x_1958_;
goto v___jp_1891_;
}
}
}
}
}
}
}
}
v___jp_1962_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1927_);
v___x_1964_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1927_, v___x_1963_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_dec_ref(v___x_1964_);
if (lean_obj_tag(v___x_1934_) == 0)
{
goto v___jp_1935_;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_1927_);
v___x_1966_ = l_Lean_Json_getObjVal_x3f(v_a_1927_, v___x_1965_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_dec_ref(v___x_1966_);
goto v___jp_1935_;
}
else
{
lean_dec_ref(v___x_1966_);
lean_dec_ref(v___x_1934_);
lean_dec(v_a_1927_);
lean_del_object(v___x_1879_);
goto v___jp_1900_;
}
}
}
else
{
lean_dec_ref(v___x_1964_);
lean_dec_ref(v___x_1934_);
lean_dec(v_a_1927_);
lean_del_object(v___x_1879_);
goto v___jp_1900_;
}
}
}
}
else
{
lean_dec(v_a_1930_);
lean_dec(v_a_1927_);
lean_del_object(v___x_1879_);
goto v___jp_1907_;
}
}
}
}
}
else
{
lean_object* v___x_1969_; 
lean_del_object(v___x_1879_);
lean_dec(v_res_1877_);
lean_dec_ref(v_input_1838_);
v___x_1969_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1890_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_pos_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2018_; 
v_pos_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v___x_1969_, 1);
lean_dec(v_unused_2019_);
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_2018_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_pos_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2018_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_fst_1974_; lean_object* v_snd_1975_; uint8_t v___y_1977_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v_fst_1974_ = lean_ctor_get(v_pos_1970_, 0);
v_snd_1975_ = lean_ctor_get(v_pos_1970_, 1);
v___x_2016_ = lean_string_utf8_byte_size(v_fst_1974_);
v___x_2017_ = lean_nat_dec_eq(v_snd_1975_, v___x_2016_);
if (v___x_2017_ == 0)
{
v___y_1977_ = v___x_1912_;
goto v___jp_1976_;
}
else
{
v___y_1977_ = v___x_1910_;
goto v___jp_1976_;
}
v___jp_1976_:
{
if (v___y_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1978_ = lean_box(0);
if (v_isShared_1973_ == 0)
{
lean_ctor_set_tag(v___x_1972_, 1);
lean_ctor_set(v___x_1972_, 1, v___x_1978_);
v___x_1980_ = v___x_1972_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_pos_1970_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
else
{
lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2013_; 
lean_inc(v_snd_1975_);
lean_inc(v_fst_1974_);
lean_del_object(v___x_1972_);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_pos_1970_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; lean_object* v_unused_2015_; 
v_unused_2014_ = lean_ctor_get(v_pos_1970_, 1);
lean_dec(v_unused_2014_);
v_unused_2015_ = lean_ctor_get(v_pos_1970_, 0);
lean_dec(v_unused_2015_);
v___x_1983_ = v_pos_1970_;
v_isShared_1984_ = v_isSharedCheck_2013_;
goto v_resetjp_1982_;
}
else
{
lean_dec(v_pos_1970_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2013_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_string_utf8_next_fast(v_fst_1974_, v_snd_1975_);
lean_dec(v_snd_1975_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 1, v___x_1985_);
v___x_1987_ = v___x_1983_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_fst_1974_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_2012_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; 
v___x_1988_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1987_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_pos_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2001_; 
v_pos_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; 
v_unused_2002_ = lean_ctor_get(v___x_1988_, 1);
lean_dec(v_unused_2002_);
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2001_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_pos_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2001_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_fst_1993_; lean_object* v_snd_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v_fst_1993_ = lean_ctor_get(v_pos_1989_, 0);
v_snd_1994_ = lean_ctor_get(v_pos_1989_, 1);
v___x_1995_ = lean_string_utf8_byte_size(v_fst_1993_);
v___x_1996_ = lean_nat_dec_eq(v_snd_1994_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_inc(v_snd_1994_);
lean_inc(v_fst_1993_);
lean_del_object(v___x_1991_);
lean_dec(v_pos_1989_);
v___y_1841_ = v_snd_1994_;
v___y_1842_ = v_fst_1993_;
goto v___jp_1840_;
}
else
{
if (v___x_1910_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1997_ = lean_box(0);
if (v_isShared_1992_ == 0)
{
lean_ctor_set_tag(v___x_1991_, 1);
lean_ctor_set(v___x_1991_, 1, v___x_1997_);
v___x_1999_ = v___x_1991_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_pos_1989_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
else
{
lean_inc(v_snd_1994_);
lean_inc(v_fst_1993_);
lean_del_object(v___x_1991_);
lean_dec(v_pos_1989_);
v___y_1841_ = v_snd_1994_;
v___y_1842_ = v_fst_1993_;
goto v___jp_1840_;
}
}
}
}
else
{
lean_object* v_pos_2003_; lean_object* v_err_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_pos_2003_ = lean_ctor_get(v___x_1988_, 0);
v_err_2004_ = lean_ctor_get(v___x_1988_, 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1988_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_err_2004_);
lean_inc(v_pos_2003_);
lean_dec(v___x_1988_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_pos_2003_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_err_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
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
lean_object* v_pos_2020_; lean_object* v_err_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
v_pos_2020_ = lean_ctor_get(v___x_1969_, 0);
v_err_2021_ = lean_ctor_get(v___x_1969_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_1969_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_err_2021_);
lean_inc(v_pos_2020_);
lean_dec(v___x_1969_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_pos_2020_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_err_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
else
{
lean_object* v___x_2029_; 
lean_del_object(v___x_1879_);
lean_dec(v_res_1877_);
lean_dec_ref(v_input_1838_);
v___x_2029_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(v___x_1890_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_pos_2030_; lean_object* v_res_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2189_; 
v_pos_2030_ = lean_ctor_get(v___x_2029_, 0);
v_res_2031_ = lean_ctor_get(v___x_2029_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2033_ = v___x_2029_;
v_isShared_2034_ = v_isSharedCheck_2189_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_res_2031_);
lean_inc(v_pos_2030_);
lean_dec(v___x_2029_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2189_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v_fst_2040_; lean_object* v_snd_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v_fst_2040_ = lean_ctor_get(v_pos_2030_, 0);
v_snd_2041_ = lean_ctor_get(v_pos_2030_, 1);
v___x_2042_ = lean_string_utf8_byte_size(v_fst_2040_);
v___x_2043_ = lean_nat_dec_eq(v_snd_2041_, v___x_2042_);
if (v___x_2043_ == 0)
{
if (v___x_1910_ == 0)
{
lean_dec(v_res_2031_);
goto v___jp_2035_;
}
else
{
lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2186_; 
lean_inc(v_snd_2041_);
lean_inc(v_fst_2040_);
lean_del_object(v___x_2033_);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_pos_2030_);
if (v_isSharedCheck_2186_ == 0)
{
lean_object* v_unused_2187_; lean_object* v_unused_2188_; 
v_unused_2187_ = lean_ctor_get(v_pos_2030_, 1);
lean_dec(v_unused_2187_);
v_unused_2188_ = lean_ctor_get(v_pos_2030_, 0);
lean_dec(v_unused_2188_);
v___x_2045_ = v_pos_2030_;
v_isShared_2046_ = v_isSharedCheck_2186_;
goto v_resetjp_2044_;
}
else
{
lean_dec(v_pos_2030_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2186_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = lean_string_utf8_next_fast(v_fst_2040_, v_snd_2041_);
lean_dec(v_snd_2041_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 1, v___x_2047_);
v___x_2049_ = v___x_2045_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_fst_2040_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; 
v___x_2050_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_pos_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2174_; 
v_pos_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; 
v_unused_2175_ = lean_ctor_get(v___x_2050_, 1);
lean_dec(v_unused_2175_);
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2174_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_pos_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2174_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v_fst_2055_; lean_object* v_snd_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_fst_2055_ = lean_ctor_get(v_pos_2051_, 0);
v_snd_2056_ = lean_ctor_get(v_pos_2051_, 1);
v___x_2057_ = lean_string_utf8_byte_size(v_fst_2055_);
v___x_2058_ = lean_nat_dec_eq(v_snd_2056_, v___x_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2167_; 
lean_inc(v_snd_2056_);
lean_inc(v_fst_2055_);
lean_del_object(v___x_2053_);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_pos_2051_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; lean_object* v_unused_2169_; 
v_unused_2168_ = lean_ctor_get(v_pos_2051_, 1);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_pos_2051_, 0);
lean_dec(v_unused_2169_);
v___x_2060_ = v_pos_2051_;
v_isShared_2061_ = v_isSharedCheck_2167_;
goto v_resetjp_2059_;
}
else
{
lean_dec(v_pos_2051_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2167_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2062_ = lean_string_utf8_next_fast(v_fst_2055_, v_snd_2056_);
lean_dec(v_snd_2056_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v___x_2062_);
v___x_2064_ = v___x_2060_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_fst_2055_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; 
v___x_2065_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2064_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_pos_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2155_; 
v_pos_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v___x_2065_, 1);
lean_dec(v_unused_2156_);
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2155_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_pos_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2155_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_fst_2070_; lean_object* v_snd_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_fst_2070_ = lean_ctor_get(v_pos_2066_, 0);
v_snd_2071_ = lean_ctor_get(v_pos_2066_, 1);
v___x_2072_ = lean_string_utf8_byte_size(v_fst_2070_);
v___x_2073_ = lean_nat_dec_eq(v_snd_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2148_; 
lean_inc(v_snd_2071_);
lean_inc(v_fst_2070_);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_pos_2066_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; lean_object* v_unused_2150_; 
v_unused_2149_ = lean_ctor_get(v_pos_2066_, 1);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_pos_2066_, 0);
lean_dec(v_unused_2150_);
v___x_2075_ = v_pos_2066_;
v_isShared_2076_ = v_isSharedCheck_2148_;
goto v_resetjp_2074_;
}
else
{
lean_dec(v_pos_2066_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2148_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2077_ = lean_string_utf8_next_fast(v_fst_2070_, v_snd_2071_);
lean_dec(v_snd_2071_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 1, v___x_2077_);
v___x_2079_ = v___x_2075_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_fst_2070_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; 
v___x_2080_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2079_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_pos_2081_; lean_object* v_res_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2137_; 
v_pos_2081_ = lean_ctor_get(v___x_2080_, 0);
v_res_2082_ = lean_ctor_get(v___x_2080_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2084_ = v___x_2080_;
v_isShared_2085_ = v_isSharedCheck_2137_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_res_2082_);
lean_inc(v_pos_2081_);
lean_dec(v___x_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2137_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2092_ = lean_string_dec_eq(v_res_2082_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
lean_del_object(v___x_2084_);
v___x_2093_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2094_ = lean_string_dec_eq(v_res_2082_, v___x_2093_);
lean_dec(v_res_2082_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
lean_dec(v_res_2031_);
v___x_2095_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5));
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 1);
lean_ctor_set(v___x_2068_, 1, v___x_2095_);
lean_ctor_set(v___x_2068_, 0, v_pos_2081_);
v___x_2097_ = v___x_2068_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_pos_2081_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2099_, 0, v_res_2031_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v___x_2099_);
lean_ctor_set(v___x_2068_, 0, v_pos_2081_);
v___x_2101_ = v___x_2068_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_pos_2081_);
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
lean_object* v_fst_2103_; lean_object* v_snd_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
lean_dec(v_res_2082_);
lean_del_object(v___x_2068_);
v_fst_2103_ = lean_ctor_get(v_pos_2081_, 0);
v_snd_2104_ = lean_ctor_get(v_pos_2081_, 1);
v___x_2105_ = lean_string_utf8_byte_size(v_fst_2103_);
v___x_2106_ = lean_nat_dec_eq(v_snd_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
if (v___x_2092_ == 0)
{
lean_dec(v_res_2031_);
goto v___jp_2086_;
}
else
{
lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2134_; 
lean_inc(v_snd_2104_);
lean_inc(v_fst_2103_);
lean_del_object(v___x_2084_);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_pos_2081_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; lean_object* v_unused_2136_; 
v_unused_2135_ = lean_ctor_get(v_pos_2081_, 1);
lean_dec(v_unused_2135_);
v_unused_2136_ = lean_ctor_get(v_pos_2081_, 0);
lean_dec(v_unused_2136_);
v___x_2108_ = v_pos_2081_;
v_isShared_2109_ = v_isSharedCheck_2134_;
goto v_resetjp_2107_;
}
else
{
lean_dec(v_pos_2081_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2134_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = lean_string_utf8_next_fast(v_fst_2103_, v_snd_2104_);
lean_dec(v_snd_2104_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 1, v___x_2110_);
v___x_2112_ = v___x_2108_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_fst_2103_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; 
v___x_2113_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2112_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_pos_2114_; lean_object* v_res_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2123_; 
v_pos_2114_ = lean_ctor_get(v___x_2113_, 0);
v_res_2115_ = lean_ctor_get(v___x_2113_, 1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2117_ = v___x_2113_;
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_res_2115_);
lean_inc(v_pos_2114_);
lean_dec(v___x_2113_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v_res_2031_);
lean_ctor_set(v___x_2119_, 1, v_res_2115_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 1, v___x_2119_);
v___x_2121_ = v___x_2117_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_pos_2114_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
else
{
lean_object* v_pos_2124_; lean_object* v_err_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_res_2031_);
v_pos_2124_ = lean_ctor_get(v___x_2113_, 0);
v_err_2125_ = lean_ctor_get(v___x_2113_, 1);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2113_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_err_2125_);
lean_inc(v_pos_2124_);
lean_dec(v___x_2113_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_pos_2124_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_err_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2031_);
goto v___jp_2086_;
}
}
v___jp_2086_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = lean_box(0);
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 1);
lean_ctor_set(v___x_2084_, 1, v___x_2087_);
v___x_2089_ = v___x_2084_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_pos_2081_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
lean_object* v_pos_2138_; lean_object* v_err_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_del_object(v___x_2068_);
lean_dec(v_res_2031_);
v_pos_2138_ = lean_ctor_get(v___x_2080_, 0);
v_err_2139_ = lean_ctor_get(v___x_2080_, 1);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2080_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_err_2139_);
lean_inc(v_pos_2138_);
lean_dec(v___x_2080_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_pos_2138_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_err_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
lean_dec(v_res_2031_);
v___x_2151_ = lean_box(0);
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 1);
lean_ctor_set(v___x_2068_, 1, v___x_2151_);
v___x_2153_ = v___x_2068_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_pos_2066_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_pos_2157_; lean_object* v_err_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_res_2031_);
v_pos_2157_ = lean_ctor_get(v___x_2065_, 0);
v_err_2158_ = lean_ctor_get(v___x_2065_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2065_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_err_2158_);
lean_inc(v_pos_2157_);
lean_dec(v___x_2065_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_pos_2157_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_err_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
lean_dec(v_res_2031_);
v___x_2170_ = lean_box(0);
if (v_isShared_2054_ == 0)
{
lean_ctor_set_tag(v___x_2053_, 1);
lean_ctor_set(v___x_2053_, 1, v___x_2170_);
v___x_2172_ = v___x_2053_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_pos_2051_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_pos_2176_; lean_object* v_err_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_res_2031_);
v_pos_2176_ = lean_ctor_get(v___x_2050_, 0);
v_err_2177_ = lean_ctor_get(v___x_2050_, 1);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2050_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_err_2177_);
lean_inc(v_pos_2176_);
lean_dec(v___x_2050_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_pos_2176_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_err_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2031_);
goto v___jp_2035_;
}
v___jp_2035_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = lean_box(0);
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 1);
lean_ctor_set(v___x_2033_, 1, v___x_2036_);
v___x_2038_ = v___x_2033_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_pos_2030_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
lean_object* v_pos_2190_; lean_object* v_err_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
v_pos_2190_ = lean_ctor_get(v___x_2029_, 0);
v_err_2191_ = lean_ctor_get(v___x_2029_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2029_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_err_2191_);
lean_inc(v_pos_2190_);
lean_dec(v___x_2029_);
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
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_pos_2190_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_err_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
v___jp_1891_:
{
lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1896_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1896_, 0, v_id_1892_);
lean_ctor_set(v___x_1896_, 1, v_message_1894_);
lean_ctor_set(v___x_1896_, 2, v_data_x3f_1895_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3, v_code_1893_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1896_);
lean_ctor_set(v___x_1879_, 0, v___x_1890_);
v___x_1898_ = v___x_1879_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
v___jp_1900_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1));
v___x_1902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1890_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
return v___x_1902_;
}
v___jp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_a_1904_);
v___x_1906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1890_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
return v___x_1906_;
}
v___jp_1907_:
{
lean_object* v___x_1908_; 
v___x_1908_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_1904_ = v___x_1908_;
goto v___jp_1903_;
}
}
}
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
lean_dec(v_res_1877_);
lean_dec_ref(v_input_1838_);
v___x_2203_ = lean_box(0);
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 1);
lean_ctor_set(v___x_1879_, 1, v___x_2203_);
v___x_2205_ = v___x_1879_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_pos_1876_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v___x_2203_);
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
else
{
lean_object* v_pos_2208_; lean_object* v_err_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec_ref(v_input_1838_);
v_pos_2208_ = lean_ctor_get(v___x_1875_, 0);
v_err_2209_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_1875_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_err_2209_);
lean_inc(v_pos_2208_);
lean_dec(v___x_1875_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_pos_2208_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_err_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec_ref(v_input_1838_);
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_a_1839_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
return v___x_2222_;
}
v___jp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_string_utf8_next_fast(v___y_1842_, v___y_1841_);
lean_dec(v___y_1841_);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___y_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1844_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_pos_1846_; lean_object* v_res_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1855_; 
v_pos_1846_ = lean_ctor_get(v___x_1845_, 0);
v_res_1847_ = lean_ctor_get(v___x_1845_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1849_ = v___x_1845_;
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_res_1847_);
lean_inc(v_pos_1846_);
lean_dec(v___x_1845_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1855_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_res_1847_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v___x_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_pos_1846_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_object* v_pos_1856_; lean_object* v_err_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
v_pos_1856_ = lean_ctor_get(v___x_1845_, 0);
v_err_1857_ = lean_ctor_get(v___x_1845_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1845_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_err_1857_);
lean_inc(v_pos_1856_);
lean_dec(v___x_1845_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_pos_1856_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_err_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object* v_input_2223_){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_inc_ref(v_input_2223_);
v___x_2224_ = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser), 2, 1);
lean_closure_set(v___x_2224_, 0, v_input_2223_);
v___x_2225_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2224_, v_input_2223_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx(uint8_t v_x_2226_){
_start:
{
if (v_x_2226_ == 0)
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_unsigned_to_nat(0u);
return v___x_2227_;
}
else
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_unsigned_to_nat(1u);
return v___x_2228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___boxed(lean_object* v_x_2229_){
_start:
{
uint8_t v_x_boxed_2230_; lean_object* v_res_2231_; 
v_x_boxed_2230_ = lean_unbox(v_x_2229_);
v_res_2231_ = l_Lean_JsonRpc_MessageDirection_ctorIdx(v_x_boxed_2230_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx(uint8_t v_x_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_JsonRpc_MessageDirection_ctorIdx(v_x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx___boxed(lean_object* v_x_2234_){
_start:
{
uint8_t v_x_4__boxed_2235_; lean_object* v_res_2236_; 
v_x_4__boxed_2235_ = lean_unbox(v_x_2234_);
v_res_2236_ = l_Lean_JsonRpc_MessageDirection_toCtorIdx(v_x_4__boxed_2235_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object* v_k_2237_){
_start:
{
lean_inc(v_k_2237_);
return v_k_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object* v_k_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(v_k_2238_);
lean_dec(v_k_2238_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object* v_motive_2240_, lean_object* v_ctorIdx_2241_, uint8_t v_t_2242_, lean_object* v_h_2243_, lean_object* v_k_2244_){
_start:
{
lean_inc(v_k_2244_);
return v_k_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object* v_motive_2245_, lean_object* v_ctorIdx_2246_, lean_object* v_t_2247_, lean_object* v_h_2248_, lean_object* v_k_2249_){
_start:
{
uint8_t v_t_boxed_2250_; lean_object* v_res_2251_; 
v_t_boxed_2250_ = lean_unbox(v_t_2247_);
v_res_2251_ = l_Lean_JsonRpc_MessageDirection_ctorElim(v_motive_2245_, v_ctorIdx_2246_, v_t_boxed_2250_, v_h_2248_, v_k_2249_);
lean_dec(v_k_2249_);
lean_dec(v_ctorIdx_2246_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object* v_clientToServer_2252_){
_start:
{
lean_inc(v_clientToServer_2252_);
return v_clientToServer_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object* v_clientToServer_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(v_clientToServer_2253_);
lean_dec(v_clientToServer_2253_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object* v_motive_2255_, uint8_t v_t_2256_, lean_object* v_h_2257_, lean_object* v_clientToServer_2258_){
_start:
{
lean_inc(v_clientToServer_2258_);
return v_clientToServer_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object* v_motive_2259_, lean_object* v_t_2260_, lean_object* v_h_2261_, lean_object* v_clientToServer_2262_){
_start:
{
uint8_t v_t_boxed_2263_; lean_object* v_res_2264_; 
v_t_boxed_2263_ = lean_unbox(v_t_2260_);
v_res_2264_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(v_motive_2259_, v_t_boxed_2263_, v_h_2261_, v_clientToServer_2262_);
lean_dec(v_clientToServer_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object* v_serverToClient_2265_){
_start:
{
lean_inc(v_serverToClient_2265_);
return v_serverToClient_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object* v_serverToClient_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(v_serverToClient_2266_);
lean_dec(v_serverToClient_2266_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object* v_motive_2268_, uint8_t v_t_2269_, lean_object* v_h_2270_, lean_object* v_serverToClient_2271_){
_start:
{
lean_inc(v_serverToClient_2271_);
return v_serverToClient_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object* v_motive_2272_, lean_object* v_t_2273_, lean_object* v_h_2274_, lean_object* v_serverToClient_2275_){
_start:
{
uint8_t v_t_boxed_2276_; lean_object* v_res_2277_; 
v_t_boxed_2276_ = lean_unbox(v_t_2273_);
v_res_2277_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(v_motive_2272_, v_t_boxed_2276_, v_h_2274_, v_serverToClient_2275_);
lean_dec(v_serverToClient_2275_);
return v_res_2277_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default(void){
_start:
{
uint8_t v___x_2278_; 
v___x_2278_ = 0;
return v___x_2278_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection(void){
_start:
{
uint8_t v___x_2279_; 
v___x_2279_ = 0;
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object* v_json_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Json_getTag_x3f(v_json_2294_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v___x_2296_; 
v___x_2296_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1));
return v___x_2296_;
}
else
{
lean_object* v_val_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v_val_2297_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_val_2297_);
lean_dec_ref(v___x_2295_);
v___x_2298_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2));
v___x_2299_ = lean_string_dec_eq(v_val_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3));
v___x_2301_ = lean_string_dec_eq(v_val_2297_, v___x_2300_);
lean_dec(v_val_2297_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; 
v___x_2302_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5));
return v___x_2302_;
}
else
{
lean_object* v___x_2303_; 
v___x_2303_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6));
return v___x_2303_;
}
}
else
{
lean_object* v___x_2304_; 
lean_dec(v_val_2297_);
v___x_2304_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7));
return v___x_2304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t v_x_2311_){
_start:
{
if (v_x_2311_ == 0)
{
lean_object* v___x_2312_; 
v___x_2312_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0));
return v___x_2312_;
}
else
{
lean_object* v___x_2313_; 
v___x_2313_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1));
return v___x_2313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object* v_x_2314_){
_start:
{
uint8_t v_x_44__boxed_2315_; lean_object* v_res_2316_; 
v_x_44__boxed_2315_ = lean_unbox(v_x_2314_);
v_res_2316_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_x_44__boxed_2315_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx(uint8_t v_x_2319_){
_start:
{
switch(v_x_2319_)
{
case 0:
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_unsigned_to_nat(0u);
return v___x_2320_;
}
case 1:
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_unsigned_to_nat(1u);
return v___x_2321_;
}
case 2:
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_unsigned_to_nat(2u);
return v___x_2322_;
}
default: 
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_unsigned_to_nat(3u);
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___boxed(lean_object* v_x_2324_){
_start:
{
uint8_t v_x_boxed_2325_; lean_object* v_res_2326_; 
v_x_boxed_2325_ = lean_unbox(v_x_2324_);
v_res_2326_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_boxed_2325_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx(uint8_t v_x_2327_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx___boxed(lean_object* v_x_2329_){
_start:
{
uint8_t v_x_4__boxed_2330_; lean_object* v_res_2331_; 
v_x_4__boxed_2330_ = lean_unbox(v_x_2329_);
v_res_2331_ = l_Lean_JsonRpc_MessageKind_toCtorIdx(v_x_4__boxed_2330_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object* v_k_2332_){
_start:
{
lean_inc(v_k_2332_);
return v_k_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object* v_k_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_JsonRpc_MessageKind_ctorElim___redArg(v_k_2333_);
lean_dec(v_k_2333_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object* v_motive_2335_, lean_object* v_ctorIdx_2336_, uint8_t v_t_2337_, lean_object* v_h_2338_, lean_object* v_k_2339_){
_start:
{
lean_inc(v_k_2339_);
return v_k_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object* v_motive_2340_, lean_object* v_ctorIdx_2341_, lean_object* v_t_2342_, lean_object* v_h_2343_, lean_object* v_k_2344_){
_start:
{
uint8_t v_t_boxed_2345_; lean_object* v_res_2346_; 
v_t_boxed_2345_ = lean_unbox(v_t_2342_);
v_res_2346_ = l_Lean_JsonRpc_MessageKind_ctorElim(v_motive_2340_, v_ctorIdx_2341_, v_t_boxed_2345_, v_h_2343_, v_k_2344_);
lean_dec(v_k_2344_);
lean_dec(v_ctorIdx_2341_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object* v_request_2347_){
_start:
{
lean_inc(v_request_2347_);
return v_request_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object* v_request_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_JsonRpc_MessageKind_request_elim___redArg(v_request_2348_);
lean_dec(v_request_2348_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object* v_motive_2350_, uint8_t v_t_2351_, lean_object* v_h_2352_, lean_object* v_request_2353_){
_start:
{
lean_inc(v_request_2353_);
return v_request_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object* v_motive_2354_, lean_object* v_t_2355_, lean_object* v_h_2356_, lean_object* v_request_2357_){
_start:
{
uint8_t v_t_boxed_2358_; lean_object* v_res_2359_; 
v_t_boxed_2358_ = lean_unbox(v_t_2355_);
v_res_2359_ = l_Lean_JsonRpc_MessageKind_request_elim(v_motive_2354_, v_t_boxed_2358_, v_h_2356_, v_request_2357_);
lean_dec(v_request_2357_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object* v_notification_2360_){
_start:
{
lean_inc(v_notification_2360_);
return v_notification_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object* v_notification_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_JsonRpc_MessageKind_notification_elim___redArg(v_notification_2361_);
lean_dec(v_notification_2361_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object* v_motive_2363_, uint8_t v_t_2364_, lean_object* v_h_2365_, lean_object* v_notification_2366_){
_start:
{
lean_inc(v_notification_2366_);
return v_notification_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object* v_motive_2367_, lean_object* v_t_2368_, lean_object* v_h_2369_, lean_object* v_notification_2370_){
_start:
{
uint8_t v_t_boxed_2371_; lean_object* v_res_2372_; 
v_t_boxed_2371_ = lean_unbox(v_t_2368_);
v_res_2372_ = l_Lean_JsonRpc_MessageKind_notification_elim(v_motive_2367_, v_t_boxed_2371_, v_h_2369_, v_notification_2370_);
lean_dec(v_notification_2370_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object* v_response_2373_){
_start:
{
lean_inc(v_response_2373_);
return v_response_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object* v_response_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_JsonRpc_MessageKind_response_elim___redArg(v_response_2374_);
lean_dec(v_response_2374_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object* v_motive_2376_, uint8_t v_t_2377_, lean_object* v_h_2378_, lean_object* v_response_2379_){
_start:
{
lean_inc(v_response_2379_);
return v_response_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object* v_motive_2380_, lean_object* v_t_2381_, lean_object* v_h_2382_, lean_object* v_response_2383_){
_start:
{
uint8_t v_t_boxed_2384_; lean_object* v_res_2385_; 
v_t_boxed_2384_ = lean_unbox(v_t_2381_);
v_res_2385_ = l_Lean_JsonRpc_MessageKind_response_elim(v_motive_2380_, v_t_boxed_2384_, v_h_2382_, v_response_2383_);
lean_dec(v_response_2383_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object* v_responseError_2386_){
_start:
{
lean_inc(v_responseError_2386_);
return v_responseError_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object* v_responseError_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(v_responseError_2387_);
lean_dec(v_responseError_2387_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object* v_motive_2389_, uint8_t v_t_2390_, lean_object* v_h_2391_, lean_object* v_responseError_2392_){
_start:
{
lean_inc(v_responseError_2392_);
return v_responseError_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object* v_motive_2393_, lean_object* v_t_2394_, lean_object* v_h_2395_, lean_object* v_responseError_2396_){
_start:
{
uint8_t v_t_boxed_2397_; lean_object* v_res_2398_; 
v_t_boxed_2397_ = lean_unbox(v_t_2394_);
v_res_2398_ = l_Lean_JsonRpc_MessageKind_responseError_elim(v_motive_2393_, v_t_boxed_2397_, v_h_2395_, v_responseError_2396_);
lean_dec(v_responseError_2396_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object* v_json_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Json_getTag_x3f(v_json_2419_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v___x_2421_; 
v___x_2421_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0));
return v___x_2421_;
}
else
{
lean_object* v_val_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_val_2422_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_val_2422_);
lean_dec_ref(v___x_2420_);
v___x_2423_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1));
v___x_2424_ = lean_string_dec_eq(v_val_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2));
v___x_2426_ = lean_string_dec_eq(v_val_2422_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2427_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3));
v___x_2428_ = lean_string_dec_eq(v_val_2422_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4));
v___x_2430_ = lean_string_dec_eq(v_val_2422_, v___x_2429_);
lean_dec(v_val_2422_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; 
v___x_2431_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5));
return v___x_2431_;
}
else
{
lean_object* v___x_2432_; 
v___x_2432_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6));
return v___x_2432_;
}
}
else
{
lean_object* v___x_2433_; 
lean_dec(v_val_2422_);
v___x_2433_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7));
return v___x_2433_;
}
}
else
{
lean_object* v___x_2434_; 
lean_dec(v_val_2422_);
v___x_2434_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8));
return v___x_2434_;
}
}
else
{
lean_object* v___x_2435_; 
lean_dec(v_val_2422_);
v___x_2435_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9));
return v___x_2435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t v_x_2446_){
_start:
{
switch(v_x_2446_)
{
case 0:
{
lean_object* v___x_2447_; 
v___x_2447_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0));
return v___x_2447_;
}
case 1:
{
lean_object* v___x_2448_; 
v___x_2448_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1));
return v___x_2448_;
}
case 2:
{
lean_object* v___x_2449_; 
v___x_2449_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2));
return v___x_2449_;
}
default: 
{
lean_object* v___x_2450_; 
v___x_2450_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3));
return v___x_2450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object* v_x_2451_){
_start:
{
uint8_t v_x_84__boxed_2452_; lean_object* v_res_2453_; 
v_x_84__boxed_2452_ = lean_unbox(v_x_2451_);
v_res_2453_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_x_84__boxed_2452_);
return v_res_2453_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object* v_x_2456_){
_start:
{
switch(lean_obj_tag(v_x_2456_))
{
case 0:
{
uint8_t v___x_2457_; 
v___x_2457_ = 0;
return v___x_2457_;
}
case 1:
{
uint8_t v___x_2458_; 
v___x_2458_ = 1;
return v___x_2458_;
}
case 2:
{
uint8_t v___x_2459_; 
v___x_2459_ = 2;
return v___x_2459_;
}
default: 
{
uint8_t v___x_2460_; 
v___x_2460_ = 3;
return v___x_2460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object* v_x_2461_){
_start:
{
uint8_t v_res_2462_; lean_object* v_r_2463_; 
v_res_2462_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_x_2461_);
lean_dec_ref(v_x_2461_);
v_r_2463_ = lean_box(v_res_2462_);
return v_r_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(lean_object* v_j_2464_, lean_object* v_k_2465_){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = l_Lean_Json_getObjValD(v_j_2464_, v_k_2465_);
v___x_2467_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2466_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0___boxed(lean_object* v_j_2468_, lean_object* v_k_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(v_j_2468_, v_k_2469_);
lean_dec_ref(v_k_2469_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object* v_h_2473_, lean_object* v_nBytes_2474_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_IO_FS_Stream_readJson(v_h_2473_, v_nBytes_2474_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2596_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2596_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2596_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___y_2482_; lean_object* v___y_2483_; uint8_t v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v_a_2496_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_a_2477_);
v___x_2508_ = l_Lean_Json_getObjVal_x3f(v_a_2477_, v___x_2507_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; 
lean_del_object(v___x_2479_);
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref(v___x_2508_);
v_a_2496_ = v_a_2509_;
goto v___jp_2495_;
}
else
{
lean_object* v_a_2510_; 
v_a_2510_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v___x_2508_);
if (lean_obj_tag(v_a_2510_) == 3)
{
lean_object* v_s_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_s_2511_ = lean_ctor_get(v_a_2510_, 0);
lean_inc_ref(v_s_2511_);
lean_dec_ref(v_a_2510_);
v___x_2512_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_2513_ = lean_string_dec_eq(v_s_2511_, v___x_2512_);
lean_dec_ref(v_s_2511_);
if (v___x_2513_ == 0)
{
lean_del_object(v___x_2479_);
goto v___jp_2505_;
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_a_2477_);
v___x_2515_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_2477_, v___x_2514_);
if (lean_obj_tag(v___x_2515_) == 0)
{
goto v___jp_2544_;
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v_a_2571_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2571_);
v___x_2572_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2477_);
v___x_2573_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2477_, v___x_2572_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_dec_ref(v___x_2573_);
lean_dec(v_a_2571_);
goto v___jp_2544_;
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v___x_2515_);
lean_del_object(v___x_2479_);
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2595_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2595_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___y_2579_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2585_ = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(v_a_2477_, v___x_2584_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v___x_2586_; 
lean_dec_ref(v___x_2585_);
v___x_2586_ = lean_box(0);
v___y_2579_ = v___x_2586_;
goto v___jp_2578_;
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
v_a_2587_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2585_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2585_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
v___y_2579_ = v___x_2592_;
goto v___jp_2578_;
}
}
}
v___jp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2580_, 0, v_a_2571_);
lean_ctor_set(v___x_2580_, 1, v_a_2574_);
lean_ctor_set(v___x_2580_, 2, v___y_2579_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set_tag(v___x_2576_, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2580_);
v___x_2582_ = v___x_2576_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
v___jp_2516_:
{
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2517_; 
lean_del_object(v___x_2479_);
v_a_2517_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2517_);
lean_dec_ref(v___x_2515_);
v_a_2496_ = v_a_2517_;
goto v___jp_2495_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v_a_2518_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2518_);
lean_dec_ref(v___x_2515_);
v___x_2519_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
lean_inc(v_a_2477_);
v___x_2520_ = l_Lean_Json_getObjVal_x3f(v_a_2477_, v___x_2519_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; 
lean_dec(v_a_2518_);
lean_del_object(v___x_2479_);
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref(v___x_2520_);
v_a_2496_ = v_a_2521_;
goto v___jp_2495_;
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_a_2522_ = lean_ctor_get(v___x_2520_, 0);
lean_inc_n(v_a_2522_, 2);
lean_dec_ref(v___x_2520_);
v___x_2523_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_2524_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_2522_, v___x_2523_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; 
lean_dec(v_a_2522_);
lean_dec(v_a_2518_);
lean_del_object(v___x_2479_);
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref(v___x_2524_);
v_a_2496_ = v_a_2525_;
goto v___jp_2495_;
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_a_2526_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2526_);
lean_dec_ref(v___x_2524_);
v___x_2527_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_2522_);
v___x_2528_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2522_, v___x_2527_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; 
lean_dec(v_a_2526_);
lean_dec(v_a_2522_);
lean_dec(v_a_2518_);
lean_del_object(v___x_2479_);
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref(v___x_2528_);
v_a_2496_ = v_a_2529_;
goto v___jp_2495_;
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec(v_a_2477_);
v_a_2530_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2530_);
lean_dec_ref(v___x_2528_);
v___x_2531_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2532_ = l_Lean_Json_getObjVal_x3f(v_a_2522_, v___x_2531_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v___x_2533_; uint8_t v___x_2534_; 
lean_dec_ref(v___x_2532_);
v___x_2533_ = lean_box(0);
v___x_2534_ = lean_unbox(v_a_2526_);
lean_dec(v_a_2526_);
v___y_2482_ = v_a_2530_;
v___y_2483_ = v_a_2518_;
v___y_2484_ = v___x_2534_;
v___y_2485_ = v___x_2533_;
goto v___jp_2481_;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2543_; 
v_a_2535_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2537_ = v___x_2532_;
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2532_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2543_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_unbox(v_a_2526_);
lean_dec(v_a_2526_);
v___y_2482_ = v_a_2530_;
v___y_2483_ = v_a_2518_;
v___y_2484_ = v___x_2541_;
v___y_2485_ = v___x_2540_;
goto v___jp_2481_;
}
}
}
}
}
}
}
}
v___jp_2544_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2477_);
v___x_2546_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2477_, v___x_2545_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_dec_ref(v___x_2546_);
if (lean_obj_tag(v___x_2515_) == 0)
{
goto v___jp_2516_;
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v_a_2547_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2547_);
v___x_2548_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_2477_);
v___x_2549_ = l_Lean_Json_getObjVal_x3f(v_a_2477_, v___x_2548_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_dec_ref(v___x_2549_);
lean_dec(v_a_2547_);
goto v___jp_2516_;
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2558_; 
lean_dec_ref(v___x_2515_);
lean_del_object(v___x_2479_);
lean_dec(v_a_2477_);
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2558_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2554_, 0, v_a_2547_);
lean_ctor_set(v___x_2554_, 1, v_a_2550_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set_tag(v___x_2552_, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2554_);
v___x_2556_ = v___x_2552_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
lean_dec_ref(v___x_2515_);
lean_del_object(v___x_2479_);
v_a_2559_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2559_);
lean_dec_ref(v___x_2546_);
v___x_2560_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2561_ = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(v_a_2477_, v___x_2560_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v___x_2562_; 
lean_dec_ref(v___x_2561_);
v___x_2562_ = lean_box(0);
v___y_2491_ = v_a_2559_;
v___y_2492_ = v___x_2562_;
goto v___jp_2490_;
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_a_2563_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2561_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2561_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
v___y_2491_ = v_a_2559_;
v___y_2492_ = v___x_2568_;
goto v___jp_2490_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2510_);
lean_del_object(v___x_2479_);
goto v___jp_2505_;
}
}
v___jp_2481_:
{
lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2486_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2486_, 0, v___y_2483_);
lean_ctor_set(v___x_2486_, 1, v___y_2482_);
lean_ctor_set(v___x_2486_, 2, v___y_2485_);
lean_ctor_set_uint8(v___x_2486_, sizeof(void*)*3, v___y_2484_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v___x_2486_);
v___x_2488_ = v___x_2479_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
v___jp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___y_2491_);
lean_ctor_set(v___x_2493_, 1, v___y_2492_);
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
v___jp_2495_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2497_ = ((lean_object*)(l_IO_FS_Stream_readMessage___closed__0));
v___x_2498_ = l_Lean_Json_compress(v_a_2477_);
v___x_2499_ = lean_string_append(v___x_2497_, v___x_2498_);
lean_dec_ref(v___x_2498_);
v___x_2500_ = ((lean_object*)(l_IO_FS_Stream_readMessage___closed__1));
v___x_2501_ = lean_string_append(v___x_2499_, v___x_2500_);
v___x_2502_ = lean_string_append(v___x_2501_, v_a_2496_);
lean_dec_ref(v_a_2496_);
v___x_2503_ = lean_mk_io_user_error(v___x_2502_);
v___x_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
v___jp_2505_:
{
lean_object* v___x_2506_; 
v___x_2506_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_2496_ = v___x_2506_;
goto v___jp_2495_;
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
v_a_2597_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2476_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2476_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object* v_h_2605_, lean_object* v_nBytes_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_IO_FS_Stream_readMessage(v_h_2605_, v_nBytes_2606_);
lean_dec(v_nBytes_2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object* v_h_2616_, lean_object* v_nBytes_2617_, lean_object* v_expectedMethod_2618_, lean_object* v_inst_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_IO_FS_Stream_readMessage(v_h_2616_, v_nBytes_2617_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2809_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2809_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2809_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
if (lean_obj_tag(v_a_2622_) == 0)
{
lean_object* v_id_2626_; lean_object* v_method_2627_; lean_object* v_params_x3f_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2668_; 
v_id_2626_ = lean_ctor_get(v_a_2622_, 0);
v_method_2627_ = lean_ctor_get(v_a_2622_, 1);
v_params_x3f_2628_ = lean_ctor_get(v_a_2622_, 2);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_a_2622_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2630_ = v_a_2622_;
v_isShared_2631_ = v_isSharedCheck_2668_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_params_x3f_2628_);
lean_inc(v_method_2627_);
lean_inc(v_id_2626_);
lean_dec(v_a_2622_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2668_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
uint8_t v___x_2632_; 
v___x_2632_ = lean_string_dec_eq(v_method_2627_, v_expectedMethod_2618_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2642_; 
lean_del_object(v___x_2630_);
lean_dec(v_params_x3f_2628_);
lean_dec(v_id_2626_);
lean_dec_ref(v_inst_2619_);
v___x_2633_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2634_ = lean_string_append(v___x_2633_, v_expectedMethod_2618_);
lean_dec_ref(v_expectedMethod_2618_);
v___x_2635_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2636_ = lean_string_append(v___x_2634_, v___x_2635_);
v___x_2637_ = lean_string_append(v___x_2636_, v_method_2627_);
lean_dec_ref(v_method_2627_);
v___x_2638_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2639_ = lean_string_append(v___x_2637_, v___x_2638_);
v___x_2640_ = lean_mk_io_user_error(v___x_2639_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 1);
lean_ctor_set(v___x_2624_, 0, v___x_2640_);
v___x_2642_ = v___x_2624_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2640_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_dec_ref(v_method_2627_);
v___x_2644_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2645_ = l_Option_toJson___redArg(v___x_2644_, v_params_x3f_2628_);
lean_inc(v___x_2645_);
v___x_2646_ = lean_apply_1(v_inst_2619_, v___x_2645_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2659_; 
lean_del_object(v___x_2630_);
lean_dec(v_id_2626_);
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref(v___x_2646_);
v___x_2648_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2649_ = l_Lean_Json_compress(v___x_2645_);
v___x_2650_ = lean_string_append(v___x_2648_, v___x_2649_);
lean_dec_ref(v___x_2649_);
v___x_2651_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2652_ = lean_string_append(v___x_2650_, v___x_2651_);
v___x_2653_ = lean_string_append(v___x_2652_, v_expectedMethod_2618_);
lean_dec_ref(v_expectedMethod_2618_);
v___x_2654_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2655_ = lean_string_append(v___x_2653_, v___x_2654_);
v___x_2656_ = lean_string_append(v___x_2655_, v_a_2647_);
lean_dec(v_a_2647_);
v___x_2657_ = lean_mk_io_user_error(v___x_2656_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 1);
lean_ctor_set(v___x_2624_, 0, v___x_2657_);
v___x_2659_ = v___x_2624_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; 
lean_dec(v___x_2645_);
v_a_2661_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2661_);
lean_dec_ref(v___x_2646_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 2, v_a_2661_);
lean_ctor_set(v___x_2630_, 1, v_expectedMethod_2618_);
v___x_2663_ = v___x_2630_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_id_2626_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_expectedMethod_2618_);
lean_ctor_set(v_reuseFailAlloc_2667_, 2, v_a_2661_);
v___x_2663_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2665_; 
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2663_);
v___x_2665_ = v___x_2624_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
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
}
else
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___y_2673_; 
lean_dec_ref(v_inst_2619_);
lean_dec_ref(v_expectedMethod_2618_);
v___x_2669_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__6));
v___x_2670_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2671_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2622_))
{
case 0:
{
lean_object* v_id_2684_; lean_object* v_method_2685_; lean_object* v_params_x3f_2686_; lean_object* v___x_2687_; lean_object* v___y_2689_; 
v_id_2684_ = lean_ctor_get(v_a_2622_, 0);
lean_inc(v_id_2684_);
v_method_2685_ = lean_ctor_get(v_a_2622_, 1);
lean_inc_ref(v_method_2685_);
v_params_x3f_2686_ = lean_ctor_get(v_a_2622_, 2);
lean_inc(v_params_x3f_2686_);
lean_dec_ref(v_a_2622_);
v___x_2687_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2684_) == 0)
{
lean_object* v_s_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
v_s_2700_ = lean_ctor_get(v_id_2684_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_id_2684_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v_id_2684_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_s_2700_);
lean_dec(v_id_2684_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
lean_ctor_set_tag(v___x_2702_, 3);
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_s_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
v___y_2689_ = v___x_2705_;
goto v___jp_2688_;
}
}
}
else
{
lean_object* v_n_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
v_n_2708_ = lean_ctor_get(v_id_2684_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_id_2684_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v_id_2684_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_n_2708_);
lean_dec(v_id_2684_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set_tag(v___x_2710_, 2);
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_n_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
v___y_2689_ = v___x_2713_;
goto v___jp_2688_;
}
}
}
v___jp_2688_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2687_);
lean_ctor_set(v___x_2690_, 1, v___y_2689_);
v___x_2691_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2692_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_method_2685_);
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2690_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2698_ = l_Lean_Json_opt___redArg(v___x_2670_, v___x_2697_, v_params_x3f_2686_);
v___x_2699_ = l_List_appendTR___redArg(v___x_2696_, v___x_2698_);
v___y_2673_ = v___x_2699_;
goto v___jp_2672_;
}
}
case 1:
{
lean_object* v_method_2716_; lean_object* v_params_x3f_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v_method_2716_ = lean_ctor_get(v_a_2622_, 0);
lean_inc_ref(v_method_2716_);
v_params_x3f_2717_ = lean_ctor_get(v_a_2622_, 1);
lean_inc(v_params_x3f_2717_);
lean_dec_ref(v_a_2622_);
v___x_2718_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2719_, 0, v_method_2716_);
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2718_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2722_ = l_Lean_Json_opt___redArg(v___x_2670_, v___x_2721_, v_params_x3f_2717_);
v___x_2723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2720_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___y_2673_ = v___x_2723_;
goto v___jp_2672_;
}
case 2:
{
lean_object* v_id_2724_; lean_object* v_result_2725_; lean_object* v___x_2726_; lean_object* v___y_2728_; 
v_id_2724_ = lean_ctor_get(v_a_2622_, 0);
lean_inc(v_id_2724_);
v_result_2725_ = lean_ctor_get(v_a_2622_, 1);
lean_inc(v_result_2725_);
lean_dec_ref(v_a_2622_);
v___x_2726_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2724_) == 0)
{
lean_object* v_s_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
v_s_2735_ = lean_ctor_get(v_id_2724_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_id_2724_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v_id_2724_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_s_2735_);
lean_dec(v_id_2724_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set_tag(v___x_2737_, 3);
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_s_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
v___y_2728_ = v___x_2740_;
goto v___jp_2727_;
}
}
}
else
{
lean_object* v_n_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
v_n_2743_ = lean_ctor_get(v_id_2724_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_id_2724_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v_id_2724_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_n_2743_);
lean_dec(v_id_2724_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set_tag(v___x_2745_, 2);
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_n_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
v___y_2728_ = v___x_2748_;
goto v___jp_2727_;
}
}
}
v___jp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2726_);
lean_ctor_set(v___x_2729_, 1, v___y_2728_);
v___x_2730_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
lean_ctor_set(v___x_2731_, 1, v_result_2725_);
v___x_2732_ = lean_box(0);
v___x_2733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2731_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
v___x_2734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2729_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___y_2673_ = v___x_2734_;
goto v___jp_2672_;
}
}
default: 
{
lean_object* v_id_2751_; uint8_t v_code_2752_; lean_object* v_message_2753_; lean_object* v_data_x3f_2754_; lean_object* v___x_2755_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___x_2775_; lean_object* v___y_2777_; 
v_id_2751_ = lean_ctor_get(v_a_2622_, 0);
lean_inc(v_id_2751_);
v_code_2752_ = lean_ctor_get_uint8(v_a_2622_, sizeof(void*)*3);
v_message_2753_ = lean_ctor_get(v_a_2622_, 1);
lean_inc_ref(v_message_2753_);
v_data_x3f_2754_ = lean_ctor_get(v_a_2622_, 2);
lean_inc(v_data_x3f_2754_);
lean_dec_ref(v_a_2622_);
v___x_2755_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2775_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2751_) == 0)
{
lean_object* v_s_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_s_2793_ = lean_ctor_get(v_id_2751_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_id_2751_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v_id_2751_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_s_2793_);
lean_dec(v_id_2751_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set_tag(v___x_2795_, 3);
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_s_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
v___y_2777_ = v___x_2798_;
goto v___jp_2776_;
}
}
}
else
{
lean_object* v_n_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
v_n_2801_ = lean_ctor_get(v_id_2751_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_id_2751_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v_id_2751_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_n_2801_);
lean_dec(v_id_2751_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set_tag(v___x_2803_, 2);
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_n_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
v___y_2777_ = v___x_2806_;
goto v___jp_2776_;
}
}
}
v___jp_2756_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_inc(v___y_2760_);
lean_inc_ref(v___y_2758_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___y_2758_);
lean_ctor_set(v___x_2761_, 1, v___y_2760_);
v___x_2762_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2763_, 0, v_message_2753_);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = lean_box(0);
v___x_2766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2761_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2769_ = l_Lean_Json_opt___redArg(v___x_2755_, v___x_2768_, v_data_x3f_2754_);
v___x_2770_ = l_List_appendTR___redArg(v___x_2767_, v___x_2769_);
v___x_2771_ = l_Lean_Json_mkObj(v___x_2770_);
lean_inc_ref(v___y_2759_);
v___x_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___y_2759_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
v___x_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set(v___x_2773_, 1, v___x_2765_);
v___x_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___y_2757_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___y_2673_ = v___x_2774_;
goto v___jp_2672_;
}
v___jp_2776_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2775_);
lean_ctor_set(v___x_2778_, 1, v___y_2777_);
v___x_2779_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2780_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2752_)
{
case 0:
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2781_;
goto v___jp_2756_;
}
case 1:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2782_;
goto v___jp_2756_;
}
case 2:
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2783_;
goto v___jp_2756_;
}
case 3:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2784_;
goto v___jp_2756_;
}
case 4:
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2785_;
goto v___jp_2756_;
}
case 5:
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2786_;
goto v___jp_2756_;
}
case 6:
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2787_;
goto v___jp_2756_;
}
case 7:
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2788_;
goto v___jp_2756_;
}
case 8:
{
lean_object* v___x_2789_; 
v___x_2789_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2789_;
goto v___jp_2756_;
}
case 9:
{
lean_object* v___x_2790_; 
v___x_2790_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2790_;
goto v___jp_2756_;
}
case 10:
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2791_;
goto v___jp_2756_;
}
default: 
{
lean_object* v___x_2792_; 
v___x_2792_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2757_ = v___x_2778_;
v___y_2758_ = v___x_2780_;
v___y_2759_ = v___x_2779_;
v___y_2760_ = v___x_2792_;
goto v___jp_2756_;
}
}
}
}
}
v___jp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2671_);
lean_ctor_set(v___x_2674_, 1, v___y_2673_);
v___x_2675_ = l_Lean_Json_mkObj(v___x_2674_);
v___x_2676_ = l_Lean_Json_compress(v___x_2675_);
v___x_2677_ = lean_string_append(v___x_2669_, v___x_2676_);
lean_dec_ref(v___x_2676_);
v___x_2678_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2679_ = lean_string_append(v___x_2677_, v___x_2678_);
v___x_2680_ = lean_mk_io_user_error(v___x_2679_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 1);
lean_ctor_set(v___x_2624_, 0, v___x_2680_);
v___x_2682_ = v___x_2624_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec_ref(v_inst_2619_);
lean_dec_ref(v_expectedMethod_2618_);
v_a_2810_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2621_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2621_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* v_h_2818_, lean_object* v_nBytes_2819_, lean_object* v_expectedMethod_2820_, lean_object* v_inst_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_IO_FS_Stream_readRequestAs___redArg(v_h_2818_, v_nBytes_2819_, v_expectedMethod_2820_, v_inst_2821_);
lean_dec(v_nBytes_2819_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object* v_h_2824_, lean_object* v_nBytes_2825_, lean_object* v_expectedMethod_2826_, lean_object* v_00_u03b1_2827_, lean_object* v_inst_2828_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_IO_FS_Stream_readRequestAs___redArg(v_h_2824_, v_nBytes_2825_, v_expectedMethod_2826_, v_inst_2828_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object* v_h_2831_, lean_object* v_nBytes_2832_, lean_object* v_expectedMethod_2833_, lean_object* v_00_u03b1_2834_, lean_object* v_inst_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_IO_FS_Stream_readRequestAs(v_h_2831_, v_nBytes_2832_, v_expectedMethod_2833_, v_00_u03b1_2834_, v_inst_2835_);
lean_dec(v_nBytes_2832_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object* v_h_2839_, lean_object* v_nBytes_2840_, lean_object* v_expectedMethod_2841_, lean_object* v_inst_2842_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_IO_FS_Stream_readMessage(v_h_2839_, v_nBytes_2840_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_3031_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_3031_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_3031_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
if (lean_obj_tag(v_a_2845_) == 1)
{
lean_object* v_method_2849_; lean_object* v_params_x3f_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2890_; 
v_method_2849_ = lean_ctor_get(v_a_2845_, 0);
v_params_x3f_2850_ = lean_ctor_get(v_a_2845_, 1);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_a_2845_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2852_ = v_a_2845_;
v_isShared_2853_ = v_isSharedCheck_2890_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_params_x3f_2850_);
lean_inc(v_method_2849_);
lean_dec(v_a_2845_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2890_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_string_dec_eq(v_method_2849_, v_expectedMethod_2841_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
lean_del_object(v___x_2852_);
lean_dec(v_params_x3f_2850_);
lean_dec_ref(v_inst_2842_);
v___x_2855_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2856_ = lean_string_append(v___x_2855_, v_expectedMethod_2841_);
lean_dec_ref(v_expectedMethod_2841_);
v___x_2857_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2858_ = lean_string_append(v___x_2856_, v___x_2857_);
v___x_2859_ = lean_string_append(v___x_2858_, v_method_2849_);
lean_dec_ref(v_method_2849_);
v___x_2860_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2861_ = lean_string_append(v___x_2859_, v___x_2860_);
v___x_2862_ = lean_mk_io_user_error(v___x_2861_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set_tag(v___x_2847_, 1);
lean_ctor_set(v___x_2847_, 0, v___x_2862_);
v___x_2864_ = v___x_2847_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_dec_ref(v_method_2849_);
v___x_2866_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2867_ = l_Option_toJson___redArg(v___x_2866_, v_params_x3f_2850_);
lean_inc(v___x_2867_);
v___x_2868_ = lean_apply_1(v_inst_2842_, v___x_2867_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
lean_del_object(v___x_2852_);
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref(v___x_2868_);
v___x_2870_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2871_ = l_Lean_Json_compress(v___x_2867_);
v___x_2872_ = lean_string_append(v___x_2870_, v___x_2871_);
lean_dec_ref(v___x_2871_);
v___x_2873_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2874_ = lean_string_append(v___x_2872_, v___x_2873_);
v___x_2875_ = lean_string_append(v___x_2874_, v_expectedMethod_2841_);
lean_dec_ref(v_expectedMethod_2841_);
v___x_2876_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2877_ = lean_string_append(v___x_2875_, v___x_2876_);
v___x_2878_ = lean_string_append(v___x_2877_, v_a_2869_);
lean_dec(v_a_2869_);
v___x_2879_ = lean_mk_io_user_error(v___x_2878_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set_tag(v___x_2847_, 1);
lean_ctor_set(v___x_2847_, 0, v___x_2879_);
v___x_2881_ = v___x_2847_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; 
lean_dec(v___x_2867_);
v_a_2883_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2868_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set_tag(v___x_2852_, 0);
lean_ctor_set(v___x_2852_, 1, v_a_2883_);
lean_ctor_set(v___x_2852_, 0, v_expectedMethod_2841_);
v___x_2885_ = v___x_2852_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_expectedMethod_2841_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_a_2883_);
v___x_2885_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2887_; 
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2885_);
v___x_2887_ = v___x_2847_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2885_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
}
}
else
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___y_2895_; 
lean_dec_ref(v_inst_2842_);
lean_dec_ref(v_expectedMethod_2841_);
v___x_2891_ = ((lean_object*)(l_IO_FS_Stream_readNotificationAs___redArg___closed__0));
v___x_2892_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2893_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2845_))
{
case 0:
{
lean_object* v_id_2906_; lean_object* v_method_2907_; lean_object* v_params_x3f_2908_; lean_object* v___x_2909_; lean_object* v___y_2911_; 
v_id_2906_ = lean_ctor_get(v_a_2845_, 0);
lean_inc(v_id_2906_);
v_method_2907_ = lean_ctor_get(v_a_2845_, 1);
lean_inc_ref(v_method_2907_);
v_params_x3f_2908_ = lean_ctor_get(v_a_2845_, 2);
lean_inc(v_params_x3f_2908_);
lean_dec_ref(v_a_2845_);
v___x_2909_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2906_) == 0)
{
lean_object* v_s_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
v_s_2922_ = lean_ctor_get(v_id_2906_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_id_2906_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v_id_2906_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_s_2922_);
lean_dec(v_id_2906_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set_tag(v___x_2924_, 3);
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_s_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
v___y_2911_ = v___x_2927_;
goto v___jp_2910_;
}
}
}
else
{
lean_object* v_n_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
v_n_2930_ = lean_ctor_get(v_id_2906_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_id_2906_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v_id_2906_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_n_2930_);
lean_dec(v_id_2906_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
lean_ctor_set_tag(v___x_2932_, 2);
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_n_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
v___y_2911_ = v___x_2935_;
goto v___jp_2910_;
}
}
}
v___jp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2909_);
lean_ctor_set(v___x_2912_, 1, v___y_2911_);
v___x_2913_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2914_, 0, v_method_2907_);
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2913_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = lean_box(0);
v___x_2917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2915_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
v___x_2918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2912_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2920_ = l_Lean_Json_opt___redArg(v___x_2892_, v___x_2919_, v_params_x3f_2908_);
v___x_2921_ = l_List_appendTR___redArg(v___x_2918_, v___x_2920_);
v___y_2895_ = v___x_2921_;
goto v___jp_2894_;
}
}
case 1:
{
lean_object* v_method_2938_; lean_object* v_params_x3f_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_method_2938_ = lean_ctor_get(v_a_2845_, 0);
lean_inc_ref(v_method_2938_);
v_params_x3f_2939_ = lean_ctor_get(v_a_2845_, 1);
lean_inc(v_params_x3f_2939_);
lean_dec_ref(v_a_2845_);
v___x_2940_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2941_, 0, v_method_2938_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2944_ = l_Lean_Json_opt___redArg(v___x_2892_, v___x_2943_, v_params_x3f_2939_);
v___x_2945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2942_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___y_2895_ = v___x_2945_;
goto v___jp_2894_;
}
case 2:
{
lean_object* v_id_2946_; lean_object* v_result_2947_; lean_object* v___x_2948_; lean_object* v___y_2950_; 
v_id_2946_ = lean_ctor_get(v_a_2845_, 0);
lean_inc(v_id_2946_);
v_result_2947_ = lean_ctor_get(v_a_2845_, 1);
lean_inc(v_result_2947_);
lean_dec_ref(v_a_2845_);
v___x_2948_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2946_) == 0)
{
lean_object* v_s_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
v_s_2957_ = lean_ctor_get(v_id_2946_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v_id_2946_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v_id_2946_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_s_2957_);
lean_dec(v_id_2946_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set_tag(v___x_2959_, 3);
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_s_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
v___y_2950_ = v___x_2962_;
goto v___jp_2949_;
}
}
}
else
{
lean_object* v_n_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
v_n_2965_ = lean_ctor_get(v_id_2946_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_id_2946_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v_id_2946_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_n_2965_);
lean_dec(v_id_2946_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 2);
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_n_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
v___y_2950_ = v___x_2970_;
goto v___jp_2949_;
}
}
}
v___jp_2949_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2948_);
lean_ctor_set(v___x_2951_, 1, v___y_2950_);
v___x_2952_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v_result_2947_);
v___x_2954_ = lean_box(0);
v___x_2955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2951_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___y_2895_ = v___x_2956_;
goto v___jp_2894_;
}
}
default: 
{
lean_object* v_id_2973_; uint8_t v_code_2974_; lean_object* v_message_2975_; lean_object* v_data_x3f_2976_; lean_object* v___x_2977_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___x_2997_; lean_object* v___y_2999_; 
v_id_2973_ = lean_ctor_get(v_a_2845_, 0);
lean_inc(v_id_2973_);
v_code_2974_ = lean_ctor_get_uint8(v_a_2845_, sizeof(void*)*3);
v_message_2975_ = lean_ctor_get(v_a_2845_, 1);
lean_inc_ref(v_message_2975_);
v_data_x3f_2976_ = lean_ctor_get(v_a_2845_, 2);
lean_inc(v_data_x3f_2976_);
lean_dec_ref(v_a_2845_);
v___x_2977_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2997_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2973_) == 0)
{
lean_object* v_s_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
v_s_3015_ = lean_ctor_get(v_id_2973_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_id_2973_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v_id_2973_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_s_3015_);
lean_dec(v_id_2973_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set_tag(v___x_3017_, 3);
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_s_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
v___y_2999_ = v___x_3020_;
goto v___jp_2998_;
}
}
}
else
{
lean_object* v_n_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
v_n_3023_ = lean_ctor_get(v_id_2973_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_id_2973_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v_id_2973_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_n_3023_);
lean_dec(v_id_2973_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
lean_ctor_set_tag(v___x_3025_, 2);
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_n_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
v___y_2999_ = v___x_3028_;
goto v___jp_2998_;
}
}
}
v___jp_2978_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_inc(v___y_2982_);
lean_inc_ref(v___y_2980_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___y_2980_);
lean_ctor_set(v___x_2983_, 1, v___y_2982_);
v___x_2984_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_message_2975_);
v___x_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
v___x_2987_ = lean_box(0);
v___x_2988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2983_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2991_ = l_Lean_Json_opt___redArg(v___x_2977_, v___x_2990_, v_data_x3f_2976_);
v___x_2992_ = l_List_appendTR___redArg(v___x_2989_, v___x_2991_);
v___x_2993_ = l_Lean_Json_mkObj(v___x_2992_);
lean_inc_ref(v___y_2979_);
v___x_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___y_2979_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
lean_ctor_set(v___x_2995_, 1, v___x_2987_);
v___x_2996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___y_2981_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
v___y_2895_ = v___x_2996_;
goto v___jp_2894_;
}
v___jp_2998_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2997_);
lean_ctor_set(v___x_3000_, 1, v___y_2999_);
v___x_3001_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3002_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2974_)
{
case 0:
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3003_;
goto v___jp_2978_;
}
case 1:
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3004_;
goto v___jp_2978_;
}
case 2:
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3005_;
goto v___jp_2978_;
}
case 3:
{
lean_object* v___x_3006_; 
v___x_3006_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3006_;
goto v___jp_2978_;
}
case 4:
{
lean_object* v___x_3007_; 
v___x_3007_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3007_;
goto v___jp_2978_;
}
case 5:
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3008_;
goto v___jp_2978_;
}
case 6:
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3009_;
goto v___jp_2978_;
}
case 7:
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3010_;
goto v___jp_2978_;
}
case 8:
{
lean_object* v___x_3011_; 
v___x_3011_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3011_;
goto v___jp_2978_;
}
case 9:
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3012_;
goto v___jp_2978_;
}
case 10:
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3013_;
goto v___jp_2978_;
}
default: 
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2979_ = v___x_3001_;
v___y_2980_ = v___x_3002_;
v___y_2981_ = v___x_3000_;
v___y_2982_ = v___x_3014_;
goto v___jp_2978_;
}
}
}
}
}
v___jp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2893_);
lean_ctor_set(v___x_2896_, 1, v___y_2895_);
v___x_2897_ = l_Lean_Json_mkObj(v___x_2896_);
v___x_2898_ = l_Lean_Json_compress(v___x_2897_);
v___x_2899_ = lean_string_append(v___x_2891_, v___x_2898_);
lean_dec_ref(v___x_2898_);
v___x_2900_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2901_ = lean_string_append(v___x_2899_, v___x_2900_);
v___x_2902_ = lean_mk_io_user_error(v___x_2901_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set_tag(v___x_2847_, 1);
lean_ctor_set(v___x_2847_, 0, v___x_2902_);
v___x_2904_ = v___x_2847_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_inst_2842_);
lean_dec_ref(v_expectedMethod_2841_);
v_a_3032_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2844_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2844_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* v_h_3040_, lean_object* v_nBytes_3041_, lean_object* v_expectedMethod_3042_, lean_object* v_inst_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_IO_FS_Stream_readNotificationAs___redArg(v_h_3040_, v_nBytes_3041_, v_expectedMethod_3042_, v_inst_3043_);
lean_dec(v_nBytes_3041_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object* v_h_3046_, lean_object* v_nBytes_3047_, lean_object* v_expectedMethod_3048_, lean_object* v_00_u03b1_3049_, lean_object* v_inst_3050_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_IO_FS_Stream_readNotificationAs___redArg(v_h_3046_, v_nBytes_3047_, v_expectedMethod_3048_, v_inst_3050_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object* v_h_3053_, lean_object* v_nBytes_3054_, lean_object* v_expectedMethod_3055_, lean_object* v_00_u03b1_3056_, lean_object* v_inst_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_IO_FS_Stream_readNotificationAs(v_h_3053_, v_nBytes_3054_, v_expectedMethod_3055_, v_00_u03b1_3056_, v_inst_3057_);
lean_dec(v_nBytes_3054_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object* v_h_3064_, lean_object* v_nBytes_3065_, lean_object* v_expectedID_3066_, lean_object* v_inst_3067_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_IO_FS_Stream_readMessage(v_h_3064_, v_nBytes_3065_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3273_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3273_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3273_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___y_3075_; lean_object* v___y_3076_; 
if (lean_obj_tag(v_a_3070_) == 2)
{
lean_object* v_id_3082_; lean_object* v_result_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3134_; 
v_id_3082_ = lean_ctor_get(v_a_3070_, 0);
v_result_3083_ = lean_ctor_get(v_a_3070_, 1);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_a_3070_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3085_ = v_a_3070_;
v_isShared_3086_ = v_isSharedCheck_3134_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_result_3083_);
lean_inc(v_id_3082_);
lean_dec(v_a_3070_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3134_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
uint8_t v___x_3087_; 
v___x_3087_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3082_, v_expectedID_3066_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___y_3090_; 
lean_del_object(v___x_3085_);
lean_dec(v_result_3083_);
lean_dec_ref(v_inst_3067_);
v___x_3088_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__0));
switch(lean_obj_tag(v_expectedID_3066_))
{
case 0:
{
lean_object* v_s_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_s_3100_ = lean_ctor_get(v_expectedID_3066_, 0);
lean_inc_ref(v_s_3100_);
lean_dec_ref(v_expectedID_3066_);
v___x_3101_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3102_ = lean_string_append(v___x_3101_, v_s_3100_);
lean_dec_ref(v_s_3100_);
v___x_3103_ = lean_string_append(v___x_3102_, v___x_3101_);
v___y_3090_ = v___x_3103_;
goto v___jp_3089_;
}
case 1:
{
lean_object* v_n_3104_; lean_object* v___x_3105_; 
v_n_3104_ = lean_ctor_get(v_expectedID_3066_, 0);
lean_inc_ref(v_n_3104_);
lean_dec_ref(v_expectedID_3066_);
v___x_3105_ = l_Lean_JsonNumber_toString(v_n_3104_);
v___y_3090_ = v___x_3105_;
goto v___jp_3089_;
}
default: 
{
lean_object* v___x_3106_; 
v___x_3106_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___y_3090_ = v___x_3106_;
goto v___jp_3089_;
}
}
v___jp_3089_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = lean_string_append(v___x_3088_, v___y_3090_);
lean_dec_ref(v___y_3090_);
v___x_3092_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__1));
v___x_3093_ = lean_string_append(v___x_3091_, v___x_3092_);
if (lean_obj_tag(v_id_3082_) == 0)
{
lean_object* v_s_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_s_3094_ = lean_ctor_get(v_id_3082_, 0);
lean_inc_ref(v_s_3094_);
lean_dec_ref(v_id_3082_);
v___x_3095_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3096_ = lean_string_append(v___x_3095_, v_s_3094_);
lean_dec_ref(v_s_3094_);
v___x_3097_ = lean_string_append(v___x_3096_, v___x_3095_);
v___y_3075_ = v___x_3093_;
v___y_3076_ = v___x_3097_;
goto v___jp_3074_;
}
else
{
lean_object* v_n_3098_; lean_object* v___x_3099_; 
v_n_3098_ = lean_ctor_get(v_id_3082_, 0);
lean_inc_ref(v_n_3098_);
lean_dec_ref(v_id_3082_);
v___x_3099_ = l_Lean_JsonNumber_toString(v_n_3098_);
v___y_3075_ = v___x_3093_;
v___y_3076_ = v___x_3099_;
goto v___jp_3074_;
}
}
}
else
{
lean_object* v___x_3107_; 
lean_dec(v_id_3082_);
lean_del_object(v___x_3072_);
lean_inc(v_result_3083_);
v___x_3107_ = lean_apply_1(v_inst_3067_, v_result_3083_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3122_; 
lean_del_object(v___x_3085_);
lean_dec(v_expectedID_3066_);
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3122_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3122_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3112_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__2));
v___x_3113_ = l_Lean_Json_compress(v_result_3083_);
v___x_3114_ = lean_string_append(v___x_3112_, v___x_3113_);
lean_dec_ref(v___x_3113_);
v___x_3115_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_3116_ = lean_string_append(v___x_3114_, v___x_3115_);
v___x_3117_ = lean_string_append(v___x_3116_, v_a_3108_);
lean_dec(v_a_3108_);
v___x_3118_ = lean_mk_io_user_error(v___x_3117_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set_tag(v___x_3110_, 1);
lean_ctor_set(v___x_3110_, 0, v___x_3118_);
v___x_3120_ = v___x_3110_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_result_3083_);
v_a_3123_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3125_ = v___x_3107_;
v_isShared_3126_ = v_isSharedCheck_3133_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3107_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3133_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set_tag(v___x_3085_, 0);
lean_ctor_set(v___x_3085_, 1, v_a_3123_);
lean_ctor_set(v___x_3085_, 0, v_expectedID_3066_);
v___x_3128_ = v___x_3085_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_expectedID_3066_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3130_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set_tag(v___x_3125_, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3128_);
v___x_3130_ = v___x_3125_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___y_3139_; 
lean_del_object(v___x_3072_);
lean_dec_ref(v_inst_3067_);
lean_dec(v_expectedID_3066_);
v___x_3135_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__3));
v___x_3136_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_3137_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_3070_))
{
case 0:
{
lean_object* v_id_3148_; lean_object* v_method_3149_; lean_object* v_params_x3f_3150_; lean_object* v___x_3151_; lean_object* v___y_3153_; 
v_id_3148_ = lean_ctor_get(v_a_3070_, 0);
lean_inc(v_id_3148_);
v_method_3149_ = lean_ctor_get(v_a_3070_, 1);
lean_inc_ref(v_method_3149_);
v_params_x3f_3150_ = lean_ctor_get(v_a_3070_, 2);
lean_inc(v_params_x3f_3150_);
lean_dec_ref(v_a_3070_);
v___x_3151_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3148_) == 0)
{
lean_object* v_s_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
v_s_3164_ = lean_ctor_get(v_id_3148_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_id_3148_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v_id_3148_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_s_3164_);
lean_dec(v_id_3148_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set_tag(v___x_3166_, 3);
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_s_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
v___y_3153_ = v___x_3169_;
goto v___jp_3152_;
}
}
}
else
{
lean_object* v_n_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
v_n_3172_ = lean_ctor_get(v_id_3148_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v_id_3148_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v_id_3148_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_n_3172_);
lean_dec(v_id_3148_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 2);
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_n_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
v___y_3153_ = v___x_3177_;
goto v___jp_3152_;
}
}
}
v___jp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3151_);
lean_ctor_set(v___x_3154_, 1, v___y_3153_);
v___x_3155_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3156_, 0, v_method_3149_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3155_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = lean_box(0);
v___x_3159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3157_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3154_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3162_ = l_Lean_Json_opt___redArg(v___x_3136_, v___x_3161_, v_params_x3f_3150_);
v___x_3163_ = l_List_appendTR___redArg(v___x_3160_, v___x_3162_);
v___y_3139_ = v___x_3163_;
goto v___jp_3138_;
}
}
case 1:
{
lean_object* v_method_3180_; lean_object* v_params_x3f_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_method_3180_ = lean_ctor_get(v_a_3070_, 0);
lean_inc_ref(v_method_3180_);
v_params_x3f_3181_ = lean_ctor_get(v_a_3070_, 1);
lean_inc(v_params_x3f_3181_);
lean_dec_ref(v_a_3070_);
v___x_3182_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3183_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3183_, 0, v_method_3180_);
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3182_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3186_ = l_Lean_Json_opt___redArg(v___x_3136_, v___x_3185_, v_params_x3f_3181_);
v___x_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3184_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___y_3139_ = v___x_3187_;
goto v___jp_3138_;
}
case 2:
{
lean_object* v_id_3188_; lean_object* v_result_3189_; lean_object* v___x_3190_; lean_object* v___y_3192_; 
v_id_3188_ = lean_ctor_get(v_a_3070_, 0);
lean_inc(v_id_3188_);
v_result_3189_ = lean_ctor_get(v_a_3070_, 1);
lean_inc(v_result_3189_);
lean_dec_ref(v_a_3070_);
v___x_3190_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3188_) == 0)
{
lean_object* v_s_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
v_s_3199_ = lean_ctor_get(v_id_3188_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_id_3188_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v_id_3188_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_s_3199_);
lean_dec(v_id_3188_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set_tag(v___x_3201_, 3);
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_s_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
v___y_3192_ = v___x_3204_;
goto v___jp_3191_;
}
}
}
else
{
lean_object* v_n_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
v_n_3207_ = lean_ctor_get(v_id_3188_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_id_3188_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v_id_3188_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_n_3207_);
lean_dec(v_id_3188_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 2);
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_n_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
v___y_3192_ = v___x_3212_;
goto v___jp_3191_;
}
}
}
v___jp_3191_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3190_);
lean_ctor_set(v___x_3193_, 1, v___y_3192_);
v___x_3194_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
lean_ctor_set(v___x_3195_, 1, v_result_3189_);
v___x_3196_ = lean_box(0);
v___x_3197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3195_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3193_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___y_3139_ = v___x_3198_;
goto v___jp_3138_;
}
}
default: 
{
lean_object* v_id_3215_; uint8_t v_code_3216_; lean_object* v_message_3217_; lean_object* v_data_x3f_3218_; lean_object* v___x_3219_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___x_3239_; lean_object* v___y_3241_; 
v_id_3215_ = lean_ctor_get(v_a_3070_, 0);
lean_inc(v_id_3215_);
v_code_3216_ = lean_ctor_get_uint8(v_a_3070_, sizeof(void*)*3);
v_message_3217_ = lean_ctor_get(v_a_3070_, 1);
lean_inc_ref(v_message_3217_);
v_data_x3f_3218_ = lean_ctor_get(v_a_3070_, 2);
lean_inc(v_data_x3f_3218_);
lean_dec_ref(v_a_3070_);
v___x_3219_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_3239_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3215_) == 0)
{
lean_object* v_s_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
v_s_3257_ = lean_ctor_get(v_id_3215_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_id_3215_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v_id_3215_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_s_3257_);
lean_dec(v_id_3215_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
lean_ctor_set_tag(v___x_3259_, 3);
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_s_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
v___y_3241_ = v___x_3262_;
goto v___jp_3240_;
}
}
}
else
{
lean_object* v_n_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
v_n_3265_ = lean_ctor_get(v_id_3215_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_id_3215_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v_id_3215_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_n_3265_);
lean_dec(v_id_3215_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 2);
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_n_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
v___y_3241_ = v___x_3270_;
goto v___jp_3240_;
}
}
}
v___jp_3220_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_inc(v___y_3224_);
lean_inc_ref(v___y_3221_);
v___x_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___y_3221_);
lean_ctor_set(v___x_3225_, 1, v___y_3224_);
v___x_3226_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_message_3217_);
v___x_3228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3226_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
v___x_3229_ = lean_box(0);
v___x_3230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3228_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3225_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3233_ = l_Lean_Json_opt___redArg(v___x_3219_, v___x_3232_, v_data_x3f_3218_);
v___x_3234_ = l_List_appendTR___redArg(v___x_3231_, v___x_3233_);
v___x_3235_ = l_Lean_Json_mkObj(v___x_3234_);
lean_inc_ref(v___y_3223_);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___y_3223_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
lean_ctor_set(v___x_3237_, 1, v___x_3229_);
v___x_3238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___y_3222_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___y_3139_ = v___x_3238_;
goto v___jp_3138_;
}
v___jp_3240_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3239_);
lean_ctor_set(v___x_3242_, 1, v___y_3241_);
v___x_3243_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3244_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3216_)
{
case 0:
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3245_;
goto v___jp_3220_;
}
case 1:
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3246_;
goto v___jp_3220_;
}
case 2:
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3247_;
goto v___jp_3220_;
}
case 3:
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3248_;
goto v___jp_3220_;
}
case 4:
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3249_;
goto v___jp_3220_;
}
case 5:
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3250_;
goto v___jp_3220_;
}
case 6:
{
lean_object* v___x_3251_; 
v___x_3251_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3251_;
goto v___jp_3220_;
}
case 7:
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3252_;
goto v___jp_3220_;
}
case 8:
{
lean_object* v___x_3253_; 
v___x_3253_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3253_;
goto v___jp_3220_;
}
case 9:
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3254_;
goto v___jp_3220_;
}
case 10:
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3255_;
goto v___jp_3220_;
}
default: 
{
lean_object* v___x_3256_; 
v___x_3256_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3221_ = v___x_3244_;
v___y_3222_ = v___x_3242_;
v___y_3223_ = v___x_3243_;
v___y_3224_ = v___x_3256_;
goto v___jp_3220_;
}
}
}
}
}
v___jp_3138_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3137_);
lean_ctor_set(v___x_3140_, 1, v___y_3139_);
v___x_3141_ = l_Lean_Json_mkObj(v___x_3140_);
v___x_3142_ = l_Lean_Json_compress(v___x_3141_);
v___x_3143_ = lean_string_append(v___x_3135_, v___x_3142_);
lean_dec_ref(v___x_3142_);
v___x_3144_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_3145_ = lean_string_append(v___x_3143_, v___x_3144_);
v___x_3146_ = lean_mk_io_user_error(v___x_3145_);
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
return v___x_3147_;
}
}
v___jp_3074_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
v___x_3077_ = lean_string_append(v___y_3075_, v___y_3076_);
lean_dec_ref(v___y_3076_);
v___x_3078_ = lean_mk_io_user_error(v___x_3077_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set_tag(v___x_3072_, 1);
lean_ctor_set(v___x_3072_, 0, v___x_3078_);
v___x_3080_ = v___x_3072_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3078_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec_ref(v_inst_3067_);
lean_dec(v_expectedID_3066_);
v_a_3274_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3069_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3069_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* v_h_3282_, lean_object* v_nBytes_3283_, lean_object* v_expectedID_3284_, lean_object* v_inst_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_IO_FS_Stream_readResponseAs___redArg(v_h_3282_, v_nBytes_3283_, v_expectedID_3284_, v_inst_3285_);
lean_dec(v_nBytes_3283_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object* v_h_3288_, lean_object* v_nBytes_3289_, lean_object* v_expectedID_3290_, lean_object* v_00_u03b1_3291_, lean_object* v_inst_3292_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_IO_FS_Stream_readResponseAs___redArg(v_h_3288_, v_nBytes_3289_, v_expectedID_3290_, v_inst_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object* v_h_3295_, lean_object* v_nBytes_3296_, lean_object* v_expectedID_3297_, lean_object* v_00_u03b1_3298_, lean_object* v_inst_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_IO_FS_Stream_readResponseAs(v_h_3295_, v_nBytes_3296_, v_expectedID_3297_, v_00_u03b1_3298_, v_inst_3299_);
lean_dec(v_nBytes_3296_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(lean_object* v_k_3302_, lean_object* v_x_3303_){
_start:
{
if (lean_obj_tag(v_x_3303_) == 0)
{
lean_object* v___x_3304_; 
lean_dec_ref(v_k_3302_);
v___x_3304_ = lean_box(0);
return v___x_3304_;
}
else
{
lean_object* v_val_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v_val_3305_ = lean_ctor_get(v_x_3303_, 0);
lean_inc(v_val_3305_);
lean_dec_ref(v_x_3303_);
v___x_3306_ = l_Lean_Json_Structured_toJson(v_val_3305_);
v___x_3307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3307_, 0, v_k_3302_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = lean_box(0);
v___x_3309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
return v___x_3309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(lean_object* v_k_3310_, lean_object* v_x_3311_){
_start:
{
if (lean_obj_tag(v_x_3311_) == 0)
{
lean_object* v___x_3312_; 
lean_dec_ref(v_k_3310_);
v___x_3312_ = lean_box(0);
return v___x_3312_;
}
else
{
lean_object* v_val_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_val_3313_ = lean_ctor_get(v_x_3311_, 0);
lean_inc(v_val_3313_);
v___x_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3314_, 0, v_k_3310_);
lean_ctor_set(v___x_3314_, 1, v_val_3313_);
v___x_3315_ = lean_box(0);
v___x_3316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
return v___x_3316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* v_k_3317_, lean_object* v_x_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(v_k_3317_, v_x_3318_);
lean_dec(v_x_3318_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object* v_h_3320_, lean_object* v_m_3321_){
_start:
{
lean_object* v___x_3323_; lean_object* v___y_3325_; 
v___x_3323_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_3321_))
{
case 0:
{
lean_object* v_id_3329_; lean_object* v_method_3330_; lean_object* v_params_x3f_3331_; lean_object* v___x_3332_; lean_object* v___y_3334_; 
v_id_3329_ = lean_ctor_get(v_m_3321_, 0);
lean_inc(v_id_3329_);
v_method_3330_ = lean_ctor_get(v_m_3321_, 1);
lean_inc_ref(v_method_3330_);
v_params_x3f_3331_ = lean_ctor_get(v_m_3321_, 2);
lean_inc(v_params_x3f_3331_);
lean_dec_ref(v_m_3321_);
v___x_3332_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3329_))
{
case 0:
{
lean_object* v_s_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
v_s_3345_ = lean_ctor_get(v_id_3329_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_id_3329_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v_id_3329_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_s_3345_);
lean_dec(v_id_3329_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
lean_ctor_set_tag(v___x_3347_, 3);
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_s_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
v___y_3334_ = v___x_3350_;
goto v___jp_3333_;
}
}
}
case 1:
{
lean_object* v_n_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
v_n_3353_ = lean_ctor_get(v_id_3329_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v_id_3329_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v_id_3329_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_n_3353_);
lean_dec(v_id_3329_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
lean_ctor_set_tag(v___x_3355_, 2);
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_n_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
v___y_3334_ = v___x_3358_;
goto v___jp_3333_;
}
}
}
default: 
{
lean_object* v___x_3361_; 
v___x_3361_ = lean_box(0);
v___y_3334_ = v___x_3361_;
goto v___jp_3333_;
}
}
v___jp_3333_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3332_);
lean_ctor_set(v___x_3335_, 1, v___y_3334_);
v___x_3336_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_method_3330_);
v___x_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3336_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = lean_box(0);
v___x_3340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3338_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3335_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3343_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(v___x_3342_, v_params_x3f_3331_);
v___x_3344_ = l_List_appendTR___redArg(v___x_3341_, v___x_3343_);
v___y_3325_ = v___x_3344_;
goto v___jp_3324_;
}
}
case 1:
{
lean_object* v_method_3362_; lean_object* v_params_x3f_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3375_; 
v_method_3362_ = lean_ctor_get(v_m_3321_, 0);
v_params_x3f_3363_ = lean_ctor_get(v_m_3321_, 1);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_m_3321_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3365_ = v_m_3321_;
v_isShared_3366_ = v_isSharedCheck_3375_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_params_x3f_3363_);
lean_inc(v_method_3362_);
lean_dec(v_m_3321_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3375_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3367_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3368_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3368_, 0, v_method_3362_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set_tag(v___x_3365_, 0);
lean_ctor_set(v___x_3365_, 1, v___x_3368_);
lean_ctor_set(v___x_3365_, 0, v___x_3367_);
v___x_3370_ = v___x_3365_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3371_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3372_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(v___x_3371_, v_params_x3f_3363_);
v___x_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3370_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
v___y_3325_ = v___x_3373_;
goto v___jp_3324_;
}
}
}
case 2:
{
lean_object* v_id_3376_; lean_object* v_result_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3409_; 
v_id_3376_ = lean_ctor_get(v_m_3321_, 0);
v_result_3377_ = lean_ctor_get(v_m_3321_, 1);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_m_3321_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3379_ = v_m_3321_;
v_isShared_3380_ = v_isSharedCheck_3409_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_result_3377_);
lean_inc(v_id_3376_);
lean_dec(v_m_3321_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3409_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; lean_object* v___y_3383_; 
v___x_3381_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3376_))
{
case 0:
{
lean_object* v_s_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
v_s_3392_ = lean_ctor_get(v_id_3376_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v_id_3376_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v_id_3376_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_s_3392_);
lean_dec(v_id_3376_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
lean_ctor_set_tag(v___x_3394_, 3);
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_s_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
v___y_3383_ = v___x_3397_;
goto v___jp_3382_;
}
}
}
case 1:
{
lean_object* v_n_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
v_n_3400_ = lean_ctor_get(v_id_3376_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_id_3376_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v_id_3376_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_n_3400_);
lean_dec(v_id_3376_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
lean_ctor_set_tag(v___x_3402_, 2);
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_n_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
v___y_3383_ = v___x_3405_;
goto v___jp_3382_;
}
}
}
default: 
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_box(0);
v___y_3383_ = v___x_3408_;
goto v___jp_3382_;
}
}
v___jp_3382_:
{
lean_object* v___x_3385_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set_tag(v___x_3379_, 0);
lean_ctor_set(v___x_3379_, 1, v___y_3383_);
lean_ctor_set(v___x_3379_, 0, v___x_3381_);
v___x_3385_ = v___x_3379_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v___y_3383_);
v___x_3385_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3386_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
lean_ctor_set(v___x_3387_, 1, v_result_3377_);
v___x_3388_ = lean_box(0);
v___x_3389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3385_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___y_3325_ = v___x_3390_;
goto v___jp_3324_;
}
}
}
}
default: 
{
lean_object* v_id_3410_; uint8_t v_code_3411_; lean_object* v_message_3412_; lean_object* v_data_x3f_3413_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___x_3433_; lean_object* v___y_3435_; 
v_id_3410_ = lean_ctor_get(v_m_3321_, 0);
lean_inc(v_id_3410_);
v_code_3411_ = lean_ctor_get_uint8(v_m_3321_, sizeof(void*)*3);
v_message_3412_ = lean_ctor_get(v_m_3321_, 1);
lean_inc_ref(v_message_3412_);
v_data_x3f_3413_ = lean_ctor_get(v_m_3321_, 2);
lean_inc(v_data_x3f_3413_);
lean_dec_ref(v_m_3321_);
v___x_3433_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3410_))
{
case 0:
{
lean_object* v_s_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
v_s_3451_ = lean_ctor_get(v_id_3410_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_id_3410_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v_id_3410_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_s_3451_);
lean_dec(v_id_3410_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set_tag(v___x_3453_, 3);
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_s_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
v___y_3435_ = v___x_3456_;
goto v___jp_3434_;
}
}
}
case 1:
{
lean_object* v_n_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
v_n_3459_ = lean_ctor_get(v_id_3410_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_id_3410_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v_id_3410_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_n_3459_);
lean_dec(v_id_3410_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
lean_ctor_set_tag(v___x_3461_, 2);
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_n_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
v___y_3435_ = v___x_3464_;
goto v___jp_3434_;
}
}
}
default: 
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_box(0);
v___y_3435_ = v___x_3467_;
goto v___jp_3434_;
}
}
v___jp_3414_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
lean_inc(v___y_3418_);
lean_inc_ref(v___y_3415_);
v___x_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___y_3415_);
lean_ctor_set(v___x_3419_, 1, v___y_3418_);
v___x_3420_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3421_, 0, v_message_3412_);
v___x_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = lean_box(0);
v___x_3424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3419_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3427_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(v___x_3426_, v_data_x3f_3413_);
lean_dec(v_data_x3f_3413_);
v___x_3428_ = l_List_appendTR___redArg(v___x_3425_, v___x_3427_);
v___x_3429_ = l_Lean_Json_mkObj(v___x_3428_);
lean_inc_ref(v___y_3416_);
v___x_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___y_3416_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
lean_ctor_set(v___x_3431_, 1, v___x_3423_);
v___x_3432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___y_3417_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___y_3325_ = v___x_3432_;
goto v___jp_3324_;
}
v___jp_3434_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3433_);
lean_ctor_set(v___x_3436_, 1, v___y_3435_);
v___x_3437_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3438_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3411_)
{
case 0:
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3439_;
goto v___jp_3414_;
}
case 1:
{
lean_object* v___x_3440_; 
v___x_3440_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3440_;
goto v___jp_3414_;
}
case 2:
{
lean_object* v___x_3441_; 
v___x_3441_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3441_;
goto v___jp_3414_;
}
case 3:
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3442_;
goto v___jp_3414_;
}
case 4:
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3443_;
goto v___jp_3414_;
}
case 5:
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3444_;
goto v___jp_3414_;
}
case 6:
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3445_;
goto v___jp_3414_;
}
case 7:
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3446_;
goto v___jp_3414_;
}
case 8:
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3447_;
goto v___jp_3414_;
}
case 9:
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3448_;
goto v___jp_3414_;
}
case 10:
{
lean_object* v___x_3449_; 
v___x_3449_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3449_;
goto v___jp_3414_;
}
default: 
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3415_ = v___x_3438_;
v___y_3416_ = v___x_3437_;
v___y_3417_ = v___x_3436_;
v___y_3418_ = v___x_3450_;
goto v___jp_3414_;
}
}
}
}
}
v___jp_3324_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3323_);
lean_ctor_set(v___x_3326_, 1, v___y_3325_);
v___x_3327_ = l_Lean_Json_mkObj(v___x_3326_);
v___x_3328_ = l_IO_FS_Stream_writeJson(v_h_3320_, v___x_3327_);
return v___x_3328_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object* v_h_3468_, lean_object* v_m_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_IO_FS_Stream_writeMessage(v_h_3468_, v_m_3469_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg(lean_object* v_inst_3472_, lean_object* v_h_3473_, lean_object* v_r_3474_){
_start:
{
lean_object* v_id_3476_; lean_object* v_method_3477_; lean_object* v_param_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3498_; 
v_id_3476_ = lean_ctor_get(v_r_3474_, 0);
v_method_3477_ = lean_ctor_get(v_r_3474_, 1);
v_param_3478_ = lean_ctor_get(v_r_3474_, 2);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_r_3474_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3480_ = v_r_3474_;
v_isShared_3481_ = v_isSharedCheck_3498_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_param_3478_);
lean_inc(v_method_3477_);
lean_inc(v_id_3476_);
lean_dec(v_r_3474_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3498_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___y_3483_; lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3472_, v_param_3478_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v___x_3489_; 
lean_dec_ref(v___x_3488_);
v___x_3489_ = lean_box(0);
v___y_3483_ = v___x_3489_;
goto v___jp_3482_;
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
v_a_3490_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3488_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3488_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
v___y_3483_ = v___x_3495_;
goto v___jp_3482_;
}
}
}
v___jp_3482_:
{
lean_object* v___x_3485_; 
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 2, v___y_3483_);
v___x_3485_ = v___x_3480_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_id_3476_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_method_3477_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v___y_3483_);
v___x_3485_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_IO_FS_Stream_writeMessage(v_h_3473_, v___x_3485_);
return v___x_3486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg___boxed(lean_object* v_inst_3499_, lean_object* v_h_3500_, lean_object* v_r_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_IO_FS_Stream_writeRequest___redArg(v_inst_3499_, v_h_3500_, v_r_3501_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object* v_00_u03b1_3504_, lean_object* v_inst_3505_, lean_object* v_h_3506_, lean_object* v_r_3507_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_IO_FS_Stream_writeRequest___redArg(v_inst_3505_, v_h_3506_, v_r_3507_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___boxed(lean_object* v_00_u03b1_3510_, lean_object* v_inst_3511_, lean_object* v_h_3512_, lean_object* v_r_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_IO_FS_Stream_writeRequest(v_00_u03b1_3510_, v_inst_3511_, v_h_3512_, v_r_3513_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg(lean_object* v_inst_3516_, lean_object* v_h_3517_, lean_object* v_n_3518_){
_start:
{
lean_object* v_method_3520_; lean_object* v_param_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3541_; 
v_method_3520_ = lean_ctor_get(v_n_3518_, 0);
v_param_3521_ = lean_ctor_get(v_n_3518_, 1);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_n_3518_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3523_ = v_n_3518_;
v_isShared_3524_ = v_isSharedCheck_3541_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_param_3521_);
lean_inc(v_method_3520_);
lean_dec(v_n_3518_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3541_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___y_3526_; lean_object* v___x_3531_; 
v___x_3531_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3516_, v_param_3521_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v___x_3532_; 
lean_dec_ref(v___x_3531_);
v___x_3532_ = lean_box(0);
v___y_3526_ = v___x_3532_;
goto v___jp_3525_;
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
v_a_3533_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3531_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3531_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
v___y_3526_ = v___x_3538_;
goto v___jp_3525_;
}
}
}
v___jp_3525_:
{
lean_object* v___x_3528_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set_tag(v___x_3523_, 1);
lean_ctor_set(v___x_3523_, 1, v___y_3526_);
v___x_3528_ = v___x_3523_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_method_3520_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v___y_3526_);
v___x_3528_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_IO_FS_Stream_writeMessage(v_h_3517_, v___x_3528_);
return v___x_3529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg___boxed(lean_object* v_inst_3542_, lean_object* v_h_3543_, lean_object* v_n_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_IO_FS_Stream_writeNotification___redArg(v_inst_3542_, v_h_3543_, v_n_3544_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object* v_00_u03b1_3547_, lean_object* v_inst_3548_, lean_object* v_h_3549_, lean_object* v_n_3550_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_IO_FS_Stream_writeNotification___redArg(v_inst_3548_, v_h_3549_, v_n_3550_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___boxed(lean_object* v_00_u03b1_3553_, lean_object* v_inst_3554_, lean_object* v_h_3555_, lean_object* v_n_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_IO_FS_Stream_writeNotification(v_00_u03b1_3553_, v_inst_3554_, v_h_3555_, v_n_3556_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg(lean_object* v_inst_3559_, lean_object* v_h_3560_, lean_object* v_r_3561_){
_start:
{
lean_object* v_id_3563_; lean_object* v_result_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3573_; 
v_id_3563_ = lean_ctor_get(v_r_3561_, 0);
v_result_3564_ = lean_ctor_get(v_r_3561_, 1);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_r_3561_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3566_ = v_r_3561_;
v_isShared_3567_ = v_isSharedCheck_3573_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_result_3564_);
lean_inc(v_id_3563_);
lean_dec(v_r_3561_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3573_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3568_ = lean_apply_1(v_inst_3559_, v_result_3564_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set_tag(v___x_3566_, 2);
lean_ctor_set(v___x_3566_, 1, v___x_3568_);
v___x_3570_ = v___x_3566_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_id_3563_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; 
v___x_3571_ = l_IO_FS_Stream_writeMessage(v_h_3560_, v___x_3570_);
return v___x_3571_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg___boxed(lean_object* v_inst_3574_, lean_object* v_h_3575_, lean_object* v_r_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_IO_FS_Stream_writeResponse___redArg(v_inst_3574_, v_h_3575_, v_r_3576_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object* v_00_u03b1_3579_, lean_object* v_inst_3580_, lean_object* v_h_3581_, lean_object* v_r_3582_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_IO_FS_Stream_writeResponse___redArg(v_inst_3580_, v_h_3581_, v_r_3582_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___boxed(lean_object* v_00_u03b1_3585_, lean_object* v_inst_3586_, lean_object* v_h_3587_, lean_object* v_r_3588_, lean_object* v_a_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_IO_FS_Stream_writeResponse(v_00_u03b1_3585_, v_inst_3586_, v_h_3587_, v_r_3588_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object* v_h_3591_, lean_object* v_e_3592_){
_start:
{
lean_object* v_id_3594_; uint8_t v_code_3595_; lean_object* v_message_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3605_; 
v_id_3594_ = lean_ctor_get(v_e_3592_, 0);
v_code_3595_ = lean_ctor_get_uint8(v_e_3592_, sizeof(void*)*3);
v_message_3596_ = lean_ctor_get(v_e_3592_, 1);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_e_3592_);
if (v_isSharedCheck_3605_ == 0)
{
lean_object* v_unused_3606_; 
v_unused_3606_ = lean_ctor_get(v_e_3592_, 2);
lean_dec(v_unused_3606_);
v___x_3598_ = v_e_3592_;
v_isShared_3599_ = v_isSharedCheck_3605_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_message_3596_);
lean_inc(v_id_3594_);
lean_dec(v_e_3592_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3605_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3600_ = lean_box(0);
if (v_isShared_3599_ == 0)
{
lean_ctor_set_tag(v___x_3598_, 3);
lean_ctor_set(v___x_3598_, 2, v___x_3600_);
v___x_3602_ = v___x_3598_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_id_3594_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_message_3596_);
lean_ctor_set(v_reuseFailAlloc_3604_, 2, v___x_3600_);
lean_ctor_set_uint8(v_reuseFailAlloc_3604_, sizeof(void*)*3, v_code_3595_);
v___x_3602_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_IO_FS_Stream_writeMessage(v_h_3591_, v___x_3602_);
return v___x_3603_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object* v_h_3607_, lean_object* v_e_3608_, lean_object* v_a_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_IO_FS_Stream_writeResponseError(v_h_3607_, v_e_3608_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* v_inst_3611_, lean_object* v_h_3612_, lean_object* v_e_3613_){
_start:
{
lean_object* v_id_3615_; uint8_t v_code_3616_; lean_object* v_message_3617_; lean_object* v_data_x3f_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3638_; 
v_id_3615_ = lean_ctor_get(v_e_3613_, 0);
v_code_3616_ = lean_ctor_get_uint8(v_e_3613_, sizeof(void*)*3);
v_message_3617_ = lean_ctor_get(v_e_3613_, 1);
v_data_x3f_3618_ = lean_ctor_get(v_e_3613_, 2);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_e_3613_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3620_ = v_e_3613_;
v_isShared_3621_ = v_isSharedCheck_3638_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_data_x3f_3618_);
lean_inc(v_message_3617_);
lean_inc(v_id_3615_);
lean_dec(v_e_3613_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3638_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___y_3623_; 
if (lean_obj_tag(v_data_x3f_3618_) == 0)
{
lean_object* v___x_3628_; 
lean_dec_ref(v_inst_3611_);
v___x_3628_ = lean_box(0);
v___y_3623_ = v___x_3628_;
goto v___jp_3622_;
}
else
{
lean_object* v_val_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3637_; 
v_val_3629_ = lean_ctor_get(v_data_x3f_3618_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_data_x3f_3618_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3631_ = v_data_x3f_3618_;
v_isShared_3632_ = v_isSharedCheck_3637_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_val_3629_);
lean_dec(v_data_x3f_3618_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3637_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v___x_3635_; 
v___x_3633_ = lean_apply_1(v_inst_3611_, v_val_3629_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v___x_3633_);
v___x_3635_ = v___x_3631_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
v___y_3623_ = v___x_3635_;
goto v___jp_3622_;
}
}
}
v___jp_3622_:
{
lean_object* v___x_3625_; 
if (v_isShared_3621_ == 0)
{
lean_ctor_set_tag(v___x_3620_, 3);
lean_ctor_set(v___x_3620_, 2, v___y_3623_);
v___x_3625_ = v___x_3620_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_id_3615_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_message_3617_);
lean_ctor_set(v_reuseFailAlloc_3627_, 2, v___y_3623_);
lean_ctor_set_uint8(v_reuseFailAlloc_3627_, sizeof(void*)*3, v_code_3616_);
v___x_3625_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_IO_FS_Stream_writeMessage(v_h_3612_, v___x_3625_);
return v___x_3626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object* v_inst_3639_, lean_object* v_h_3640_, lean_object* v_e_3641_, lean_object* v_a_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3639_, v_h_3640_, v_e_3641_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object* v_00_u03b1_3644_, lean_object* v_inst_3645_, lean_object* v_h_3646_, lean_object* v_e_3647_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3645_, v_h_3646_, v_e_3647_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object* v_00_u03b1_3650_, lean_object* v_inst_3651_, lean_object* v_h_3652_, lean_object* v_e_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_IO_FS_Stream_writeResponseErrorWithData(v_00_u03b1_3650_, v_inst_3651_, v_h_3652_, v_e_3653_);
return v_res_3655_;
}
}
lean_object* runtime_initialize_Lean_Data_Json_Stream(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_JsonRpc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
