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
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
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
lean_dec_ref_known(v_x_85_, 1);
v_s_88_ = lean_ctor_get(v_x_86_, 0);
lean_inc_ref(v_s_88_);
lean_dec_ref_known(v_x_86_, 1);
v___x_89_ = lean_string_compare(v_s_87_, v_s_88_);
lean_dec_ref(v_s_88_);
lean_dec_ref(v_s_87_);
if (v___x_89_ == 1)
{
return v___x_89_;
}
else
{
return v___x_89_;
}
}
case 1:
{
uint8_t v___x_90_; 
lean_dec_ref_known(v_x_86_, 1);
lean_dec_ref_known(v_x_85_, 1);
v___x_90_ = 0;
return v___x_90_;
}
default: 
{
uint8_t v___x_91_; 
lean_dec_ref_known(v_x_85_, 1);
lean_dec(v_x_86_);
v___x_91_ = 0;
return v___x_91_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_86_))
{
case 0:
{
uint8_t v___x_92_; 
lean_dec_ref_known(v_x_86_, 1);
lean_dec_ref_known(v_x_85_, 1);
v___x_92_ = 2;
return v___x_92_;
}
case 1:
{
lean_object* v_n_93_; lean_object* v_n_94_; uint8_t v___x_95_; 
v_n_93_ = lean_ctor_get(v_x_85_, 0);
lean_inc_ref_n(v_n_93_, 2);
lean_dec_ref_known(v_x_85_, 1);
v_n_94_ = lean_ctor_get(v_x_86_, 0);
lean_inc_ref_n(v_n_94_, 2);
lean_dec_ref_known(v_x_86_, 1);
v___x_95_ = l_Lean_JsonNumber_lt(v_n_93_, v_n_94_);
if (v___x_95_ == 0)
{
uint8_t v___x_96_; 
v___x_96_ = l_Lean_JsonNumber_lt(v_n_94_, v_n_93_);
if (v___x_96_ == 0)
{
uint8_t v___x_97_; 
v___x_97_ = 1;
return v___x_97_;
}
else
{
uint8_t v___x_98_; 
v___x_98_ = 2;
return v___x_98_;
}
}
else
{
uint8_t v___x_99_; 
lean_dec_ref(v_n_94_);
lean_dec_ref(v_n_93_);
v___x_99_ = 0;
return v___x_99_;
}
}
default: 
{
uint8_t v___x_100_; 
lean_dec_ref_known(v_x_85_, 1);
lean_dec(v_x_86_);
v___x_100_ = 0;
return v___x_100_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_86_) == 2)
{
uint8_t v___x_101_; 
v___x_101_ = 1;
return v___x_101_;
}
else
{
uint8_t v___x_102_; 
lean_dec(v_x_86_);
v___x_102_ = 2;
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID_ord___boxed(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Lean_JsonRpc_instOrdRequestID_ord(v_x_103_, v_x_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOfNatRequestID(lean_object* v_n_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = l_Lean_JsonNumber_fromNat(v_n_109_);
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0(lean_object* v_x_114_){
_start:
{
switch(lean_obj_tag(v_x_114_))
{
case 0:
{
lean_object* v_s_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_s_115_ = lean_ctor_get(v_x_114_, 0);
lean_inc_ref(v_s_115_);
lean_dec_ref_known(v_x_114_, 1);
v___x_116_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_117_ = lean_string_append(v___x_116_, v_s_115_);
lean_dec_ref(v_s_115_);
v___x_118_ = lean_string_append(v___x_117_, v___x_116_);
return v___x_118_;
}
case 1:
{
lean_object* v_n_119_; lean_object* v___x_120_; 
v_n_119_ = lean_ctor_get(v_x_114_, 0);
lean_inc_ref(v_n_119_);
lean_dec_ref_known(v_x_114_, 1);
v___x_120_ = l_Lean_JsonNumber_toString(v_n_119_);
return v___x_120_;
}
default: 
{
lean_object* v___x_121_; 
v___x_121_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx(uint8_t v_x_124_){
_start:
{
switch(v_x_124_)
{
case 0:
{
lean_object* v___x_125_; 
v___x_125_ = lean_unsigned_to_nat(0u);
return v___x_125_;
}
case 1:
{
lean_object* v___x_126_; 
v___x_126_ = lean_unsigned_to_nat(1u);
return v___x_126_;
}
case 2:
{
lean_object* v___x_127_; 
v___x_127_ = lean_unsigned_to_nat(2u);
return v___x_127_;
}
case 3:
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(3u);
return v___x_128_;
}
case 4:
{
lean_object* v___x_129_; 
v___x_129_ = lean_unsigned_to_nat(4u);
return v___x_129_;
}
case 5:
{
lean_object* v___x_130_; 
v___x_130_ = lean_unsigned_to_nat(5u);
return v___x_130_;
}
case 6:
{
lean_object* v___x_131_; 
v___x_131_ = lean_unsigned_to_nat(6u);
return v___x_131_;
}
case 7:
{
lean_object* v___x_132_; 
v___x_132_ = lean_unsigned_to_nat(7u);
return v___x_132_;
}
case 8:
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(8u);
return v___x_133_;
}
case 9:
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(9u);
return v___x_134_;
}
case 10:
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(10u);
return v___x_135_;
}
default: 
{
lean_object* v___x_136_; 
v___x_136_ = lean_unsigned_to_nat(11u);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___boxed(lean_object* v_x_137_){
_start:
{
uint8_t v_x_boxed_138_; lean_object* v_res_139_; 
v_x_boxed_138_ = lean_unbox(v_x_137_);
v_res_139_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_boxed_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(lean_object* v_k_140_){
_start:
{
lean_inc(v_k_140_);
return v_k_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg___boxed(lean_object* v_k_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(v_k_141_);
lean_dec(v_k_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim(lean_object* v_motive_143_, lean_object* v_ctorIdx_144_, uint8_t v_t_145_, lean_object* v_h_146_, lean_object* v_k_147_){
_start:
{
lean_inc(v_k_147_);
return v_k_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___boxed(lean_object* v_motive_148_, lean_object* v_ctorIdx_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_k_152_){
_start:
{
uint8_t v_t_boxed_153_; lean_object* v_res_154_; 
v_t_boxed_153_ = lean_unbox(v_t_150_);
v_res_154_ = l_Lean_JsonRpc_ErrorCode_ctorElim(v_motive_148_, v_ctorIdx_149_, v_t_boxed_153_, v_h_151_, v_k_152_);
lean_dec(v_k_152_);
lean_dec(v_ctorIdx_149_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(lean_object* v_parseError_155_){
_start:
{
lean_inc(v_parseError_155_);
return v_parseError_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg___boxed(lean_object* v_parseError_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(v_parseError_156_);
lean_dec(v_parseError_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_object* v_motive_158_, uint8_t v_t_159_, lean_object* v_h_160_, lean_object* v_parseError_161_){
_start:
{
lean_inc(v_parseError_161_);
return v_parseError_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___boxed(lean_object* v_motive_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_parseError_165_){
_start:
{
uint8_t v_t_boxed_166_; lean_object* v_res_167_; 
v_t_boxed_166_ = lean_unbox(v_t_163_);
v_res_167_ = l_Lean_JsonRpc_ErrorCode_parseError_elim(v_motive_162_, v_t_boxed_166_, v_h_164_, v_parseError_165_);
lean_dec(v_parseError_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(lean_object* v_invalidRequest_168_){
_start:
{
lean_inc(v_invalidRequest_168_);
return v_invalidRequest_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg___boxed(lean_object* v_invalidRequest_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(v_invalidRequest_169_);
lean_dec(v_invalidRequest_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_object* v_motive_171_, uint8_t v_t_172_, lean_object* v_h_173_, lean_object* v_invalidRequest_174_){
_start:
{
lean_inc(v_invalidRequest_174_);
return v_invalidRequest_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___boxed(lean_object* v_motive_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_invalidRequest_178_){
_start:
{
uint8_t v_t_boxed_179_; lean_object* v_res_180_; 
v_t_boxed_179_ = lean_unbox(v_t_176_);
v_res_180_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(v_motive_175_, v_t_boxed_179_, v_h_177_, v_invalidRequest_178_);
lean_dec(v_invalidRequest_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(lean_object* v_methodNotFound_181_){
_start:
{
lean_inc(v_methodNotFound_181_);
return v_methodNotFound_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg___boxed(lean_object* v_methodNotFound_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(v_methodNotFound_182_);
lean_dec(v_methodNotFound_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(lean_object* v_motive_184_, uint8_t v_t_185_, lean_object* v_h_186_, lean_object* v_methodNotFound_187_){
_start:
{
lean_inc(v_methodNotFound_187_);
return v_methodNotFound_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___boxed(lean_object* v_motive_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_methodNotFound_191_){
_start:
{
uint8_t v_t_boxed_192_; lean_object* v_res_193_; 
v_t_boxed_192_ = lean_unbox(v_t_189_);
v_res_193_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(v_motive_188_, v_t_boxed_192_, v_h_190_, v_methodNotFound_191_);
lean_dec(v_methodNotFound_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(lean_object* v_invalidParams_194_){
_start:
{
lean_inc(v_invalidParams_194_);
return v_invalidParams_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg___boxed(lean_object* v_invalidParams_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(v_invalidParams_195_);
lean_dec(v_invalidParams_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_object* v_motive_197_, uint8_t v_t_198_, lean_object* v_h_199_, lean_object* v_invalidParams_200_){
_start:
{
lean_inc(v_invalidParams_200_);
return v_invalidParams_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___boxed(lean_object* v_motive_201_, lean_object* v_t_202_, lean_object* v_h_203_, lean_object* v_invalidParams_204_){
_start:
{
uint8_t v_t_boxed_205_; lean_object* v_res_206_; 
v_t_boxed_205_ = lean_unbox(v_t_202_);
v_res_206_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim(v_motive_201_, v_t_boxed_205_, v_h_203_, v_invalidParams_204_);
lean_dec(v_invalidParams_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(lean_object* v_internalError_207_){
_start:
{
lean_inc(v_internalError_207_);
return v_internalError_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg___boxed(lean_object* v_internalError_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(v_internalError_208_);
lean_dec(v_internalError_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_object* v_motive_210_, uint8_t v_t_211_, lean_object* v_h_212_, lean_object* v_internalError_213_){
_start:
{
lean_inc(v_internalError_213_);
return v_internalError_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___boxed(lean_object* v_motive_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_internalError_217_){
_start:
{
uint8_t v_t_boxed_218_; lean_object* v_res_219_; 
v_t_boxed_218_ = lean_unbox(v_t_215_);
v_res_219_ = l_Lean_JsonRpc_ErrorCode_internalError_elim(v_motive_214_, v_t_boxed_218_, v_h_216_, v_internalError_217_);
lean_dec(v_internalError_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(lean_object* v_serverNotInitialized_220_){
_start:
{
lean_inc(v_serverNotInitialized_220_);
return v_serverNotInitialized_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg___boxed(lean_object* v_serverNotInitialized_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(v_serverNotInitialized_221_);
lean_dec(v_serverNotInitialized_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_object* v_motive_223_, uint8_t v_t_224_, lean_object* v_h_225_, lean_object* v_serverNotInitialized_226_){
_start:
{
lean_inc(v_serverNotInitialized_226_);
return v_serverNotInitialized_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___boxed(lean_object* v_motive_227_, lean_object* v_t_228_, lean_object* v_h_229_, lean_object* v_serverNotInitialized_230_){
_start:
{
uint8_t v_t_boxed_231_; lean_object* v_res_232_; 
v_t_boxed_231_ = lean_unbox(v_t_228_);
v_res_232_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(v_motive_227_, v_t_boxed_231_, v_h_229_, v_serverNotInitialized_230_);
lean_dec(v_serverNotInitialized_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(lean_object* v_unknownErrorCode_233_){
_start:
{
lean_inc(v_unknownErrorCode_233_);
return v_unknownErrorCode_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg___boxed(lean_object* v_unknownErrorCode_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(v_unknownErrorCode_234_);
lean_dec(v_unknownErrorCode_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_object* v_motive_236_, uint8_t v_t_237_, lean_object* v_h_238_, lean_object* v_unknownErrorCode_239_){
_start:
{
lean_inc(v_unknownErrorCode_239_);
return v_unknownErrorCode_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___boxed(lean_object* v_motive_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_unknownErrorCode_243_){
_start:
{
uint8_t v_t_boxed_244_; lean_object* v_res_245_; 
v_t_boxed_244_ = lean_unbox(v_t_241_);
v_res_245_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(v_motive_240_, v_t_boxed_244_, v_h_242_, v_unknownErrorCode_243_);
lean_dec(v_unknownErrorCode_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(lean_object* v_contentModified_246_){
_start:
{
lean_inc(v_contentModified_246_);
return v_contentModified_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg___boxed(lean_object* v_contentModified_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(v_contentModified_247_);
lean_dec(v_contentModified_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_object* v_motive_249_, uint8_t v_t_250_, lean_object* v_h_251_, lean_object* v_contentModified_252_){
_start:
{
lean_inc(v_contentModified_252_);
return v_contentModified_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___boxed(lean_object* v_motive_253_, lean_object* v_t_254_, lean_object* v_h_255_, lean_object* v_contentModified_256_){
_start:
{
uint8_t v_t_boxed_257_; lean_object* v_res_258_; 
v_t_boxed_257_ = lean_unbox(v_t_254_);
v_res_258_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim(v_motive_253_, v_t_boxed_257_, v_h_255_, v_contentModified_256_);
lean_dec(v_contentModified_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(lean_object* v_requestCancelled_259_){
_start:
{
lean_inc(v_requestCancelled_259_);
return v_requestCancelled_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg___boxed(lean_object* v_requestCancelled_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(v_requestCancelled_260_);
lean_dec(v_requestCancelled_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_object* v_motive_262_, uint8_t v_t_263_, lean_object* v_h_264_, lean_object* v_requestCancelled_265_){
_start:
{
lean_inc(v_requestCancelled_265_);
return v_requestCancelled_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___boxed(lean_object* v_motive_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_requestCancelled_269_){
_start:
{
uint8_t v_t_boxed_270_; lean_object* v_res_271_; 
v_t_boxed_270_ = lean_unbox(v_t_267_);
v_res_271_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(v_motive_266_, v_t_boxed_270_, v_h_268_, v_requestCancelled_269_);
lean_dec(v_requestCancelled_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(lean_object* v_rpcNeedsReconnect_272_){
_start:
{
lean_inc(v_rpcNeedsReconnect_272_);
return v_rpcNeedsReconnect_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg___boxed(lean_object* v_rpcNeedsReconnect_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(v_rpcNeedsReconnect_273_);
lean_dec(v_rpcNeedsReconnect_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(lean_object* v_motive_275_, uint8_t v_t_276_, lean_object* v_h_277_, lean_object* v_rpcNeedsReconnect_278_){
_start:
{
lean_inc(v_rpcNeedsReconnect_278_);
return v_rpcNeedsReconnect_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___boxed(lean_object* v_motive_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_rpcNeedsReconnect_282_){
_start:
{
uint8_t v_t_boxed_283_; lean_object* v_res_284_; 
v_t_boxed_283_ = lean_unbox(v_t_280_);
v_res_284_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(v_motive_279_, v_t_boxed_283_, v_h_281_, v_rpcNeedsReconnect_282_);
lean_dec(v_rpcNeedsReconnect_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(lean_object* v_workerExited_285_){
_start:
{
lean_inc(v_workerExited_285_);
return v_workerExited_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg___boxed(lean_object* v_workerExited_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(v_workerExited_286_);
lean_dec(v_workerExited_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim(lean_object* v_motive_288_, uint8_t v_t_289_, lean_object* v_h_290_, lean_object* v_workerExited_291_){
_start:
{
lean_inc(v_workerExited_291_);
return v_workerExited_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___boxed(lean_object* v_motive_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_workerExited_295_){
_start:
{
uint8_t v_t_boxed_296_; lean_object* v_res_297_; 
v_t_boxed_296_ = lean_unbox(v_t_293_);
v_res_297_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim(v_motive_292_, v_t_boxed_296_, v_h_294_, v_workerExited_295_);
lean_dec(v_workerExited_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(lean_object* v_workerCrashed_298_){
_start:
{
lean_inc(v_workerCrashed_298_);
return v_workerCrashed_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg___boxed(lean_object* v_workerCrashed_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(v_workerCrashed_299_);
lean_dec(v_workerCrashed_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_object* v_motive_301_, uint8_t v_t_302_, lean_object* v_h_303_, lean_object* v_workerCrashed_304_){
_start:
{
lean_inc(v_workerCrashed_304_);
return v_workerCrashed_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___boxed(lean_object* v_motive_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_workerCrashed_308_){
_start:
{
uint8_t v_t_boxed_309_; lean_object* v_res_310_; 
v_t_boxed_309_ = lean_unbox(v_t_306_);
v_res_310_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(v_motive_305_, v_t_boxed_309_, v_h_307_, v_workerCrashed_308_);
lean_dec(v_workerCrashed_308_);
return v_res_310_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode_default(void){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = 0;
return v___x_311_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode(void){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = 0;
return v___x_312_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqErrorCode_beq(uint8_t v_x_313_, uint8_t v_y_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_315_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_313_);
v___x_316_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_y_314_);
v___x_317_ = lean_nat_dec_eq(v___x_315_, v___x_316_);
lean_dec(v___x_316_);
lean_dec(v___x_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode_beq___boxed(lean_object* v_x_318_, lean_object* v_y_319_){
_start:
{
uint8_t v_x_21__boxed_320_; uint8_t v_y_22__boxed_321_; uint8_t v_res_322_; lean_object* v_r_323_; 
v_x_21__boxed_320_ = lean_unbox(v_x_318_);
v_y_22__boxed_321_ = lean_unbox(v_y_319_);
v_res_322_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_x_21__boxed_320_, v_y_22__boxed_321_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(32700u);
v___x_330_ = lean_nat_to_int(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2);
v___x_332_ = lean_int_neg(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(32600u);
v___x_334_ = lean_nat_to_int(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4);
v___x_336_ = lean_int_neg(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(32601u);
v___x_338_ = lean_nat_to_int(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6);
v___x_340_ = lean_int_neg(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(32602u);
v___x_342_ = lean_nat_to_int(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8);
v___x_344_ = lean_int_neg(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(32603u);
v___x_346_ = lean_nat_to_int(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10);
v___x_348_ = lean_int_neg(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_unsigned_to_nat(32002u);
v___x_350_ = lean_nat_to_int(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12);
v___x_352_ = lean_int_neg(v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(32001u);
v___x_354_ = lean_nat_to_int(v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14);
v___x_356_ = lean_int_neg(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_unsigned_to_nat(32801u);
v___x_358_ = lean_nat_to_int(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16);
v___x_360_ = lean_int_neg(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_unsigned_to_nat(32800u);
v___x_362_ = lean_nat_to_int(v___x_361_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18);
v___x_364_ = lean_int_neg(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_unsigned_to_nat(32900u);
v___x_366_ = lean_nat_to_int(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20);
v___x_368_ = lean_int_neg(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_unsigned_to_nat(32901u);
v___x_370_ = lean_nat_to_int(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22);
v___x_372_ = lean_int_neg(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_unsigned_to_nat(32902u);
v___x_374_ = lean_nat_to_int(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24);
v___x_376_ = lean_int_neg(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_413_) == 2)
{
lean_object* v_n_416_; lean_object* v_mantissa_417_; lean_object* v_exponent_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_n_416_ = lean_ctor_get(v_x_413_, 0);
v_mantissa_417_ = lean_ctor_get(v_n_416_, 0);
v_exponent_418_ = lean_ctor_get(v_n_416_, 1);
v___x_419_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_420_ = lean_int_dec_eq(v_mantissa_417_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_422_ = lean_int_dec_eq(v_mantissa_417_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_424_ = lean_int_dec_eq(v_mantissa_417_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_426_ = lean_int_dec_eq(v_mantissa_417_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_428_ = lean_int_dec_eq(v_mantissa_417_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_430_ = lean_int_dec_eq(v_mantissa_417_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_432_ = lean_int_dec_eq(v_mantissa_417_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_434_ = lean_int_dec_eq(v_mantissa_417_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_436_ = lean_int_dec_eq(v_mantissa_417_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_438_ = lean_int_dec_eq(v_mantissa_417_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_440_ = lean_int_dec_eq(v_mantissa_417_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_442_ = lean_int_dec_eq(v_mantissa_417_, v___x_441_);
if (v___x_442_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_nat_dec_eq(v_exponent_418_, v___x_443_);
if (v___x_444_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_445_; 
v___x_445_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_445_;
}
}
}
else
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_nat_dec_eq(v_exponent_418_, v___x_446_);
if (v___x_447_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_448_;
}
}
}
else
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_nat_dec_eq(v_exponent_418_, v___x_449_);
if (v___x_450_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_451_;
}
}
}
else
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_nat_dec_eq(v_exponent_418_, v___x_452_);
if (v___x_453_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_454_; 
v___x_454_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_454_;
}
}
}
else
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_nat_dec_eq(v_exponent_418_, v___x_455_);
if (v___x_456_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_457_;
}
}
}
else
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = lean_nat_dec_eq(v_exponent_418_, v___x_458_);
if (v___x_459_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_460_;
}
}
}
else
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_nat_dec_eq(v_exponent_418_, v___x_461_);
if (v___x_462_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_463_; 
v___x_463_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_463_;
}
}
}
else
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_nat_dec_eq(v_exponent_418_, v___x_464_);
if (v___x_465_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_466_; 
v___x_466_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_466_;
}
}
}
else
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_nat_dec_eq(v_exponent_418_, v___x_467_);
if (v___x_468_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_469_; 
v___x_469_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_469_;
}
}
}
else
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_nat_dec_eq(v_exponent_418_, v___x_470_);
if (v___x_471_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_472_;
}
}
}
else
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_nat_dec_eq(v_exponent_418_, v___x_473_);
if (v___x_474_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_475_;
}
}
}
else
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_nat_dec_eq(v_exponent_418_, v___x_476_);
if (v___x_477_ == 0)
{
goto v___jp_414_;
}
else
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_478_;
}
}
}
else
{
goto v___jp_414_;
}
v___jp_414_:
{
lean_object* v___x_415_; 
v___x_415_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed(lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(v_x_479_);
lean_dec(v_x_479_);
return v_res_480_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_484_ = l_Lean_JsonNumber_fromInt(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0);
v___x_486_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_488_ = l_Lean_JsonNumber_fromInt(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2);
v___x_490_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_492_ = l_Lean_JsonNumber_fromInt(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4);
v___x_494_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_496_ = l_Lean_JsonNumber_fromInt(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6);
v___x_498_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_500_ = l_Lean_JsonNumber_fromInt(v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8);
v___x_502_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_504_ = l_Lean_JsonNumber_fromInt(v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10);
v___x_506_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_508_ = l_Lean_JsonNumber_fromInt(v___x_507_);
return v___x_508_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12);
v___x_510_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_512_ = l_Lean_JsonNumber_fromInt(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14);
v___x_514_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_516_ = l_Lean_JsonNumber_fromInt(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16);
v___x_518_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_520_ = l_Lean_JsonNumber_fromInt(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18);
v___x_522_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_524_ = l_Lean_JsonNumber_fromInt(v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20);
v___x_526_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_528_ = l_Lean_JsonNumber_fromInt(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22);
v___x_530_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t v_x_531_){
_start:
{
switch(v_x_531_)
{
case 0:
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
return v___x_532_;
}
case 1:
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
return v___x_533_;
}
case 2:
{
lean_object* v___x_534_; 
v___x_534_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
return v___x_534_;
}
case 3:
{
lean_object* v___x_535_; 
v___x_535_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
return v___x_535_;
}
case 4:
{
lean_object* v___x_536_; 
v___x_536_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
return v___x_536_;
}
case 5:
{
lean_object* v___x_537_; 
v___x_537_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
return v___x_537_;
}
case 6:
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
return v___x_538_;
}
case 7:
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
return v___x_539_;
}
case 8:
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
return v___x_540_;
}
case 9:
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
return v___x_541_;
}
case 10:
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
return v___x_542_;
}
default: 
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object* v_x_544_){
_start:
{
uint8_t v_x_474__boxed_545_; lean_object* v_res_546_; 
v_x_474__boxed_545_ = lean_unbox(v_x_544_);
v_res_546_ = l_Lean_JsonRpc_instToJsonErrorCode___lam__0(v_x_474__boxed_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx(lean_object* v_x_549_){
_start:
{
switch(lean_obj_tag(v_x_549_))
{
case 0:
{
lean_object* v___x_550_; 
v___x_550_ = lean_unsigned_to_nat(0u);
return v___x_550_;
}
case 1:
{
lean_object* v___x_551_; 
v___x_551_ = lean_unsigned_to_nat(1u);
return v___x_551_;
}
case 2:
{
lean_object* v___x_552_; 
v___x_552_ = lean_unsigned_to_nat(2u);
return v___x_552_;
}
default: 
{
lean_object* v___x_553_; 
v___x_553_ = lean_unsigned_to_nat(3u);
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___boxed(lean_object* v_x_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_JsonRpc_Message_ctorIdx(v_x_554_);
lean_dec_ref(v_x_554_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___redArg(lean_object* v_t_556_, lean_object* v_k_557_){
_start:
{
switch(lean_obj_tag(v_t_556_))
{
case 0:
{
lean_object* v_id_558_; lean_object* v_method_559_; lean_object* v_params_x3f_560_; lean_object* v___x_561_; 
v_id_558_ = lean_ctor_get(v_t_556_, 0);
lean_inc(v_id_558_);
v_method_559_ = lean_ctor_get(v_t_556_, 1);
lean_inc_ref(v_method_559_);
v_params_x3f_560_ = lean_ctor_get(v_t_556_, 2);
lean_inc(v_params_x3f_560_);
lean_dec_ref_known(v_t_556_, 3);
v___x_561_ = lean_apply_3(v_k_557_, v_id_558_, v_method_559_, v_params_x3f_560_);
return v___x_561_;
}
case 1:
{
lean_object* v_method_562_; lean_object* v_params_x3f_563_; lean_object* v___x_564_; 
v_method_562_ = lean_ctor_get(v_t_556_, 0);
lean_inc_ref(v_method_562_);
v_params_x3f_563_ = lean_ctor_get(v_t_556_, 1);
lean_inc(v_params_x3f_563_);
lean_dec_ref_known(v_t_556_, 2);
v___x_564_ = lean_apply_2(v_k_557_, v_method_562_, v_params_x3f_563_);
return v___x_564_;
}
case 2:
{
lean_object* v_id_565_; lean_object* v_result_566_; lean_object* v___x_567_; 
v_id_565_ = lean_ctor_get(v_t_556_, 0);
lean_inc(v_id_565_);
v_result_566_ = lean_ctor_get(v_t_556_, 1);
lean_inc(v_result_566_);
lean_dec_ref_known(v_t_556_, 2);
v___x_567_ = lean_apply_2(v_k_557_, v_id_565_, v_result_566_);
return v___x_567_;
}
default: 
{
lean_object* v_id_568_; uint8_t v_code_569_; lean_object* v_message_570_; lean_object* v_data_x3f_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_id_568_ = lean_ctor_get(v_t_556_, 0);
lean_inc(v_id_568_);
v_code_569_ = lean_ctor_get_uint8(v_t_556_, sizeof(void*)*3);
v_message_570_ = lean_ctor_get(v_t_556_, 1);
lean_inc_ref(v_message_570_);
v_data_x3f_571_ = lean_ctor_get(v_t_556_, 2);
lean_inc(v_data_x3f_571_);
lean_dec_ref_known(v_t_556_, 3);
v___x_572_ = lean_box(v_code_569_);
v___x_573_ = lean_apply_4(v_k_557_, v_id_568_, v___x_572_, v_message_570_, v_data_x3f_571_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim(lean_object* v_motive_574_, lean_object* v_ctorIdx_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_k_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_576_, v_k_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___boxed(lean_object* v_motive_580_, lean_object* v_ctorIdx_581_, lean_object* v_t_582_, lean_object* v_h_583_, lean_object* v_k_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_JsonRpc_Message_ctorElim(v_motive_580_, v_ctorIdx_581_, v_t_582_, v_h_583_, v_k_584_);
lean_dec(v_ctorIdx_581_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim___redArg(lean_object* v_t_586_, lean_object* v_request_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_586_, v_request_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim(lean_object* v_motive_589_, lean_object* v_t_590_, lean_object* v_h_591_, lean_object* v_request_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_590_, v_request_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim___redArg(lean_object* v_t_594_, lean_object* v_notification_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_594_, v_notification_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim(lean_object* v_motive_597_, lean_object* v_t_598_, lean_object* v_h_599_, lean_object* v_notification_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_598_, v_notification_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim___redArg(lean_object* v_t_602_, lean_object* v_response_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_602_, v_response_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim(lean_object* v_motive_605_, lean_object* v_t_606_, lean_object* v_h_607_, lean_object* v_response_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_606_, v_response_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim___redArg(lean_object* v_t_610_, lean_object* v_responseError_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_610_, v_responseError_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim(lean_object* v_motive_613_, lean_object* v_t_614_, lean_object* v_h_615_, lean_object* v_responseError_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_614_, v_responseError_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default___redArg(lean_object* v_inst_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default));
v___x_626_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
lean_ctor_set(v___x_627_, 2, v_inst_624_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default(lean_object* v_00_u03b1_628_, lean_object* v_inst_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___redArg(lean_object* v_inst_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object* v_a_633_, lean_object* v_inst_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_634_);
return v___x_635_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq___redArg(lean_object* v_inst_636_, lean_object* v_x_637_, lean_object* v_x_638_){
_start:
{
lean_object* v_id_639_; lean_object* v_method_640_; lean_object* v_param_641_; lean_object* v_id_642_; lean_object* v_method_643_; lean_object* v_param_644_; uint8_t v___x_645_; 
v_id_639_ = lean_ctor_get(v_x_637_, 0);
lean_inc(v_id_639_);
v_method_640_ = lean_ctor_get(v_x_637_, 1);
lean_inc_ref(v_method_640_);
v_param_641_ = lean_ctor_get(v_x_637_, 2);
lean_inc(v_param_641_);
lean_dec_ref(v_x_637_);
v_id_642_ = lean_ctor_get(v_x_638_, 0);
lean_inc(v_id_642_);
v_method_643_ = lean_ctor_get(v_x_638_, 1);
lean_inc_ref(v_method_643_);
v_param_644_ = lean_ctor_get(v_x_638_, 2);
lean_inc(v_param_644_);
lean_dec_ref(v_x_638_);
v___x_645_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_639_, v_id_642_);
lean_dec(v_id_642_);
lean_dec(v_id_639_);
if (v___x_645_ == 0)
{
lean_dec(v_param_644_);
lean_dec_ref(v_method_643_);
lean_dec(v_param_641_);
lean_dec_ref(v_method_640_);
lean_dec_ref(v_inst_636_);
return v___x_645_;
}
else
{
uint8_t v___x_646_; 
v___x_646_ = lean_string_dec_eq(v_method_640_, v_method_643_);
lean_dec_ref(v_method_643_);
lean_dec_ref(v_method_640_);
if (v___x_646_ == 0)
{
lean_dec(v_param_644_);
lean_dec(v_param_641_);
lean_dec_ref(v_inst_636_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_apply_2(v_inst_636_, v_param_641_, v_param_644_);
v___x_648_ = lean_unbox(v___x_647_);
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___redArg___boxed(lean_object* v_inst_649_, lean_object* v_x_650_, lean_object* v_x_651_){
_start:
{
uint8_t v_res_652_; lean_object* v_r_653_; 
v_res_652_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_649_, v_x_650_, v_x_651_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq(lean_object* v_00_u03b1_654_, lean_object* v_inst_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
uint8_t v___x_658_; 
v___x_658_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_655_, v_x_656_, v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___boxed(lean_object* v_00_u03b1_659_, lean_object* v_inst_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
uint8_t v_res_663_; lean_object* v_r_664_; 
v_res_663_ = l_Lean_JsonRpc_instBEqRequest_beq(v_00_u03b1_659_, v_inst_660_, v_x_661_, v_x_662_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object* v_inst_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_666_, 0, lean_box(0));
lean_closure_set(v___x_666_, 1, v_inst_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object* v_00_u03b1_667_, lean_object* v_inst_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_669_, 0, lean_box(0));
lean_closure_set(v___x_669_, 1, v_inst_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object* v_inst_670_, lean_object* v_r_671_){
_start:
{
lean_object* v_id_672_; lean_object* v_method_673_; lean_object* v_param_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_694_; 
v_id_672_ = lean_ctor_get(v_r_671_, 0);
v_method_673_ = lean_ctor_get(v_r_671_, 1);
v_param_674_ = lean_ctor_get(v_r_671_, 2);
v_isSharedCheck_694_ = !lean_is_exclusive(v_r_671_);
if (v_isSharedCheck_694_ == 0)
{
v___x_676_ = v_r_671_;
v_isShared_677_ = v_isSharedCheck_694_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_param_674_);
lean_inc(v_method_673_);
lean_inc(v_id_672_);
lean_dec(v_r_671_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_694_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_670_, v_param_674_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v___x_679_; lean_object* v___x_681_; 
lean_dec_ref_known(v___x_678_, 1);
v___x_679_ = lean_box(0);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 2, v___x_679_);
v___x_681_ = v___x_676_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_id_672_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_method_673_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_693_; 
v_a_683_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_693_ == 0)
{
v___x_685_ = v___x_678_;
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_678_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 2, v___x_688_);
v___x_690_ = v___x_676_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_id_672_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_method_673_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object* v_inst_695_){
_start:
{
lean_object* v___f_696_; 
v___f_696_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_696_, 0, v_inst_695_);
return v___f_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object* v_00_u03b1_697_, lean_object* v_inst_698_){
_start:
{
lean_object* v___f_699_; 
v___f_699_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_699_, 0, v_inst_698_);
return v___f_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_700_) == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_box(0);
return v___x_701_;
}
else
{
lean_object* v_val_702_; lean_object* v___x_703_; 
v_val_702_ = lean_ctor_get(v_x_700_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v_x_700_, 1);
v___x_703_ = l_Lean_Json_Structured_toJson(v_val_702_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ofMessage_x3f(lean_object* v_x_704_){
_start:
{
if (lean_obj_tag(v_x_704_) == 0)
{
lean_object* v_id_705_; lean_object* v_method_706_; lean_object* v_params_x3f_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_716_; 
v_id_705_ = lean_ctor_get(v_x_704_, 0);
v_method_706_ = lean_ctor_get(v_x_704_, 1);
v_params_x3f_707_ = lean_ctor_get(v_x_704_, 2);
v_isSharedCheck_716_ = !lean_is_exclusive(v_x_704_);
if (v_isSharedCheck_716_ == 0)
{
v___x_709_ = v_x_704_;
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_params_x3f_707_);
lean_inc(v_method_706_);
lean_inc(v_id_705_);
lean_dec(v_x_704_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_707_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 2, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_id_705_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_method_706_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v___x_711_);
v___x_713_ = v_reuseFailAlloc_715_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
}
else
{
lean_object* v___x_717_; 
lean_dec_ref(v_x_704_);
v___x_717_ = lean_box(0);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default___redArg(lean_object* v_inst_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v_inst_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default(lean_object* v_00_u03b1_721_, lean_object* v_inst_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___redArg(lean_object* v_inst_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object* v_a_726_, lean_object* v_inst_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_727_);
return v___x_728_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq___redArg(lean_object* v_inst_729_, lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
lean_object* v_method_732_; lean_object* v_param_733_; lean_object* v_method_734_; lean_object* v_param_735_; uint8_t v___x_736_; 
v_method_732_ = lean_ctor_get(v_x_730_, 0);
lean_inc_ref(v_method_732_);
v_param_733_ = lean_ctor_get(v_x_730_, 1);
lean_inc(v_param_733_);
lean_dec_ref(v_x_730_);
v_method_734_ = lean_ctor_get(v_x_731_, 0);
lean_inc_ref(v_method_734_);
v_param_735_ = lean_ctor_get(v_x_731_, 1);
lean_inc(v_param_735_);
lean_dec_ref(v_x_731_);
v___x_736_ = lean_string_dec_eq(v_method_732_, v_method_734_);
lean_dec_ref(v_method_734_);
lean_dec_ref(v_method_732_);
if (v___x_736_ == 0)
{
lean_dec(v_param_735_);
lean_dec(v_param_733_);
lean_dec_ref(v_inst_729_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = lean_apply_2(v_inst_729_, v_param_733_, v_param_735_);
v___x_738_ = lean_unbox(v___x_737_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___redArg___boxed(lean_object* v_inst_739_, lean_object* v_x_740_, lean_object* v_x_741_){
_start:
{
uint8_t v_res_742_; lean_object* v_r_743_; 
v_res_742_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_739_, v_x_740_, v_x_741_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq(lean_object* v_00_u03b1_744_, lean_object* v_inst_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_745_, v_x_746_, v_x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___boxed(lean_object* v_00_u03b1_749_, lean_object* v_inst_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
uint8_t v_res_753_; lean_object* v_r_754_; 
v_res_753_ = l_Lean_JsonRpc_instBEqNotification_beq(v_00_u03b1_749_, v_inst_750_, v_x_751_, v_x_752_);
v_r_754_ = lean_box(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___redArg(lean_object* v_inst_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(v___x_756_, 0, lean_box(0));
lean_closure_set(v___x_756_, 1, v_inst_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object* v_00_u03b1_757_, lean_object* v_inst_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(v___x_759_, 0, lean_box(0));
lean_closure_set(v___x_759_, 1, v_inst_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(lean_object* v_inst_760_, lean_object* v_r_761_){
_start:
{
lean_object* v_method_762_; lean_object* v_param_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_783_; 
v_method_762_ = lean_ctor_get(v_r_761_, 0);
v_param_763_ = lean_ctor_get(v_r_761_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_r_761_);
if (v_isSharedCheck_783_ == 0)
{
v___x_765_ = v_r_761_;
v_isShared_766_ = v_isSharedCheck_783_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_param_763_);
lean_inc(v_method_762_);
lean_dec(v_r_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_783_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_760_, v_param_763_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v___x_768_; lean_object* v___x_770_; 
lean_dec_ref_known(v___x_767_, 1);
v___x_768_ = lean_box(0);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 1);
lean_ctor_set(v___x_765_, 1, v___x_768_);
v___x_770_ = v___x_765_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_method_762_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_782_; 
v_a_772_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_782_ == 0)
{
v___x_774_ = v___x_767_;
v_isShared_775_ = v_isSharedCheck_782_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_767_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_782_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_781_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_779_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 1);
lean_ctor_set(v___x_765_, 1, v___x_777_);
v___x_779_ = v___x_765_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_method_762_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(lean_object* v_inst_784_){
_start:
{
lean_object* v___f_785_; 
v___f_785_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_785_, 0, v_inst_784_);
return v___f_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object* v_00_u03b1_786_, lean_object* v_inst_787_){
_start:
{
lean_object* v___f_788_; 
v___f_788_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_788_, 0, v_inst_787_);
return v___f_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ofMessage_x3f(lean_object* v_x_789_){
_start:
{
if (lean_obj_tag(v_x_789_) == 1)
{
lean_object* v_method_790_; lean_object* v_params_x3f_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_800_; 
v_method_790_ = lean_ctor_get(v_x_789_, 0);
v_params_x3f_791_ = lean_ctor_get(v_x_789_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_x_789_);
if (v_isSharedCheck_800_ == 0)
{
v___x_793_ = v_x_789_;
v_isShared_794_ = v_isSharedCheck_800_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_params_x3f_791_);
lean_inc(v_method_790_);
lean_dec(v_x_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_800_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_791_);
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 0);
lean_ctor_set(v___x_793_, 1, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_method_790_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_795_);
v___x_797_ = v_reuseFailAlloc_799_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; 
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
}
else
{
lean_object* v___x_801_; 
lean_dec_ref(v_x_789_);
v___x_801_ = lean_box(0);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default___redArg(lean_object* v_inst_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default));
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v_inst_802_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default(lean_object* v_00_u03b1_805_, lean_object* v_inst_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___redArg(lean_object* v_inst_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object* v_a_810_, lean_object* v_inst_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_811_);
return v___x_812_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq___redArg(lean_object* v_inst_813_, lean_object* v_x_814_, lean_object* v_x_815_){
_start:
{
lean_object* v_id_816_; lean_object* v_result_817_; lean_object* v_id_818_; lean_object* v_result_819_; uint8_t v___x_820_; 
v_id_816_ = lean_ctor_get(v_x_814_, 0);
lean_inc(v_id_816_);
v_result_817_ = lean_ctor_get(v_x_814_, 1);
lean_inc(v_result_817_);
lean_dec_ref(v_x_814_);
v_id_818_ = lean_ctor_get(v_x_815_, 0);
lean_inc(v_id_818_);
v_result_819_ = lean_ctor_get(v_x_815_, 1);
lean_inc(v_result_819_);
lean_dec_ref(v_x_815_);
v___x_820_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_816_, v_id_818_);
lean_dec(v_id_818_);
lean_dec(v_id_816_);
if (v___x_820_ == 0)
{
lean_dec(v_result_819_);
lean_dec(v_result_817_);
lean_dec_ref(v_inst_813_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_apply_2(v_inst_813_, v_result_817_, v_result_819_);
v___x_822_ = lean_unbox(v___x_821_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___redArg___boxed(lean_object* v_inst_823_, lean_object* v_x_824_, lean_object* v_x_825_){
_start:
{
uint8_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_823_, v_x_824_, v_x_825_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq(lean_object* v_00_u03b1_828_, lean_object* v_inst_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_829_, v_x_830_, v_x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___boxed(lean_object* v_00_u03b1_833_, lean_object* v_inst_834_, lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
uint8_t v_res_837_; lean_object* v_r_838_; 
v_res_837_ = l_Lean_JsonRpc_instBEqResponse_beq(v_00_u03b1_833_, v_inst_834_, v_x_835_, v_x_836_);
v_r_838_ = lean_box(v_res_837_);
return v_r_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object* v_inst_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_840_, 0, lean_box(0));
lean_closure_set(v___x_840_, 1, v_inst_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object* v_00_u03b1_841_, lean_object* v_inst_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_843_, 0, lean_box(0));
lean_closure_set(v___x_843_, 1, v_inst_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(lean_object* v_inst_844_, lean_object* v_r_845_){
_start:
{
lean_object* v_id_846_; lean_object* v_result_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_855_; 
v_id_846_ = lean_ctor_get(v_r_845_, 0);
v_result_847_ = lean_ctor_get(v_r_845_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_r_845_);
if (v_isSharedCheck_855_ == 0)
{
v___x_849_ = v_r_845_;
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_result_847_);
lean_inc(v_id_846_);
lean_dec(v_r_845_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_apply_1(v_inst_844_, v_result_847_);
if (v_isShared_850_ == 0)
{
lean_ctor_set_tag(v___x_849_, 2);
lean_ctor_set(v___x_849_, 1, v___x_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_id_846_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object* v_inst_856_){
_start:
{
lean_object* v___f_857_; 
v___f_857_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_857_, 0, v_inst_856_);
return v___f_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object* v_00_u03b1_858_, lean_object* v_inst_859_){
_start:
{
lean_object* v___f_860_; 
v___f_860_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_860_, 0, v_inst_859_);
return v___f_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ofMessage_x3f(lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_861_) == 2)
{
lean_object* v_id_862_; lean_object* v_result_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
v_id_862_ = lean_ctor_get(v_x_861_, 0);
v_result_863_ = lean_ctor_get(v_x_861_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_x_861_);
if (v_isSharedCheck_871_ == 0)
{
v___x_865_ = v_x_861_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_result_863_);
lean_inc(v_id_862_);
lean_dec(v_x_861_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set_tag(v___x_865_, 0);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_id_862_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_result_863_);
v___x_868_ = v_reuseFailAlloc_870_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; 
v___x_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
}
else
{
lean_object* v___x_872_; 
lean_dec_ref(v_x_861_);
v___x_872_ = lean_box(0);
return v___x_872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object* v_00_u03b1_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0));
return v___x_879_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__0(void){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_JsonRpc_instInhabitedResponseError_default(lean_box(0));
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object* v_a_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__0);
return v___x_882_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq___redArg(lean_object* v_inst_883_, lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
lean_object* v_id_886_; uint8_t v_code_887_; lean_object* v_message_888_; lean_object* v_data_x3f_889_; lean_object* v_id_890_; uint8_t v_code_891_; lean_object* v_message_892_; lean_object* v_data_x3f_893_; uint8_t v___x_894_; 
v_id_886_ = lean_ctor_get(v_x_884_, 0);
lean_inc(v_id_886_);
v_code_887_ = lean_ctor_get_uint8(v_x_884_, sizeof(void*)*3);
v_message_888_ = lean_ctor_get(v_x_884_, 1);
lean_inc_ref(v_message_888_);
v_data_x3f_889_ = lean_ctor_get(v_x_884_, 2);
lean_inc(v_data_x3f_889_);
lean_dec_ref(v_x_884_);
v_id_890_ = lean_ctor_get(v_x_885_, 0);
lean_inc(v_id_890_);
v_code_891_ = lean_ctor_get_uint8(v_x_885_, sizeof(void*)*3);
v_message_892_ = lean_ctor_get(v_x_885_, 1);
lean_inc_ref(v_message_892_);
v_data_x3f_893_ = lean_ctor_get(v_x_885_, 2);
lean_inc(v_data_x3f_893_);
lean_dec_ref(v_x_885_);
v___x_894_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_886_, v_id_890_);
lean_dec(v_id_890_);
lean_dec(v_id_886_);
if (v___x_894_ == 0)
{
lean_dec(v_data_x3f_893_);
lean_dec_ref(v_message_892_);
lean_dec(v_data_x3f_889_);
lean_dec_ref(v_message_888_);
lean_dec_ref(v_inst_883_);
return v___x_894_;
}
else
{
uint8_t v___x_895_; 
v___x_895_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_code_887_, v_code_891_);
if (v___x_895_ == 0)
{
lean_dec(v_data_x3f_893_);
lean_dec_ref(v_message_892_);
lean_dec(v_data_x3f_889_);
lean_dec_ref(v_message_888_);
lean_dec_ref(v_inst_883_);
return v___x_895_;
}
else
{
uint8_t v___x_896_; 
v___x_896_ = lean_string_dec_eq(v_message_888_, v_message_892_);
lean_dec_ref(v_message_892_);
lean_dec_ref(v_message_888_);
if (v___x_896_ == 0)
{
lean_dec(v_data_x3f_893_);
lean_dec(v_data_x3f_889_);
lean_dec_ref(v_inst_883_);
return v___x_896_;
}
else
{
uint8_t v___x_897_; 
v___x_897_ = l_Option_instBEq_beq___redArg(v_inst_883_, v_data_x3f_889_, v_data_x3f_893_);
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(lean_object* v_inst_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_898_, v_x_899_, v_x_900_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object* v_00_u03b1_903_, lean_object* v_inst_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
uint8_t v___x_907_; 
v___x_907_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_904_, v_x_905_, v_x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___boxed(lean_object* v_00_u03b1_908_, lean_object* v_inst_909_, lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
uint8_t v_res_912_; lean_object* v_r_913_; 
v_res_912_ = l_Lean_JsonRpc_instBEqResponseError_beq(v_00_u03b1_908_, v_inst_909_, v_x_910_, v_x_911_);
v_r_913_ = lean_box(v_res_912_);
return v_r_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object* v_inst_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_915_, 0, lean_box(0));
lean_closure_set(v___x_915_, 1, v_inst_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object* v_00_u03b1_916_, lean_object* v_inst_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_918_, 0, lean_box(0));
lean_closure_set(v___x_918_, 1, v_inst_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object* v_inst_919_, lean_object* v_r_920_){
_start:
{
lean_object* v_data_x3f_921_; 
v_data_x3f_921_ = lean_ctor_get(v_r_920_, 2);
lean_inc(v_data_x3f_921_);
if (lean_obj_tag(v_data_x3f_921_) == 0)
{
lean_object* v_id_922_; uint8_t v_code_923_; lean_object* v_message_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_inst_919_);
v_id_922_ = lean_ctor_get(v_r_920_, 0);
v_code_923_ = lean_ctor_get_uint8(v_r_920_, sizeof(void*)*3);
v_message_924_ = lean_ctor_get(v_r_920_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v_r_920_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v_r_920_, 2);
lean_dec(v_unused_933_);
v___x_926_ = v_r_920_;
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_message_924_);
lean_inc(v_id_922_);
lean_dec(v_r_920_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = lean_box(0);
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 3);
lean_ctor_set(v___x_926_, 2, v___x_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_id_922_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_message_924_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v___x_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_931_, sizeof(void*)*3, v_code_923_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
lean_object* v_id_934_; uint8_t v_code_935_; lean_object* v_message_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_952_; 
v_id_934_ = lean_ctor_get(v_r_920_, 0);
v_code_935_ = lean_ctor_get_uint8(v_r_920_, sizeof(void*)*3);
v_message_936_ = lean_ctor_get(v_r_920_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v_r_920_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v_r_920_, 2);
lean_dec(v_unused_953_);
v___x_938_ = v_r_920_;
v_isShared_939_ = v_isSharedCheck_952_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_message_936_);
lean_inc(v_id_934_);
lean_dec(v_r_920_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_952_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_val_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_951_; 
v_val_940_ = lean_ctor_get(v_data_x3f_921_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v_data_x3f_921_);
if (v_isSharedCheck_951_ == 0)
{
v___x_942_ = v_data_x3f_921_;
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_val_940_);
lean_dec(v_data_x3f_921_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_951_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = lean_apply_1(v_inst_919_, v_val_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_944_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 3);
lean_ctor_set(v___x_938_, 2, v___x_946_);
v___x_948_ = v___x_938_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_id_934_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_message_936_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v___x_946_);
lean_ctor_set_uint8(v_reuseFailAlloc_949_, sizeof(void*)*3, v_code_935_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object* v_inst_954_){
_start:
{
lean_object* v___f_955_; 
v___f_955_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_955_, 0, v_inst_954_);
return v___f_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object* v_00_u03b1_956_, lean_object* v_inst_957_){
_start:
{
lean_object* v___f_958_; 
v___f_958_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_958_, 0, v_inst_957_);
return v___f_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object* v_r_959_){
_start:
{
lean_object* v_id_960_; uint8_t v_code_961_; lean_object* v_message_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_970_; 
v_id_960_ = lean_ctor_get(v_r_959_, 0);
v_code_961_ = lean_ctor_get_uint8(v_r_959_, sizeof(void*)*3);
v_message_962_ = lean_ctor_get(v_r_959_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_r_959_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v_r_959_, 2);
lean_dec(v_unused_971_);
v___x_964_ = v_r_959_;
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_message_962_);
lean_inc(v_id_960_);
lean_dec(v_r_959_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_box(0);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 3);
lean_ctor_set(v___x_964_, 2, v___x_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_id_960_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_message_962_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v___x_966_);
lean_ctor_set_uint8(v_reuseFailAlloc_969_, sizeof(void*)*3, v_code_961_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ofMessage_x3f(lean_object* v_x_974_){
_start:
{
if (lean_obj_tag(v_x_974_) == 3)
{
lean_object* v_id_975_; uint8_t v_code_976_; lean_object* v_message_977_; lean_object* v_data_x3f_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
v_id_975_ = lean_ctor_get(v_x_974_, 0);
v_code_976_ = lean_ctor_get_uint8(v_x_974_, sizeof(void*)*3);
v_message_977_ = lean_ctor_get(v_x_974_, 1);
v_data_x3f_978_ = lean_ctor_get(v_x_974_, 2);
v_isSharedCheck_986_ = !lean_is_exclusive(v_x_974_);
if (v_isSharedCheck_986_ == 0)
{
v___x_980_ = v_x_974_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_data_x3f_978_);
lean_inc(v_message_977_);
lean_inc(v_id_975_);
lean_dec(v_x_974_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set_tag(v___x_980_, 0);
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_id_975_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_message_977_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_data_x3f_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*3, v_code_976_);
v___x_983_ = v_reuseFailAlloc_985_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
}
else
{
lean_object* v___x_987_; 
lean_dec_ref(v_x_974_);
v___x_987_ = lean_box(0);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object* v_s_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v_s_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object* v_n_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_993_, 0, v_n_992_);
return v___x_993_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_RequestID_lt(lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
switch(lean_obj_tag(v_x_996_))
{
case 0:
{
if (lean_obj_tag(v_x_997_) == 0)
{
lean_object* v_s_998_; lean_object* v_s_999_; uint8_t v___x_1000_; 
v_s_998_ = lean_ctor_get(v_x_996_, 0);
lean_inc_ref(v_s_998_);
lean_dec_ref_known(v_x_996_, 1);
v_s_999_ = lean_ctor_get(v_x_997_, 0);
lean_inc_ref(v_s_999_);
lean_dec_ref_known(v_x_997_, 1);
v___x_1000_ = lean_string_dec_lt(v_s_998_, v_s_999_);
lean_dec_ref(v_s_999_);
lean_dec_ref(v_s_998_);
return v___x_1000_;
}
else
{
uint8_t v___x_1001_; 
lean_dec_ref_known(v_x_996_, 1);
lean_dec(v_x_997_);
v___x_1001_ = 0;
return v___x_1001_;
}
}
case 1:
{
switch(lean_obj_tag(v_x_997_))
{
case 1:
{
lean_object* v_n_1002_; lean_object* v_n_1003_; uint8_t v___x_1004_; 
v_n_1002_ = lean_ctor_get(v_x_996_, 0);
lean_inc_ref(v_n_1002_);
lean_dec_ref_known(v_x_996_, 1);
v_n_1003_ = lean_ctor_get(v_x_997_, 0);
lean_inc_ref(v_n_1003_);
lean_dec_ref_known(v_x_997_, 1);
v___x_1004_ = l_Lean_JsonNumber_lt(v_n_1002_, v_n_1003_);
return v___x_1004_;
}
case 0:
{
uint8_t v___x_1005_; 
lean_dec_ref_known(v_x_997_, 1);
lean_dec_ref_known(v_x_996_, 1);
v___x_1005_ = 1;
return v___x_1005_;
}
default: 
{
uint8_t v___x_1006_; 
lean_dec_ref_known(v_x_996_, 1);
lean_dec(v_x_997_);
v___x_1006_ = 0;
return v___x_1006_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_997_))
{
case 1:
{
uint8_t v___x_1007_; 
lean_dec_ref_known(v_x_997_, 1);
v___x_1007_ = 1;
return v___x_1007_;
}
case 0:
{
uint8_t v___x_1008_; 
lean_dec_ref_known(v_x_997_, 1);
v___x_1008_ = 1;
return v___x_1008_;
}
default: 
{
uint8_t v___x_1009_; 
lean_dec(v_x_997_);
v___x_1009_ = 0;
return v___x_1009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_lt___boxed(lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
uint8_t v_res_1012_; lean_object* v_r_1013_; 
v_res_1012_ = l_Lean_JsonRpc_RequestID_lt(v_x_1010_, v_x_1011_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
static lean_object* _init_l_Lean_JsonRpc_RequestID_ltProp(void){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_box(0);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instLTRequestID(void){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_box(0);
return v___x_1015_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object* v_a_1016_, lean_object* v_b_1017_){
_start:
{
uint8_t v___x_1018_; 
v___x_1018_ = l_Lean_JsonRpc_RequestID_lt(v_a_1016_, v_b_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object* v_a_1019_, lean_object* v_b_1020_){
_start:
{
uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_res_1021_ = l_Lean_JsonRpc_instDecidableLtRequestID(v_a_1019_, v_b_1020_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object* v_j_1026_){
_start:
{
switch(lean_obj_tag(v_j_1026_))
{
case 3:
{
lean_object* v_s_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1035_; 
v_s_1027_ = lean_ctor_get(v_j_1026_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_j_1026_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1029_ = v_j_1026_;
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_s_1027_);
lean_dec(v_j_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set_tag(v___x_1029_, 0);
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_s_1027_);
v___x_1032_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
}
case 2:
{
lean_object* v_n_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1044_; 
v_n_1036_ = lean_ctor_get(v_j_1026_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_j_1026_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1038_ = v_j_1026_;
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_n_1036_);
lean_dec(v_j_1026_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 1);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_n_1036_);
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
default: 
{
lean_object* v___x_1045_; 
lean_dec(v_j_1026_);
v___x_1045_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object* v_rid_1048_){
_start:
{
switch(lean_obj_tag(v_rid_1048_))
{
case 0:
{
lean_object* v_s_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
v_s_1049_ = lean_ctor_get(v_rid_1048_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_rid_1048_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v_rid_1048_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_s_1049_);
lean_dec(v_rid_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 3);
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_s_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
case 1:
{
lean_object* v_n_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_n_1057_ = lean_ctor_get(v_rid_1048_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_rid_1048_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v_rid_1048_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_n_1057_);
lean_dec(v_rid_1048_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 2);
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_n_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
default: 
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_box(0);
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v_m_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v___y_1088_; 
v___x_1086_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_1085_))
{
case 0:
{
lean_object* v_id_1091_; lean_object* v_method_1092_; lean_object* v_params_x3f_1093_; lean_object* v___x_1094_; lean_object* v___y_1096_; 
lean_dec_ref(v___x_1084_);
v_id_1091_ = lean_ctor_get(v_m_1085_, 0);
lean_inc(v_id_1091_);
v_method_1092_ = lean_ctor_get(v_m_1085_, 1);
lean_inc_ref(v_method_1092_);
v_params_x3f_1093_ = lean_ctor_get(v_m_1085_, 2);
lean_inc(v_params_x3f_1093_);
lean_dec_ref_known(v_m_1085_, 3);
v___x_1094_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1091_))
{
case 0:
{
lean_object* v_s_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_s_1107_ = lean_ctor_get(v_id_1091_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_id_1091_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v_id_1091_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_s_1107_);
lean_dec(v_id_1091_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set_tag(v___x_1109_, 3);
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_s_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
v___y_1096_ = v___x_1112_;
goto v___jp_1095_;
}
}
}
case 1:
{
lean_object* v_n_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_n_1115_ = lean_ctor_get(v_id_1091_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_id_1091_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v_id_1091_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_n_1115_);
lean_dec(v_id_1091_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 2);
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_n_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
v___y_1096_ = v___x_1120_;
goto v___jp_1095_;
}
}
}
default: 
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_box(0);
v___y_1096_ = v___x_1123_;
goto v___jp_1095_;
}
}
v___jp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1094_);
lean_ctor_set(v___x_1097_, 1, v___y_1096_);
v___x_1098_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1099_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_method_1092_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1097_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1105_ = l_Lean_Json_opt___redArg(v___x_1083_, v___x_1104_, v_params_x3f_1093_);
v___x_1106_ = l_List_appendTR___redArg(v___x_1103_, v___x_1105_);
v___y_1088_ = v___x_1106_;
goto v___jp_1087_;
}
}
case 1:
{
lean_object* v_method_1124_; lean_object* v_params_x3f_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v___x_1084_);
v_method_1124_ = lean_ctor_get(v_m_1085_, 0);
v_params_x3f_1125_ = lean_ctor_get(v_m_1085_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_m_1085_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1127_ = v_m_1085_;
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_params_x3f_1125_);
lean_inc(v_method_1124_);
lean_dec(v_m_1085_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1129_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1130_, 0, v_method_1124_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set_tag(v___x_1127_, 0);
lean_ctor_set(v___x_1127_, 1, v___x_1130_);
lean_ctor_set(v___x_1127_, 0, v___x_1129_);
v___x_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1134_ = l_Lean_Json_opt___redArg(v___x_1083_, v___x_1133_, v_params_x3f_1125_);
v___x_1135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1132_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___y_1088_ = v___x_1135_;
goto v___jp_1087_;
}
}
}
case 2:
{
lean_object* v_id_1138_; lean_object* v_result_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v___x_1084_);
lean_dec_ref(v___x_1083_);
v_id_1138_ = lean_ctor_get(v_m_1085_, 0);
v_result_1139_ = lean_ctor_get(v_m_1085_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_m_1085_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1141_ = v_m_1085_;
v_isShared_1142_ = v_isSharedCheck_1171_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_result_1139_);
lean_inc(v_id_1138_);
lean_dec(v_m_1085_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1171_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___y_1145_; 
v___x_1143_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1138_))
{
case 0:
{
lean_object* v_s_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
v_s_1154_ = lean_ctor_get(v_id_1138_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_id_1138_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v_id_1138_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_s_1154_);
lean_dec(v_id_1138_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 3);
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_s_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
v___y_1145_ = v___x_1159_;
goto v___jp_1144_;
}
}
}
case 1:
{
lean_object* v_n_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
v_n_1162_ = lean_ctor_get(v_id_1138_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_id_1138_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v_id_1138_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_n_1162_);
lean_dec(v_id_1138_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 2);
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_n_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
v___y_1145_ = v___x_1167_;
goto v___jp_1144_;
}
}
}
default: 
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_box(0);
v___y_1145_ = v___x_1170_;
goto v___jp_1144_;
}
}
v___jp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 0);
lean_ctor_set(v___x_1141_, 1, v___y_1145_);
lean_ctor_set(v___x_1141_, 0, v___x_1143_);
v___x_1147_ = v___x_1141_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___y_1145_);
v___x_1147_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1148_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
lean_ctor_set(v___x_1149_, 1, v_result_1139_);
v___x_1150_ = lean_box(0);
v___x_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1147_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___y_1088_ = v___x_1152_;
goto v___jp_1087_;
}
}
}
}
default: 
{
lean_object* v_id_1172_; uint8_t v_code_1173_; lean_object* v_message_1174_; lean_object* v_data_x3f_1175_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___x_1195_; lean_object* v___y_1197_; 
lean_dec_ref(v___x_1083_);
v_id_1172_ = lean_ctor_get(v_m_1085_, 0);
lean_inc(v_id_1172_);
v_code_1173_ = lean_ctor_get_uint8(v_m_1085_, sizeof(void*)*3);
v_message_1174_ = lean_ctor_get(v_m_1085_, 1);
lean_inc_ref(v_message_1174_);
v_data_x3f_1175_ = lean_ctor_get(v_m_1085_, 2);
lean_inc(v_data_x3f_1175_);
lean_dec_ref_known(v_m_1085_, 3);
v___x_1195_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1172_))
{
case 0:
{
lean_object* v_s_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
v_s_1213_ = lean_ctor_get(v_id_1172_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_id_1172_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v_id_1172_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_s_1213_);
lean_dec(v_id_1172_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set_tag(v___x_1215_, 3);
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_s_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
v___y_1197_ = v___x_1218_;
goto v___jp_1196_;
}
}
}
case 1:
{
lean_object* v_n_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v_n_1221_ = lean_ctor_get(v_id_1172_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_id_1172_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v_id_1172_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_n_1221_);
lean_dec(v_id_1172_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 2);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_n_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
v___y_1197_ = v___x_1226_;
goto v___jp_1196_;
}
}
}
default: 
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_box(0);
v___y_1197_ = v___x_1229_;
goto v___jp_1196_;
}
}
v___jp_1176_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1178_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___y_1178_);
lean_ctor_set(v___x_1181_, 1, v___y_1180_);
v___x_1182_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1183_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_message_1174_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1181_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1189_ = l_Lean_Json_opt___redArg(v___x_1084_, v___x_1188_, v_data_x3f_1175_);
v___x_1190_ = l_List_appendTR___redArg(v___x_1187_, v___x_1189_);
v___x_1191_ = l_Lean_Json_mkObj(v___x_1190_);
lean_dec(v___x_1190_);
lean_inc_ref(v___y_1179_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___y_1179_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1185_);
v___x_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___y_1177_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___y_1088_ = v___x_1194_;
goto v___jp_1087_;
}
v___jp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1195_);
lean_ctor_set(v___x_1198_, 1, v___y_1197_);
v___x_1199_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1200_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_1173_)
{
case 0:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1201_;
goto v___jp_1176_;
}
case 1:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1202_;
goto v___jp_1176_;
}
case 2:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1203_;
goto v___jp_1176_;
}
case 3:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1204_;
goto v___jp_1176_;
}
case 4:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1205_;
goto v___jp_1176_;
}
case 5:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1206_;
goto v___jp_1176_;
}
case 6:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1207_;
goto v___jp_1176_;
}
case 7:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1208_;
goto v___jp_1176_;
}
case 8:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1209_;
goto v___jp_1176_;
}
case 9:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1210_;
goto v___jp_1176_;
}
case 10:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1211_;
goto v___jp_1176_;
}
default: 
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_1177_ = v___x_1198_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1199_;
v___y_1180_ = v___x_1212_;
goto v___jp_1176_;
}
}
}
}
}
v___jp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1086_);
lean_ctor_set(v___x_1089_, 1, v___y_1088_);
v___x_1090_ = l_Lean_Json_mkObj(v___x_1089_);
lean_dec_ref_known(v___x_1089_, 2);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object* v___f_1239_, lean_object* v___f_1240_, lean_object* v___x_1241_, lean_object* v___x_1242_, lean_object* v_j_1243_){
_start:
{
lean_object* v___y_1247_; lean_object* v___y_1248_; uint8_t v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1243_);
v___x_1259_ = l_Lean_Json_getObjVal_x3f(v_j_1243_, v___x_1258_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_j_1243_);
lean_dec_ref(v___x_1242_);
lean_dec_ref(v___x_1241_);
lean_dec_ref(v___f_1240_);
lean_dec_ref(v___f_1239_);
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
else
{
lean_object* v_a_1268_; 
v_a_1268_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1259_, 1);
if (lean_obj_tag(v_a_1268_) == 3)
{
lean_object* v_s_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_s_1269_ = lean_ctor_get(v_a_1268_, 0);
lean_inc_ref(v_s_1269_);
lean_dec_ref_known(v_a_1268_, 1);
v___x_1270_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1271_ = lean_string_dec_eq(v_s_1269_, v___x_1270_);
lean_dec_ref(v_s_1269_);
if (v___x_1271_ == 0)
{
lean_dec(v_j_1243_);
lean_dec_ref(v___x_1242_);
lean_dec_ref(v___x_1241_);
lean_dec_ref(v___f_1240_);
lean_dec_ref(v___f_1239_);
goto v___jp_1244_;
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1243_);
v___x_1273_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1243_, v___f_1239_, v___x_1272_);
if (lean_obj_tag(v___x_1273_) == 0)
{
goto v___jp_1330_;
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v_a_1357_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1357_);
v___x_1358_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1241_);
lean_inc(v_j_1243_);
v___x_1359_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1243_, v___x_1241_, v___x_1358_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_dec_ref_known(v___x_1359_, 1);
lean_dec(v_a_1357_);
goto v___jp_1330_;
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1381_; 
lean_dec_ref_known(v___x_1273_, 1);
lean_dec_ref(v___x_1241_);
lean_dec_ref(v___f_1240_);
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1381_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1381_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___y_1365_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1371_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1243_, v___x_1242_, v___x_1370_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref_known(v___x_1371_, 1);
v___x_1372_ = lean_box(0);
v___y_1365_ = v___x_1372_;
goto v___jp_1364_;
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1371_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1371_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
v___y_1365_ = v___x_1378_;
goto v___jp_1364_;
}
}
}
v___jp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1357_);
lean_ctor_set(v___x_1366_, 1, v_a_1360_);
lean_ctor_set(v___x_1366_, 2, v___y_1365_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1366_);
v___x_1368_ = v___x_1362_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
v___jp_1274_:
{
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_j_1243_);
lean_dec_ref(v___x_1241_);
lean_dec_ref(v___f_1240_);
v_a_1275_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1273_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1273_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_a_1283_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1273_, 1);
v___x_1284_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1285_ = l_Lean_Json_getObjVal_x3f(v_j_1243_, v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_a_1283_);
lean_dec_ref(v___x_1241_);
lean_dec_ref(v___f_1240_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_a_1294_ = lean_ctor_get(v___x_1285_, 0);
lean_inc_n(v_a_1294_, 2);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1295_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1296_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1294_, v___f_1240_, v___x_1295_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_a_1294_);
lean_dec(v_a_1283_);
lean_dec_ref(v___x_1241_);
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_a_1305_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1306_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1294_);
v___x_1307_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1294_, v___x_1241_, v___x_1306_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_a_1305_);
lean_dec(v_a_1294_);
lean_dec(v_a_1283_);
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_a_1316_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1317_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1318_ = l_Lean_Json_getObjVal_x3f(v_a_1294_, v___x_1317_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
lean_dec_ref_known(v___x_1318_, 1);
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_unbox(v_a_1305_);
lean_dec(v_a_1305_);
v___y_1247_ = v_a_1283_;
v___y_1248_ = v_a_1316_;
v___y_1249_ = v___x_1320_;
v___y_1250_ = v___x_1319_;
goto v___jp_1246_;
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1329_; 
v_a_1321_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1323_ = v___x_1318_;
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1318_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_unbox(v_a_1305_);
lean_dec(v_a_1305_);
v___y_1247_ = v_a_1283_;
v___y_1248_ = v_a_1316_;
v___y_1249_ = v___x_1327_;
v___y_1250_ = v___x_1326_;
goto v___jp_1246_;
}
}
}
}
}
}
}
}
v___jp_1330_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1241_);
lean_inc(v_j_1243_);
v___x_1332_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1243_, v___x_1241_, v___x_1331_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_dec_ref_known(v___x_1332_, 1);
lean_dec_ref(v___x_1242_);
if (lean_obj_tag(v___x_1273_) == 0)
{
goto v___jp_1274_;
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_a_1333_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_a_1333_);
v___x_1334_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1243_);
v___x_1335_ = l_Lean_Json_getObjVal_x3f(v_j_1243_, v___x_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_dec_ref_known(v___x_1335_, 1);
lean_dec(v_a_1333_);
goto v___jp_1274_;
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1344_; 
lean_dec_ref_known(v___x_1273_, 1);
lean_dec(v_j_1243_);
lean_dec_ref(v___x_1241_);
lean_dec_ref(v___f_1240_);
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1344_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1344_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1340_, 0, v_a_1333_);
lean_ctor_set(v___x_1340_, 1, v_a_1336_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1340_);
v___x_1342_ = v___x_1338_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec_ref(v___x_1273_);
lean_dec_ref(v___x_1241_);
lean_dec_ref(v___f_1240_);
v_a_1345_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1346_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1347_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1243_, v___x_1242_, v___x_1346_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v___x_1348_; 
lean_dec_ref_known(v___x_1347_, 1);
v___x_1348_ = lean_box(0);
v___y_1254_ = v_a_1345_;
v___y_1255_ = v___x_1348_;
goto v___jp_1253_;
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1347_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1347_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
v___y_1254_ = v_a_1345_;
v___y_1255_ = v___x_1354_;
goto v___jp_1253_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1268_);
lean_dec(v_j_1243_);
lean_dec_ref(v___x_1242_);
lean_dec_ref(v___x_1241_);
lean_dec_ref(v___f_1240_);
lean_dec_ref(v___f_1239_);
goto v___jp_1244_;
}
}
v___jp_1244_:
{
lean_object* v___x_1245_; 
v___x_1245_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1));
return v___x_1245_;
}
v___jp_1246_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1251_, 0, v___y_1247_);
lean_ctor_set(v___x_1251_, 1, v___y_1248_);
lean_ctor_set(v___x_1251_, 2, v___y_1250_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*3, v___y_1249_);
v___x_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
v___jp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___y_1254_);
lean_ctor_set(v___x_1256_, 1, v___y_1255_);
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object* v___x_1395_, lean_object* v_inst_1396_, lean_object* v_j_1397_){
_start:
{
lean_object* v_method_1401_; lean_object* v_params_x3f_1402_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1397_);
v___x_1425_ = l_Lean_Json_getObjVal_x3f(v_j_1397_, v___x_1424_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_dec(v_j_1397_);
lean_dec_ref(v_inst_1396_);
lean_dec_ref(v___x_1395_);
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
else
{
lean_object* v_a_1434_; 
v_a_1434_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1425_, 1);
if (lean_obj_tag(v_a_1434_) == 3)
{
lean_object* v_s_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_s_1435_ = lean_ctor_get(v_a_1434_, 0);
lean_inc_ref(v_s_1435_);
lean_dec_ref_known(v_a_1434_, 1);
v___x_1436_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1437_ = lean_string_dec_eq(v_s_1435_, v___x_1436_);
lean_dec_ref(v_s_1435_);
if (v___x_1437_ == 0)
{
lean_dec(v_j_1397_);
lean_dec_ref(v_inst_1396_);
lean_dec_ref(v___x_1395_);
goto v___jp_1422_;
}
else
{
lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___f_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___f_1438_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___closed__0));
v___x_1439_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__0));
v___x_1440_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__1));
v___f_1441_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___closed__0));
v___x_1442_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1397_);
v___x_1443_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1397_, v___f_1438_, v___x_1442_);
if (lean_obj_tag(v___x_1443_) == 0)
{
goto v___jp_1484_;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1397_);
v___x_1502_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1397_, v___x_1439_, v___x_1501_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_dec_ref_known(v___x_1502_, 1);
goto v___jp_1484_;
}
else
{
lean_dec_ref_known(v___x_1502_, 1);
lean_dec_ref_known(v___x_1443_, 1);
lean_dec(v_j_1397_);
lean_dec_ref(v_inst_1396_);
lean_dec_ref(v___x_1395_);
goto v___jp_1398_;
}
}
v___jp_1444_:
{
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_j_1397_);
v_a_1445_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1443_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1443_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_dec_ref_known(v___x_1443_, 1);
v___x_1453_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1454_ = l_Lean_Json_getObjVal_x3f(v_j_1397_, v___x_1453_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_a_1463_ = lean_ctor_get(v___x_1454_, 0);
lean_inc_n(v_a_1463_, 2);
lean_dec_ref_known(v___x_1454_, 1);
v___x_1464_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1465_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1463_, v___f_1441_, v___x_1464_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_a_1463_);
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec_ref_known(v___x_1465_, 1);
v___x_1474_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1475_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1463_, v___x_1439_, v___x_1474_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
else
{
lean_dec_ref_known(v___x_1475_, 1);
goto v___jp_1398_;
}
}
}
}
}
v___jp_1484_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1397_);
v___x_1486_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1397_, v___x_1439_, v___x_1485_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_dec_ref_known(v___x_1486_, 1);
lean_dec_ref(v_inst_1396_);
lean_dec_ref(v___x_1395_);
if (lean_obj_tag(v___x_1443_) == 0)
{
goto v___jp_1444_;
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1397_);
v___x_1488_ = l_Lean_Json_getObjVal_x3f(v_j_1397_, v___x_1487_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_dec_ref_known(v___x_1488_, 1);
goto v___jp_1444_;
}
else
{
lean_dec_ref_known(v___x_1488_, 1);
lean_dec_ref_known(v___x_1443_, 1);
lean_dec(v_j_1397_);
goto v___jp_1398_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec_ref(v___x_1443_);
v_a_1489_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1490_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1491_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1397_, v___x_1440_, v___x_1490_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v___x_1492_; 
lean_dec_ref_known(v___x_1491_, 1);
v___x_1492_ = lean_box(0);
v_method_1401_ = v_a_1489_;
v_params_x3f_1402_ = v___x_1492_;
goto v___jp_1400_;
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
v_a_1493_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1491_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1491_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
v_method_1401_ = v_a_1489_;
v_params_x3f_1402_ = v___x_1498_;
goto v___jp_1400_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1434_);
lean_dec(v_j_1397_);
lean_dec_ref(v_inst_1396_);
lean_dec_ref(v___x_1395_);
goto v___jp_1422_;
}
}
v___jp_1398_:
{
lean_object* v___x_1399_; 
v___x_1399_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1));
return v___x_1399_;
}
v___jp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = l_Lean_Option_toJson___redArg(v___x_1395_, v_params_x3f_1402_);
v___x_1404_ = lean_apply_1(v_inst_1396_, v___x_1403_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v_method_1401_);
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1421_; 
v_a_1413_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1415_ = v___x_1404_;
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1404_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v_method_1401_);
lean_ctor_set(v___x_1417_, 1, v_a_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
v___jp_1422_:
{
lean_object* v___x_1423_; 
v___x_1423_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2));
return v___x_1423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object* v_inst_1503_){
_start:
{
lean_object* v___x_1504_; lean_object* v___f_1505_; 
v___x_1504_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___f_1505_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1505_, 0, v___x_1504_);
lean_closure_set(v___f_1505_, 1, v_inst_1503_);
return v___f_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object* v_00_u03b1_1506_, lean_object* v_inst_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_JsonRpc_instFromJsonNotification___redArg(v_inst_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx(lean_object* v_x_1509_){
_start:
{
switch(lean_obj_tag(v_x_1509_))
{
case 0:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_unsigned_to_nat(0u);
return v___x_1510_;
}
case 1:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_unsigned_to_nat(1u);
return v___x_1511_;
}
case 2:
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_unsigned_to_nat(2u);
return v___x_1512_;
}
default: 
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_unsigned_to_nat(3u);
return v___x_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___boxed(lean_object* v_x_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_JsonRpc_MessageMetaData_ctorIdx(v_x_1514_);
lean_dec_ref(v_x_1514_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(lean_object* v_t_1516_, lean_object* v_k_1517_){
_start:
{
switch(lean_obj_tag(v_t_1516_))
{
case 0:
{
lean_object* v_id_1518_; lean_object* v_method_1519_; lean_object* v___x_1520_; 
v_id_1518_ = lean_ctor_get(v_t_1516_, 0);
lean_inc(v_id_1518_);
v_method_1519_ = lean_ctor_get(v_t_1516_, 1);
lean_inc_ref(v_method_1519_);
lean_dec_ref_known(v_t_1516_, 2);
v___x_1520_ = lean_apply_2(v_k_1517_, v_id_1518_, v_method_1519_);
return v___x_1520_;
}
case 1:
{
lean_object* v_method_1521_; lean_object* v___x_1522_; 
v_method_1521_ = lean_ctor_get(v_t_1516_, 0);
lean_inc_ref(v_method_1521_);
lean_dec_ref_known(v_t_1516_, 1);
v___x_1522_ = lean_apply_1(v_k_1517_, v_method_1521_);
return v___x_1522_;
}
case 2:
{
lean_object* v_id_1523_; lean_object* v___x_1524_; 
v_id_1523_ = lean_ctor_get(v_t_1516_, 0);
lean_inc(v_id_1523_);
lean_dec_ref_known(v_t_1516_, 1);
v___x_1524_ = lean_apply_1(v_k_1517_, v_id_1523_);
return v___x_1524_;
}
default: 
{
lean_object* v_id_1525_; uint8_t v_code_1526_; lean_object* v_message_1527_; lean_object* v_data_x3f_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v_id_1525_ = lean_ctor_get(v_t_1516_, 0);
lean_inc(v_id_1525_);
v_code_1526_ = lean_ctor_get_uint8(v_t_1516_, sizeof(void*)*3);
v_message_1527_ = lean_ctor_get(v_t_1516_, 1);
lean_inc_ref(v_message_1527_);
v_data_x3f_1528_ = lean_ctor_get(v_t_1516_, 2);
lean_inc(v_data_x3f_1528_);
lean_dec_ref_known(v_t_1516_, 3);
v___x_1529_ = lean_box(v_code_1526_);
v___x_1530_ = lean_apply_4(v_k_1517_, v_id_1525_, v___x_1529_, v_message_1527_, v_data_x3f_1528_);
return v___x_1530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim(lean_object* v_motive_1531_, lean_object* v_ctorIdx_1532_, lean_object* v_t_1533_, lean_object* v_h_1534_, lean_object* v_k_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1533_, v_k_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(lean_object* v_motive_1537_, lean_object* v_ctorIdx_1538_, lean_object* v_t_1539_, lean_object* v_h_1540_, lean_object* v_k_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_JsonRpc_MessageMetaData_ctorElim(v_motive_1537_, v_ctorIdx_1538_, v_t_1539_, v_h_1540_, v_k_1541_);
lean_dec(v_ctorIdx_1538_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim___redArg(lean_object* v_t_1543_, lean_object* v_request_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1543_, v_request_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim(lean_object* v_motive_1546_, lean_object* v_t_1547_, lean_object* v_h_1548_, lean_object* v_request_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1547_, v_request_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(lean_object* v_t_1551_, lean_object* v_notification_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1551_, v_notification_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim(lean_object* v_motive_1554_, lean_object* v_t_1555_, lean_object* v_h_1556_, lean_object* v_notification_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1555_, v_notification_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(lean_object* v_t_1559_, lean_object* v_response_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1559_, v_response_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim(lean_object* v_motive_1562_, lean_object* v_t_1563_, lean_object* v_h_1564_, lean_object* v_response_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1563_, v_response_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim___redArg(lean_object* v_t_1567_, lean_object* v_responseError_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1567_, v_responseError_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim(lean_object* v_motive_1570_, lean_object* v_t_1571_, lean_object* v_h_1572_, lean_object* v_responseError_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1571_, v_responseError_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_metaData(lean_object* v_x_1580_){
_start:
{
switch(lean_obj_tag(v_x_1580_))
{
case 0:
{
lean_object* v_id_1581_; lean_object* v_method_1582_; lean_object* v___x_1583_; 
v_id_1581_ = lean_ctor_get(v_x_1580_, 0);
lean_inc(v_id_1581_);
v_method_1582_ = lean_ctor_get(v_x_1580_, 1);
lean_inc_ref(v_method_1582_);
lean_dec_ref_known(v_x_1580_, 3);
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v_id_1581_);
lean_ctor_set(v___x_1583_, 1, v_method_1582_);
return v___x_1583_;
}
case 1:
{
lean_object* v_method_1584_; lean_object* v___x_1585_; 
v_method_1584_ = lean_ctor_get(v_x_1580_, 0);
lean_inc_ref(v_method_1584_);
lean_dec_ref_known(v_x_1580_, 2);
v___x_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_method_1584_);
return v___x_1585_;
}
case 2:
{
lean_object* v_id_1586_; lean_object* v___x_1587_; 
v_id_1586_ = lean_ctor_get(v_x_1580_, 0);
lean_inc(v_id_1586_);
lean_dec_ref_known(v_x_1580_, 2);
v___x_1587_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_id_1586_);
return v___x_1587_;
}
default: 
{
lean_object* v_id_1588_; uint8_t v_code_1589_; lean_object* v_message_1590_; lean_object* v_data_x3f_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
v_id_1588_ = lean_ctor_get(v_x_1580_, 0);
v_code_1589_ = lean_ctor_get_uint8(v_x_1580_, sizeof(void*)*3);
v_message_1590_ = lean_ctor_get(v_x_1580_, 1);
v_data_x3f_1591_ = lean_ctor_get(v_x_1580_, 2);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_x_1580_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v_x_1580_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_data_x3f_1591_);
lean_inc(v_message_1590_);
lean_inc(v_id_1588_);
lean_dec(v_x_1580_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_id_1588_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_message_1590_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_data_x3f_1591_);
lean_ctor_set_uint8(v_reuseFailAlloc_1597_, sizeof(void*)*3, v_code_1589_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_toMessage(lean_object* v_x_1599_){
_start:
{
switch(lean_obj_tag(v_x_1599_))
{
case 0:
{
lean_object* v_id_1600_; lean_object* v_method_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_id_1600_ = lean_ctor_get(v_x_1599_, 0);
lean_inc(v_id_1600_);
v_method_1601_ = lean_ctor_get(v_x_1599_, 1);
lean_inc_ref(v_method_1601_);
lean_dec_ref_known(v_x_1599_, 2);
v___x_1602_ = lean_box(0);
v___x_1603_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1603_, 0, v_id_1600_);
lean_ctor_set(v___x_1603_, 1, v_method_1601_);
lean_ctor_set(v___x_1603_, 2, v___x_1602_);
return v___x_1603_;
}
case 1:
{
lean_object* v_method_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_method_1604_ = lean_ctor_get(v_x_1599_, 0);
lean_inc_ref(v_method_1604_);
lean_dec_ref_known(v_x_1599_, 1);
v___x_1605_ = lean_box(0);
v___x_1606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1606_, 0, v_method_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
return v___x_1606_;
}
case 2:
{
lean_object* v_id_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_id_1607_ = lean_ctor_get(v_x_1599_, 0);
lean_inc(v_id_1607_);
lean_dec_ref_known(v_x_1599_, 1);
v___x_1608_ = lean_box(0);
v___x_1609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1609_, 0, v_id_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
return v___x_1609_;
}
default: 
{
lean_object* v_id_1610_; uint8_t v_code_1611_; lean_object* v_message_1612_; lean_object* v_data_x3f_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_id_1610_ = lean_ctor_get(v_x_1599_, 0);
v_code_1611_ = lean_ctor_get_uint8(v_x_1599_, sizeof(void*)*3);
v_message_1612_ = lean_ctor_get(v_x_1599_, 1);
v_data_x3f_1613_ = lean_ctor_get(v_x_1599_, 2);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_x_1599_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v_x_1599_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_data_x3f_1613_);
lean_inc(v_message_1612_);
lean_inc(v_id_1610_);
lean_dec(v_x_1599_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_id_1610_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_message_1612_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_data_x3f_1613_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*3, v_code_1611_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(lean_object* v_a_1624_){
_start:
{
lean_object* v_fst_1625_; lean_object* v_snd_1626_; lean_object* v___x_1627_; uint8_t v_decide_1628_; 
v_fst_1625_ = lean_ctor_get(v_a_1624_, 0);
v_snd_1626_ = lean_ctor_get(v_a_1624_, 1);
v___x_1627_ = lean_string_utf8_byte_size(v_fst_1625_);
v_decide_1628_ = lean_nat_dec_eq(v_snd_1626_, v___x_1627_);
if (v_decide_1628_ == 0)
{
uint32_t v___x_1629_; uint32_t v___x_1630_; uint8_t v___x_1631_; 
v___x_1629_ = lean_string_utf8_get_fast(v_fst_1625_, v_snd_1626_);
v___x_1630_ = 34;
v___x_1631_ = lean_uint32_dec_eq(v___x_1629_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1));
v___x_1633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1633_, 0, v_a_1624_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
return v___x_1633_;
}
else
{
lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1643_; 
lean_inc(v_snd_1626_);
lean_inc(v_fst_1625_);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_a_1624_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; lean_object* v_unused_1645_; 
v_unused_1644_ = lean_ctor_get(v_a_1624_, 1);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_a_1624_, 0);
lean_dec(v_unused_1645_);
v___x_1635_ = v_a_1624_;
v_isShared_1636_ = v_isSharedCheck_1643_;
goto v_resetjp_1634_;
}
else
{
lean_dec(v_a_1624_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1643_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1637_ = lean_string_utf8_next_fast(v_fst_1625_, v_snd_1626_);
lean_dec(v_snd_1626_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 1, v___x_1637_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_fst_1625_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_1641_ = l_Lean_Json_Parser_strCore(v___x_1640_, v___x_1639_);
return v___x_1641_;
}
}
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1647_, 0, v_a_1624_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1649_; 
lean_inc_ref(v_a_1648_);
v___x_1649_ = l_Lean_Json_Parser_num(v_a_1648_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_pos_1650_; lean_object* v_res_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_a_1648_);
v_pos_1650_ = lean_ctor_get(v___x_1649_, 0);
v_res_1651_ = lean_ctor_get(v___x_1649_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1653_ = v___x_1649_;
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_res_1651_);
lean_inc(v_pos_1650_);
lean_dec(v___x_1649_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_res_1651_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v___x_1655_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_pos_1650_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
lean_object* v_pos_1660_; lean_object* v_err_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1714_; 
v_pos_1660_ = lean_ctor_get(v___x_1649_, 0);
v_err_1661_ = lean_ctor_get(v___x_1649_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1663_ = v___x_1649_;
v_isShared_1664_ = v_isSharedCheck_1714_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_err_1661_);
lean_inc(v_pos_1660_);
lean_dec(v___x_1649_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1714_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v_snd_1665_; lean_object* v_snd_1666_; uint8_t v_decide_1667_; 
v_snd_1665_ = lean_ctor_get(v_a_1648_, 1);
lean_inc(v_snd_1665_);
lean_dec_ref(v_a_1648_);
v_snd_1666_ = lean_ctor_get(v_pos_1660_, 1);
v_decide_1667_ = lean_nat_dec_eq(v_snd_1665_, v_snd_1666_);
lean_dec(v_snd_1665_);
if (v_decide_1667_ == 0)
{
lean_object* v___x_1669_; 
if (v_isShared_1664_ == 0)
{
v___x_1669_ = v___x_1663_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_pos_1660_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_err_1661_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
else
{
lean_object* v___x_1671_; 
lean_inc(v_snd_1666_);
lean_del_object(v___x_1663_);
lean_dec(v_err_1661_);
v___x_1671_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v_pos_1660_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_pos_1672_; lean_object* v_res_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v_snd_1666_);
v_pos_1672_ = lean_ctor_get(v___x_1671_, 0);
v_res_1673_ = lean_ctor_get(v___x_1671_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1675_ = v___x_1671_;
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_res_1673_);
lean_inc(v_pos_1672_);
lean_dec(v___x_1671_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_res_1673_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 1, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_pos_1672_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
lean_object* v_pos_1682_; lean_object* v_err_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1713_; 
v_pos_1682_ = lean_ctor_get(v___x_1671_, 0);
v_err_1683_ = lean_ctor_get(v___x_1671_, 1);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1685_ = v___x_1671_;
v_isShared_1686_ = v_isSharedCheck_1713_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_err_1683_);
lean_inc(v_pos_1682_);
lean_dec(v___x_1671_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1713_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_snd_1687_; uint8_t v_decide_1688_; 
v_snd_1687_ = lean_ctor_get(v_pos_1682_, 1);
v_decide_1688_ = lean_nat_dec_eq(v_snd_1666_, v_snd_1687_);
lean_dec(v_snd_1666_);
if (v_decide_1688_ == 0)
{
lean_object* v___x_1690_; 
if (v_isShared_1686_ == 0)
{
v___x_1690_ = v___x_1685_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_pos_1682_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_err_1683_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_del_object(v___x_1685_);
lean_dec(v_err_1683_);
v___x_1692_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___x_1693_ = l_Std_Internal_Parsec_String_pstring(v___x_1692_, v_pos_1682_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_pos_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1702_; 
v_pos_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v___x_1693_, 1);
lean_dec(v_unused_1703_);
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_pos_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1702_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1698_ = lean_box(2);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 1, v___x_1698_);
v___x_1700_ = v___x_1696_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_pos_1694_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
else
{
lean_object* v_pos_1704_; lean_object* v_err_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
v_pos_1704_ = lean_ctor_get(v___x_1693_, 0);
v_err_1705_ = lean_ctor_get(v___x_1693_, 1);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1693_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_err_1705_);
lean_inc(v_pos_1704_);
lean_dec(v___x_1693_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_pos_1704_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_err_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object* v_j_1715_, lean_object* v_k_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_Json_getObjValD(v_j_1715_, v_k_1716_);
switch(lean_obj_tag(v___x_1717_))
{
case 3:
{
lean_object* v_s_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1726_; 
v_s_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_s_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set_tag(v___x_1720_, 0);
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_s_1718_);
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
case 2:
{
lean_object* v_n_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1735_; 
v_n_1727_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1729_ = v___x_1717_;
v_isShared_1730_ = v_isSharedCheck_1735_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_n_1727_);
lean_dec(v___x_1717_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1735_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 1);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_n_1727_);
v___x_1732_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
}
}
default: 
{
lean_object* v___x_1736_; 
lean_dec(v___x_1717_);
v___x_1736_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object* v_j_1737_, lean_object* v_k_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_j_1737_, v_k_1738_);
lean_dec_ref(v_k_1738_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object* v_j_1740_, lean_object* v_k_1741_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Json_getObjValD(v_j_1740_, v_k_1741_);
if (lean_obj_tag(v___x_1744_) == 2)
{
lean_object* v_n_1745_; lean_object* v_mantissa_1746_; lean_object* v_exponent_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v_n_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc_ref(v_n_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v_mantissa_1746_ = lean_ctor_get(v_n_1745_, 0);
lean_inc(v_mantissa_1746_);
v_exponent_1747_ = lean_ctor_get(v_n_1745_, 1);
lean_inc(v_exponent_1747_);
lean_dec_ref(v_n_1745_);
v___x_1748_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_1749_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_1751_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1752_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_1753_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1752_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_1755_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_1757_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_1759_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_1761_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_1763_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_1765_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_1767_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_1769_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_1771_ = lean_int_dec_eq(v_mantissa_1746_, v___x_1770_);
lean_dec(v_mantissa_1746_);
if (v___x_1771_ == 0)
{
lean_dec(v_exponent_1747_);
goto v___jp_1742_;
}
else
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1772_);
lean_dec(v_exponent_1747_);
if (v___x_1773_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1774_; 
v___x_1774_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_1774_;
}
}
}
else
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
lean_dec(v_mantissa_1746_);
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1775_);
lean_dec(v_exponent_1747_);
if (v___x_1776_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_1777_;
}
}
}
else
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
lean_dec(v_mantissa_1746_);
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1778_);
lean_dec(v_exponent_1747_);
if (v___x_1779_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_1780_;
}
}
}
else
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
lean_dec(v_mantissa_1746_);
v___x_1781_ = lean_unsigned_to_nat(0u);
v___x_1782_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1781_);
lean_dec(v_exponent_1747_);
if (v___x_1782_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_1783_;
}
}
}
else
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
lean_dec(v_mantissa_1746_);
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1784_);
lean_dec(v_exponent_1747_);
if (v___x_1785_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1786_; 
v___x_1786_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_1786_;
}
}
}
else
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
lean_dec(v_mantissa_1746_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1787_);
lean_dec(v_exponent_1747_);
if (v___x_1788_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_1789_;
}
}
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
lean_dec(v_mantissa_1746_);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1790_);
lean_dec(v_exponent_1747_);
if (v___x_1791_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1792_; 
v___x_1792_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_1792_;
}
}
}
else
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
lean_dec(v_mantissa_1746_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1793_);
lean_dec(v_exponent_1747_);
if (v___x_1794_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1795_; 
v___x_1795_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_1795_;
}
}
}
else
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
lean_dec(v_mantissa_1746_);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1796_);
lean_dec(v_exponent_1747_);
if (v___x_1797_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_1798_;
}
}
}
else
{
lean_object* v___x_1799_; uint8_t v___x_1800_; 
lean_dec(v_mantissa_1746_);
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1799_);
lean_dec(v_exponent_1747_);
if (v___x_1800_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_1801_;
}
}
}
else
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
lean_dec(v_mantissa_1746_);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1802_);
lean_dec(v_exponent_1747_);
if (v___x_1803_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1804_; 
v___x_1804_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_1804_;
}
}
}
else
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
lean_dec(v_mantissa_1746_);
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1806_ = lean_nat_dec_eq(v_exponent_1747_, v___x_1805_);
lean_dec(v_exponent_1747_);
if (v___x_1806_ == 0)
{
goto v___jp_1742_;
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_1807_;
}
}
}
else
{
lean_dec(v___x_1744_);
goto v___jp_1742_;
}
v___jp_1742_:
{
lean_object* v___x_1743_; 
v___x_1743_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object* v_j_1808_, lean_object* v_k_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_j_1808_, v_k_1809_);
lean_dec_ref(v_k_1809_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object* v_j_1811_, lean_object* v_k_1812_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = l_Lean_Json_getObjValD(v_j_1811_, v_k_1812_);
v___x_1814_ = l_Lean_Json_getStr_x3f(v___x_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object* v_j_1815_, lean_object* v_k_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_j_1815_, v_k_1816_);
lean_dec_ref(v_k_1816_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object* v_input_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v_fst_1854_; lean_object* v_snd_1855_; lean_object* v___x_1856_; uint8_t v_decide_1857_; 
v_fst_1854_ = lean_ctor_get(v_a_1828_, 0);
v_snd_1855_ = lean_ctor_get(v_a_1828_, 1);
v___x_1856_ = lean_string_utf8_byte_size(v_fst_1854_);
v_decide_1857_ = lean_nat_dec_eq(v_snd_1855_, v___x_1856_);
if (v_decide_1857_ == 0)
{
lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_2207_; 
lean_inc(v_snd_1855_);
lean_inc(v_fst_1854_);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_a_1828_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; lean_object* v_unused_2209_; 
v_unused_2208_ = lean_ctor_get(v_a_1828_, 1);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_a_1828_, 0);
lean_dec(v_unused_2209_);
v___x_1859_ = v_a_1828_;
v_isShared_1860_ = v_isSharedCheck_2207_;
goto v_resetjp_1858_;
}
else
{
lean_dec(v_a_1828_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_2207_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = lean_string_utf8_next_fast(v_fst_1854_, v_snd_1855_);
lean_dec(v_snd_1855_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 1, v___x_1861_);
v___x_1863_ = v___x_1859_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_fst_1854_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_2206_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; 
v___x_1864_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1863_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_pos_1865_; lean_object* v_res_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_2196_; 
v_pos_1865_ = lean_ctor_get(v___x_1864_, 0);
v_res_1866_ = lean_ctor_get(v___x_1864_, 1);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_1868_ = v___x_1864_;
v_isShared_1869_ = v_isSharedCheck_2196_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_res_1866_);
lean_inc(v_pos_1865_);
lean_dec(v___x_1864_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_2196_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v_fst_1870_; lean_object* v_snd_1871_; lean_object* v___x_1872_; uint8_t v_decide_1873_; 
v_fst_1870_ = lean_ctor_get(v_pos_1865_, 0);
v_snd_1871_ = lean_ctor_get(v_pos_1865_, 1);
v___x_1872_ = lean_string_utf8_byte_size(v_fst_1870_);
v_decide_1873_ = lean_nat_dec_eq(v_snd_1871_, v___x_1872_);
if (v_decide_1873_ == 0)
{
lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_2189_; 
lean_inc(v_snd_1871_);
lean_inc(v_fst_1870_);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_pos_1865_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; lean_object* v_unused_2191_; 
v_unused_2190_ = lean_ctor_get(v_pos_1865_, 1);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_pos_1865_, 0);
lean_dec(v_unused_2191_);
v___x_1875_ = v_pos_1865_;
v_isShared_1876_ = v_isSharedCheck_2189_;
goto v_resetjp_1874_;
}
else
{
lean_dec(v_pos_1865_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_2189_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1877_ = lean_string_utf8_next_fast(v_fst_1870_, v_snd_1871_);
lean_dec(v_snd_1871_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 1, v___x_1877_);
v___x_1879_ = v___x_1875_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_fst_1870_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_2188_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v_id_1881_; uint8_t v_code_1882_; lean_object* v_message_1883_; lean_object* v_data_x3f_1884_; lean_object* v_a_1893_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
v___x_1899_ = lean_string_dec_eq(v_res_1866_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
v___x_1901_ = lean_string_dec_eq(v_res_1866_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1902_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1903_ = lean_string_dec_eq(v_res_1866_, v___x_1902_);
lean_dec(v_res_1866_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_del_object(v___x_1868_);
lean_dec_ref(v_input_1827_);
v___x_1904_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3));
v___x_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1879_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_Json_parse(v_input_1827_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1915_; 
lean_del_object(v___x_1868_);
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1915_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 1);
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1879_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
return v___x_1913_;
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1906_, 0);
lean_inc_n(v_a_1916_, 2);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1917_ = l_Lean_Json_getObjVal_x3f(v_a_1916_, v___x_1900_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; 
lean_dec(v_a_1916_);
lean_del_object(v___x_1868_);
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v_a_1893_ = v_a_1918_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1919_; 
v_a_1919_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1917_, 1);
if (lean_obj_tag(v_a_1919_) == 3)
{
lean_object* v_s_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_s_1920_ = lean_ctor_get(v_a_1919_, 0);
lean_inc_ref(v_s_1920_);
lean_dec_ref_known(v_a_1919_, 1);
v___x_1921_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1922_ = lean_string_dec_eq(v_s_1920_, v___x_1921_);
lean_dec_ref(v_s_1920_);
if (v___x_1922_ == 0)
{
lean_dec(v_a_1916_);
lean_del_object(v___x_1868_);
goto v___jp_1896_;
}
else
{
lean_object* v___x_1923_; 
lean_inc(v_a_1916_);
v___x_1923_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_1916_, v___x_1898_);
if (lean_obj_tag(v___x_1923_) == 0)
{
goto v___jp_1951_;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1916_);
v___x_1957_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1916_, v___x_1956_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_dec_ref_known(v___x_1957_, 1);
goto v___jp_1951_;
}
else
{
lean_dec_ref_known(v___x_1957_, 1);
lean_dec_ref_known(v___x_1923_, 1);
lean_dec(v_a_1916_);
lean_del_object(v___x_1868_);
goto v___jp_1889_;
}
}
v___jp_1924_:
{
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1925_; 
lean_dec(v_a_1916_);
lean_del_object(v___x_1868_);
v_a_1925_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1923_, 1);
v_a_1893_ = v_a_1925_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1927_ = l_Lean_Json_getObjVal_x3f(v_a_1916_, v___x_1902_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; 
lean_dec(v_a_1926_);
lean_del_object(v___x_1868_);
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v_a_1893_ = v_a_1928_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_a_1929_ = lean_ctor_get(v___x_1927_, 0);
lean_inc_n(v_a_1929_, 2);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1930_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1931_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_1929_, v___x_1930_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; 
lean_dec(v_a_1929_);
lean_dec(v_a_1926_);
lean_del_object(v___x_1868_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v_a_1893_ = v_a_1932_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_a_1933_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1934_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1929_);
v___x_1935_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1929_, v___x_1934_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; 
lean_dec(v_a_1933_);
lean_dec(v_a_1929_);
lean_dec(v_a_1926_);
lean_del_object(v___x_1868_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v_a_1893_ = v_a_1936_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_a_1937_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1938_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1939_ = l_Lean_Json_getObjVal_x3f(v_a_1929_, v___x_1938_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v___x_1940_; uint8_t v___x_1941_; 
lean_dec_ref_known(v___x_1939_, 1);
v___x_1940_ = lean_box(0);
v___x_1941_ = lean_unbox(v_a_1933_);
lean_dec(v_a_1933_);
v_id_1881_ = v_a_1926_;
v_code_1882_ = v___x_1941_;
v_message_1883_ = v_a_1937_;
v_data_x3f_1884_ = v___x_1940_;
goto v___jp_1880_;
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1950_; 
v_a_1942_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1944_ = v___x_1939_;
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1939_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1950_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_unbox(v_a_1933_);
lean_dec(v_a_1933_);
v_id_1881_ = v_a_1926_;
v_code_1882_ = v___x_1948_;
v_message_1883_ = v_a_1937_;
v_data_x3f_1884_ = v___x_1947_;
goto v___jp_1880_;
}
}
}
}
}
}
}
}
v___jp_1951_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1916_);
v___x_1953_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1916_, v___x_1952_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_dec_ref_known(v___x_1953_, 1);
if (lean_obj_tag(v___x_1923_) == 0)
{
goto v___jp_1924_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_1916_);
v___x_1955_ = l_Lean_Json_getObjVal_x3f(v_a_1916_, v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_dec_ref_known(v___x_1955_, 1);
goto v___jp_1924_;
}
else
{
lean_dec_ref_known(v___x_1955_, 1);
lean_dec_ref_known(v___x_1923_, 1);
lean_dec(v_a_1916_);
lean_del_object(v___x_1868_);
goto v___jp_1889_;
}
}
}
else
{
lean_dec_ref_known(v___x_1953_, 1);
lean_dec_ref(v___x_1923_);
lean_dec(v_a_1916_);
lean_del_object(v___x_1868_);
goto v___jp_1889_;
}
}
}
}
else
{
lean_dec(v_a_1919_);
lean_dec(v_a_1916_);
lean_del_object(v___x_1868_);
goto v___jp_1896_;
}
}
}
}
}
else
{
lean_object* v___x_1958_; 
lean_del_object(v___x_1868_);
lean_dec(v_res_1866_);
lean_dec_ref(v_input_1827_);
v___x_1958_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1879_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_pos_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_2007_; 
v_pos_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; 
v_unused_2008_ = lean_ctor_get(v___x_1958_, 1);
lean_dec(v_unused_2008_);
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_2007_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_pos_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_2007_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v_fst_1963_; lean_object* v_snd_1964_; uint8_t v___y_1966_; lean_object* v___x_2005_; uint8_t v_decide_2006_; 
v_fst_1963_ = lean_ctor_get(v_pos_1959_, 0);
v_snd_1964_ = lean_ctor_get(v_pos_1959_, 1);
v___x_2005_ = lean_string_utf8_byte_size(v_fst_1963_);
v_decide_2006_ = lean_nat_dec_eq(v_snd_1964_, v___x_2005_);
if (v_decide_2006_ == 0)
{
v___y_1966_ = v___x_1901_;
goto v___jp_1965_;
}
else
{
v___y_1966_ = v___x_1899_;
goto v___jp_1965_;
}
v___jp_1965_:
{
if (v___y_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_box(0);
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 1);
lean_ctor_set(v___x_1961_, 1, v___x_1967_);
v___x_1969_ = v___x_1961_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_pos_1959_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
else
{
lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2002_; 
lean_inc(v_snd_1964_);
lean_inc(v_fst_1963_);
lean_del_object(v___x_1961_);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_pos_1959_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; lean_object* v_unused_2004_; 
v_unused_2003_ = lean_ctor_get(v_pos_1959_, 1);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_pos_1959_, 0);
lean_dec(v_unused_2004_);
v___x_1972_ = v_pos_1959_;
v_isShared_1973_ = v_isSharedCheck_2002_;
goto v_resetjp_1971_;
}
else
{
lean_dec(v_pos_1959_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2002_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1974_ = lean_string_utf8_next_fast(v_fst_1963_, v_snd_1964_);
lean_dec(v_snd_1964_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 1, v___x_1974_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_fst_1963_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; 
v___x_1977_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1976_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_pos_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1990_; 
v_pos_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; 
v_unused_1991_ = lean_ctor_get(v___x_1977_, 1);
lean_dec(v_unused_1991_);
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1990_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_pos_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1990_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_fst_1982_; lean_object* v_snd_1983_; lean_object* v___x_1984_; uint8_t v_decide_1985_; 
v_fst_1982_ = lean_ctor_get(v_pos_1978_, 0);
v_snd_1983_ = lean_ctor_get(v_pos_1978_, 1);
v___x_1984_ = lean_string_utf8_byte_size(v_fst_1982_);
v_decide_1985_ = lean_nat_dec_eq(v_snd_1983_, v___x_1984_);
if (v_decide_1985_ == 0)
{
lean_inc(v_snd_1983_);
lean_inc(v_fst_1982_);
lean_del_object(v___x_1980_);
lean_dec(v_pos_1978_);
v___y_1830_ = v_snd_1983_;
v___y_1831_ = v_fst_1982_;
goto v___jp_1829_;
}
else
{
if (v___x_1899_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1986_ = lean_box(0);
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 1);
lean_ctor_set(v___x_1980_, 1, v___x_1986_);
v___x_1988_ = v___x_1980_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_pos_1978_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
else
{
lean_inc(v_snd_1983_);
lean_inc(v_fst_1982_);
lean_del_object(v___x_1980_);
lean_dec(v_pos_1978_);
v___y_1830_ = v_snd_1983_;
v___y_1831_ = v_fst_1982_;
goto v___jp_1829_;
}
}
}
}
else
{
lean_object* v_pos_1992_; lean_object* v_err_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
v_pos_1992_ = lean_ctor_get(v___x_1977_, 0);
v_err_1993_ = lean_ctor_get(v___x_1977_, 1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1977_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_err_1993_);
lean_inc(v_pos_1992_);
lean_dec(v___x_1977_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_pos_1992_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_err_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
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
lean_object* v_pos_2009_; lean_object* v_err_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
v_pos_2009_ = lean_ctor_get(v___x_1958_, 0);
v_err_2010_ = lean_ctor_get(v___x_1958_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1958_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_err_2010_);
lean_inc(v_pos_2009_);
lean_dec(v___x_1958_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_pos_2009_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_err_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
else
{
lean_object* v___x_2018_; 
lean_del_object(v___x_1868_);
lean_dec(v_res_1866_);
lean_dec_ref(v_input_1827_);
v___x_2018_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(v___x_1879_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_pos_2019_; lean_object* v_res_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2178_; 
v_pos_2019_ = lean_ctor_get(v___x_2018_, 0);
v_res_2020_ = lean_ctor_get(v___x_2018_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2022_ = v___x_2018_;
v_isShared_2023_ = v_isSharedCheck_2178_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_res_2020_);
lean_inc(v_pos_2019_);
lean_dec(v___x_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2178_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v_fst_2029_; lean_object* v_snd_2030_; lean_object* v___x_2031_; uint8_t v_decide_2032_; 
v_fst_2029_ = lean_ctor_get(v_pos_2019_, 0);
v_snd_2030_ = lean_ctor_get(v_pos_2019_, 1);
v___x_2031_ = lean_string_utf8_byte_size(v_fst_2029_);
v_decide_2032_ = lean_nat_dec_eq(v_snd_2030_, v___x_2031_);
if (v_decide_2032_ == 0)
{
if (v___x_1899_ == 0)
{
lean_dec(v_res_2020_);
goto v___jp_2024_;
}
else
{
lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2175_; 
lean_inc(v_snd_2030_);
lean_inc(v_fst_2029_);
lean_del_object(v___x_2022_);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_pos_2019_);
if (v_isSharedCheck_2175_ == 0)
{
lean_object* v_unused_2176_; lean_object* v_unused_2177_; 
v_unused_2176_ = lean_ctor_get(v_pos_2019_, 1);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_pos_2019_, 0);
lean_dec(v_unused_2177_);
v___x_2034_ = v_pos_2019_;
v_isShared_2035_ = v_isSharedCheck_2175_;
goto v_resetjp_2033_;
}
else
{
lean_dec(v_pos_2019_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2175_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = lean_string_utf8_next_fast(v_fst_2029_, v_snd_2030_);
lean_dec(v_snd_2030_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v___x_2036_);
v___x_2038_ = v___x_2034_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_fst_2029_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; 
v___x_2039_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2038_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_pos_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2163_; 
v_pos_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; 
v_unused_2164_ = lean_ctor_get(v___x_2039_, 1);
lean_dec(v_unused_2164_);
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2163_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_pos_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2163_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v_fst_2044_; lean_object* v_snd_2045_; lean_object* v___x_2046_; uint8_t v_decide_2047_; 
v_fst_2044_ = lean_ctor_get(v_pos_2040_, 0);
v_snd_2045_ = lean_ctor_get(v_pos_2040_, 1);
v___x_2046_ = lean_string_utf8_byte_size(v_fst_2044_);
v_decide_2047_ = lean_nat_dec_eq(v_snd_2045_, v___x_2046_);
if (v_decide_2047_ == 0)
{
lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2156_; 
lean_inc(v_snd_2045_);
lean_inc(v_fst_2044_);
lean_del_object(v___x_2042_);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_pos_2040_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; lean_object* v_unused_2158_; 
v_unused_2157_ = lean_ctor_get(v_pos_2040_, 1);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_pos_2040_, 0);
lean_dec(v_unused_2158_);
v___x_2049_ = v_pos_2040_;
v_isShared_2050_ = v_isSharedCheck_2156_;
goto v_resetjp_2048_;
}
else
{
lean_dec(v_pos_2040_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2156_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2051_ = lean_string_utf8_next_fast(v_fst_2044_, v_snd_2045_);
lean_dec(v_snd_2045_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v___x_2051_);
v___x_2053_ = v___x_2049_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_fst_2044_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2054_; 
v___x_2054_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2053_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_pos_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2144_; 
v_pos_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v___x_2054_, 1);
lean_dec(v_unused_2145_);
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2144_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_pos_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2144_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_fst_2059_; lean_object* v_snd_2060_; lean_object* v___x_2061_; uint8_t v_decide_2062_; 
v_fst_2059_ = lean_ctor_get(v_pos_2055_, 0);
v_snd_2060_ = lean_ctor_get(v_pos_2055_, 1);
v___x_2061_ = lean_string_utf8_byte_size(v_fst_2059_);
v_decide_2062_ = lean_nat_dec_eq(v_snd_2060_, v___x_2061_);
if (v_decide_2062_ == 0)
{
lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2137_; 
lean_inc(v_snd_2060_);
lean_inc(v_fst_2059_);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_pos_2055_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; lean_object* v_unused_2139_; 
v_unused_2138_ = lean_ctor_get(v_pos_2055_, 1);
lean_dec(v_unused_2138_);
v_unused_2139_ = lean_ctor_get(v_pos_2055_, 0);
lean_dec(v_unused_2139_);
v___x_2064_ = v_pos_2055_;
v_isShared_2065_ = v_isSharedCheck_2137_;
goto v_resetjp_2063_;
}
else
{
lean_dec(v_pos_2055_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2137_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2066_ = lean_string_utf8_next_fast(v_fst_2059_, v_snd_2060_);
lean_dec(v_snd_2060_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v___x_2066_);
v___x_2068_ = v___x_2064_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_fst_2059_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; 
v___x_2069_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_pos_2070_; lean_object* v_res_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2126_; 
v_pos_2070_ = lean_ctor_get(v___x_2069_, 0);
v_res_2071_ = lean_ctor_get(v___x_2069_, 1);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2073_ = v___x_2069_;
v_isShared_2074_ = v_isSharedCheck_2126_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_res_2071_);
lean_inc(v_pos_2070_);
lean_dec(v___x_2069_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2126_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2081_ = lean_string_dec_eq(v_res_2071_, v___x_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
lean_del_object(v___x_2073_);
v___x_2082_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2083_ = lean_string_dec_eq(v_res_2071_, v___x_2082_);
lean_dec(v_res_2071_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
lean_dec(v_res_2020_);
v___x_2084_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5));
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 1);
lean_ctor_set(v___x_2057_, 1, v___x_2084_);
lean_ctor_set(v___x_2057_, 0, v_pos_2070_);
v___x_2086_ = v___x_2057_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_pos_2070_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2088_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_res_2020_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v___x_2088_);
lean_ctor_set(v___x_2057_, 0, v_pos_2070_);
v___x_2090_ = v___x_2057_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_pos_2070_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
else
{
lean_object* v_fst_2092_; lean_object* v_snd_2093_; lean_object* v___x_2094_; uint8_t v_decide_2095_; 
lean_dec(v_res_2071_);
lean_del_object(v___x_2057_);
v_fst_2092_ = lean_ctor_get(v_pos_2070_, 0);
v_snd_2093_ = lean_ctor_get(v_pos_2070_, 1);
v___x_2094_ = lean_string_utf8_byte_size(v_fst_2092_);
v_decide_2095_ = lean_nat_dec_eq(v_snd_2093_, v___x_2094_);
if (v_decide_2095_ == 0)
{
if (v___x_2081_ == 0)
{
lean_dec(v_res_2020_);
goto v___jp_2075_;
}
else
{
lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2123_; 
lean_inc(v_snd_2093_);
lean_inc(v_fst_2092_);
lean_del_object(v___x_2073_);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_pos_2070_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; lean_object* v_unused_2125_; 
v_unused_2124_ = lean_ctor_get(v_pos_2070_, 1);
lean_dec(v_unused_2124_);
v_unused_2125_ = lean_ctor_get(v_pos_2070_, 0);
lean_dec(v_unused_2125_);
v___x_2097_ = v_pos_2070_;
v_isShared_2098_ = v_isSharedCheck_2123_;
goto v_resetjp_2096_;
}
else
{
lean_dec(v_pos_2070_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2123_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_string_utf8_next_fast(v_fst_2092_, v_snd_2093_);
lean_dec(v_snd_2093_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v___x_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_fst_2092_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; 
v___x_2102_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2101_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_pos_2103_; lean_object* v_res_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2112_; 
v_pos_2103_ = lean_ctor_get(v___x_2102_, 0);
v_res_2104_ = lean_ctor_get(v___x_2102_, 1);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2106_ = v___x_2102_;
v_isShared_2107_ = v_isSharedCheck_2112_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_res_2104_);
lean_inc(v_pos_2103_);
lean_dec(v___x_2102_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2112_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2108_, 0, v_res_2020_);
lean_ctor_set(v___x_2108_, 1, v_res_2104_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v___x_2108_);
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_pos_2103_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
else
{
lean_object* v_pos_2113_; lean_object* v_err_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_res_2020_);
v_pos_2113_ = lean_ctor_get(v___x_2102_, 0);
v_err_2114_ = lean_ctor_get(v___x_2102_, 1);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2102_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_err_2114_);
lean_inc(v_pos_2113_);
lean_dec(v___x_2102_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_pos_2113_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_err_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2020_);
goto v___jp_2075_;
}
}
v___jp_2075_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_box(0);
if (v_isShared_2074_ == 0)
{
lean_ctor_set_tag(v___x_2073_, 1);
lean_ctor_set(v___x_2073_, 1, v___x_2076_);
v___x_2078_ = v___x_2073_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_pos_2070_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v_pos_2127_; lean_object* v_err_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_del_object(v___x_2057_);
lean_dec(v_res_2020_);
v_pos_2127_ = lean_ctor_get(v___x_2069_, 0);
v_err_2128_ = lean_ctor_get(v___x_2069_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2069_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_err_2128_);
lean_inc(v_pos_2127_);
lean_dec(v___x_2069_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_pos_2127_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_err_2128_);
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
}
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
lean_dec(v_res_2020_);
v___x_2140_ = lean_box(0);
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 1);
lean_ctor_set(v___x_2057_, 1, v___x_2140_);
v___x_2142_ = v___x_2057_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_pos_2055_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_pos_2146_; lean_object* v_err_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec(v_res_2020_);
v_pos_2146_ = lean_ctor_get(v___x_2054_, 0);
v_err_2147_ = lean_ctor_get(v___x_2054_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2054_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_err_2147_);
lean_inc(v_pos_2146_);
lean_dec(v___x_2054_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_pos_2146_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_err_2147_);
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
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v_res_2020_);
v___x_2159_ = lean_box(0);
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 1);
lean_ctor_set(v___x_2042_, 1, v___x_2159_);
v___x_2161_ = v___x_2042_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_pos_2040_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v_pos_2165_; lean_object* v_err_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v_res_2020_);
v_pos_2165_ = lean_ctor_get(v___x_2039_, 0);
v_err_2166_ = lean_ctor_get(v___x_2039_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2039_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_err_2166_);
lean_inc(v_pos_2165_);
lean_dec(v___x_2039_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_pos_2165_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_err_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2020_);
goto v___jp_2024_;
}
v___jp_2024_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = lean_box(0);
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 1);
lean_ctor_set(v___x_2022_, 1, v___x_2025_);
v___x_2027_ = v___x_2022_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_pos_2019_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_pos_2179_; lean_object* v_err_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v_pos_2179_ = lean_ctor_get(v___x_2018_, 0);
v_err_2180_ = lean_ctor_get(v___x_2018_, 1);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2018_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_err_2180_);
lean_inc(v_pos_2179_);
lean_dec(v___x_2018_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_pos_2179_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_err_2180_);
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
v___jp_1880_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1885_, 0, v_id_1881_);
lean_ctor_set(v___x_1885_, 1, v_message_1883_);
lean_ctor_set(v___x_1885_, 2, v_data_x3f_1884_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*3, v_code_1882_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___x_1885_);
lean_ctor_set(v___x_1868_, 0, v___x_1879_);
v___x_1887_ = v___x_1868_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
v___jp_1889_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1));
v___x_1891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1879_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
return v___x_1891_;
}
v___jp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v_a_1893_);
v___x_1895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1879_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
return v___x_1895_;
}
v___jp_1896_:
{
lean_object* v___x_1897_; 
v___x_1897_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_1893_ = v___x_1897_;
goto v___jp_1892_;
}
}
}
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
lean_dec(v_res_1866_);
lean_dec_ref(v_input_1827_);
v___x_2192_ = lean_box(0);
if (v_isShared_1869_ == 0)
{
lean_ctor_set_tag(v___x_1868_, 1);
lean_ctor_set(v___x_1868_, 1, v___x_2192_);
v___x_2194_ = v___x_1868_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_pos_1865_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v___x_2192_);
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
else
{
lean_object* v_pos_2197_; lean_object* v_err_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref(v_input_1827_);
v_pos_2197_ = lean_ctor_get(v___x_1864_, 0);
v_err_2198_ = lean_ctor_get(v___x_1864_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_1864_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_err_2198_);
lean_inc(v_pos_2197_);
lean_dec(v___x_1864_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_pos_2197_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_err_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec_ref(v_input_1827_);
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2211_, 0, v_a_1828_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
return v___x_2211_;
}
v___jp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = lean_string_utf8_next_fast(v___y_1831_, v___y_1830_);
lean_dec(v___y_1830_);
v___x_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___y_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1833_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_pos_1835_; lean_object* v_res_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1844_; 
v_pos_1835_ = lean_ctor_get(v___x_1834_, 0);
v_res_1836_ = lean_ctor_get(v___x_1834_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1838_ = v___x_1834_;
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_res_1836_);
lean_inc(v_pos_1835_);
lean_dec(v___x_1834_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_res_1836_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 1, v___x_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_pos_1835_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
else
{
lean_object* v_pos_1845_; lean_object* v_err_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_pos_1845_ = lean_ctor_get(v___x_1834_, 0);
v_err_1846_ = lean_ctor_get(v___x_1834_, 1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1834_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_err_1846_);
lean_inc(v_pos_1845_);
lean_dec(v___x_1834_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_pos_1845_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_err_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object* v_input_2212_){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_inc_ref(v_input_2212_);
v___x_2213_ = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser), 2, 1);
lean_closure_set(v___x_2213_, 0, v_input_2212_);
v___x_2214_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2213_, v_input_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx(uint8_t v_x_2215_){
_start:
{
if (v_x_2215_ == 0)
{
lean_object* v___x_2216_; 
v___x_2216_ = lean_unsigned_to_nat(0u);
return v___x_2216_;
}
else
{
lean_object* v___x_2217_; 
v___x_2217_ = lean_unsigned_to_nat(1u);
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___boxed(lean_object* v_x_2218_){
_start:
{
uint8_t v_x_boxed_2219_; lean_object* v_res_2220_; 
v_x_boxed_2219_ = lean_unbox(v_x_2218_);
v_res_2220_ = l_Lean_JsonRpc_MessageDirection_ctorIdx(v_x_boxed_2219_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object* v_k_2221_){
_start:
{
lean_inc(v_k_2221_);
return v_k_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object* v_k_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(v_k_2222_);
lean_dec(v_k_2222_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object* v_motive_2224_, lean_object* v_ctorIdx_2225_, uint8_t v_t_2226_, lean_object* v_h_2227_, lean_object* v_k_2228_){
_start:
{
lean_inc(v_k_2228_);
return v_k_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object* v_motive_2229_, lean_object* v_ctorIdx_2230_, lean_object* v_t_2231_, lean_object* v_h_2232_, lean_object* v_k_2233_){
_start:
{
uint8_t v_t_boxed_2234_; lean_object* v_res_2235_; 
v_t_boxed_2234_ = lean_unbox(v_t_2231_);
v_res_2235_ = l_Lean_JsonRpc_MessageDirection_ctorElim(v_motive_2229_, v_ctorIdx_2230_, v_t_boxed_2234_, v_h_2232_, v_k_2233_);
lean_dec(v_k_2233_);
lean_dec(v_ctorIdx_2230_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object* v_clientToServer_2236_){
_start:
{
lean_inc(v_clientToServer_2236_);
return v_clientToServer_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object* v_clientToServer_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(v_clientToServer_2237_);
lean_dec(v_clientToServer_2237_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object* v_motive_2239_, uint8_t v_t_2240_, lean_object* v_h_2241_, lean_object* v_clientToServer_2242_){
_start:
{
lean_inc(v_clientToServer_2242_);
return v_clientToServer_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object* v_motive_2243_, lean_object* v_t_2244_, lean_object* v_h_2245_, lean_object* v_clientToServer_2246_){
_start:
{
uint8_t v_t_boxed_2247_; lean_object* v_res_2248_; 
v_t_boxed_2247_ = lean_unbox(v_t_2244_);
v_res_2248_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(v_motive_2243_, v_t_boxed_2247_, v_h_2245_, v_clientToServer_2246_);
lean_dec(v_clientToServer_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object* v_serverToClient_2249_){
_start:
{
lean_inc(v_serverToClient_2249_);
return v_serverToClient_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object* v_serverToClient_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(v_serverToClient_2250_);
lean_dec(v_serverToClient_2250_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object* v_motive_2252_, uint8_t v_t_2253_, lean_object* v_h_2254_, lean_object* v_serverToClient_2255_){
_start:
{
lean_inc(v_serverToClient_2255_);
return v_serverToClient_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object* v_motive_2256_, lean_object* v_t_2257_, lean_object* v_h_2258_, lean_object* v_serverToClient_2259_){
_start:
{
uint8_t v_t_boxed_2260_; lean_object* v_res_2261_; 
v_t_boxed_2260_ = lean_unbox(v_t_2257_);
v_res_2261_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(v_motive_2256_, v_t_boxed_2260_, v_h_2258_, v_serverToClient_2259_);
lean_dec(v_serverToClient_2259_);
return v_res_2261_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default(void){
_start:
{
uint8_t v___x_2262_; 
v___x_2262_ = 0;
return v___x_2262_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection(void){
_start:
{
uint8_t v___x_2263_; 
v___x_2263_ = 0;
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object* v_json_2278_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Json_getTag_x3f(v_json_2278_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v___x_2280_; 
v___x_2280_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1));
return v___x_2280_;
}
else
{
lean_object* v_val_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_val_2281_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_val_2281_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2282_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2));
v___x_2283_ = lean_string_dec_eq(v_val_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3));
v___x_2285_ = lean_string_dec_eq(v_val_2281_, v___x_2284_);
lean_dec(v_val_2281_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5));
return v___x_2286_;
}
else
{
lean_object* v___x_2287_; 
v___x_2287_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6));
return v___x_2287_;
}
}
else
{
lean_object* v___x_2288_; 
lean_dec(v_val_2281_);
v___x_2288_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7));
return v___x_2288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t v_x_2295_){
_start:
{
if (v_x_2295_ == 0)
{
lean_object* v___x_2296_; 
v___x_2296_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0));
return v___x_2296_;
}
else
{
lean_object* v___x_2297_; 
v___x_2297_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1));
return v___x_2297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object* v_x_2298_){
_start:
{
uint8_t v_x_44__boxed_2299_; lean_object* v_res_2300_; 
v_x_44__boxed_2299_ = lean_unbox(v_x_2298_);
v_res_2300_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_x_44__boxed_2299_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx(uint8_t v_x_2303_){
_start:
{
switch(v_x_2303_)
{
case 0:
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_unsigned_to_nat(0u);
return v___x_2304_;
}
case 1:
{
lean_object* v___x_2305_; 
v___x_2305_ = lean_unsigned_to_nat(1u);
return v___x_2305_;
}
case 2:
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_unsigned_to_nat(2u);
return v___x_2306_;
}
default: 
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_unsigned_to_nat(3u);
return v___x_2307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___boxed(lean_object* v_x_2308_){
_start:
{
uint8_t v_x_boxed_2309_; lean_object* v_res_2310_; 
v_x_boxed_2309_ = lean_unbox(v_x_2308_);
v_res_2310_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_boxed_2309_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object* v_k_2311_){
_start:
{
lean_inc(v_k_2311_);
return v_k_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object* v_k_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_JsonRpc_MessageKind_ctorElim___redArg(v_k_2312_);
lean_dec(v_k_2312_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object* v_motive_2314_, lean_object* v_ctorIdx_2315_, uint8_t v_t_2316_, lean_object* v_h_2317_, lean_object* v_k_2318_){
_start:
{
lean_inc(v_k_2318_);
return v_k_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object* v_motive_2319_, lean_object* v_ctorIdx_2320_, lean_object* v_t_2321_, lean_object* v_h_2322_, lean_object* v_k_2323_){
_start:
{
uint8_t v_t_boxed_2324_; lean_object* v_res_2325_; 
v_t_boxed_2324_ = lean_unbox(v_t_2321_);
v_res_2325_ = l_Lean_JsonRpc_MessageKind_ctorElim(v_motive_2319_, v_ctorIdx_2320_, v_t_boxed_2324_, v_h_2322_, v_k_2323_);
lean_dec(v_k_2323_);
lean_dec(v_ctorIdx_2320_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object* v_request_2326_){
_start:
{
lean_inc(v_request_2326_);
return v_request_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object* v_request_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_JsonRpc_MessageKind_request_elim___redArg(v_request_2327_);
lean_dec(v_request_2327_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object* v_motive_2329_, uint8_t v_t_2330_, lean_object* v_h_2331_, lean_object* v_request_2332_){
_start:
{
lean_inc(v_request_2332_);
return v_request_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object* v_motive_2333_, lean_object* v_t_2334_, lean_object* v_h_2335_, lean_object* v_request_2336_){
_start:
{
uint8_t v_t_boxed_2337_; lean_object* v_res_2338_; 
v_t_boxed_2337_ = lean_unbox(v_t_2334_);
v_res_2338_ = l_Lean_JsonRpc_MessageKind_request_elim(v_motive_2333_, v_t_boxed_2337_, v_h_2335_, v_request_2336_);
lean_dec(v_request_2336_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object* v_notification_2339_){
_start:
{
lean_inc(v_notification_2339_);
return v_notification_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object* v_notification_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_JsonRpc_MessageKind_notification_elim___redArg(v_notification_2340_);
lean_dec(v_notification_2340_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object* v_motive_2342_, uint8_t v_t_2343_, lean_object* v_h_2344_, lean_object* v_notification_2345_){
_start:
{
lean_inc(v_notification_2345_);
return v_notification_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object* v_motive_2346_, lean_object* v_t_2347_, lean_object* v_h_2348_, lean_object* v_notification_2349_){
_start:
{
uint8_t v_t_boxed_2350_; lean_object* v_res_2351_; 
v_t_boxed_2350_ = lean_unbox(v_t_2347_);
v_res_2351_ = l_Lean_JsonRpc_MessageKind_notification_elim(v_motive_2346_, v_t_boxed_2350_, v_h_2348_, v_notification_2349_);
lean_dec(v_notification_2349_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object* v_response_2352_){
_start:
{
lean_inc(v_response_2352_);
return v_response_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object* v_response_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_JsonRpc_MessageKind_response_elim___redArg(v_response_2353_);
lean_dec(v_response_2353_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object* v_motive_2355_, uint8_t v_t_2356_, lean_object* v_h_2357_, lean_object* v_response_2358_){
_start:
{
lean_inc(v_response_2358_);
return v_response_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object* v_motive_2359_, lean_object* v_t_2360_, lean_object* v_h_2361_, lean_object* v_response_2362_){
_start:
{
uint8_t v_t_boxed_2363_; lean_object* v_res_2364_; 
v_t_boxed_2363_ = lean_unbox(v_t_2360_);
v_res_2364_ = l_Lean_JsonRpc_MessageKind_response_elim(v_motive_2359_, v_t_boxed_2363_, v_h_2361_, v_response_2362_);
lean_dec(v_response_2362_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object* v_responseError_2365_){
_start:
{
lean_inc(v_responseError_2365_);
return v_responseError_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object* v_responseError_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(v_responseError_2366_);
lean_dec(v_responseError_2366_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object* v_motive_2368_, uint8_t v_t_2369_, lean_object* v_h_2370_, lean_object* v_responseError_2371_){
_start:
{
lean_inc(v_responseError_2371_);
return v_responseError_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object* v_motive_2372_, lean_object* v_t_2373_, lean_object* v_h_2374_, lean_object* v_responseError_2375_){
_start:
{
uint8_t v_t_boxed_2376_; lean_object* v_res_2377_; 
v_t_boxed_2376_ = lean_unbox(v_t_2373_);
v_res_2377_ = l_Lean_JsonRpc_MessageKind_responseError_elim(v_motive_2372_, v_t_boxed_2376_, v_h_2374_, v_responseError_2375_);
lean_dec(v_responseError_2375_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object* v_json_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_Json_getTag_x3f(v_json_2398_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v___x_2400_; 
v___x_2400_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0));
return v___x_2400_;
}
else
{
lean_object* v_val_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v_val_2401_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_val_2401_);
lean_dec_ref_known(v___x_2399_, 1);
v___x_2402_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1));
v___x_2403_ = lean_string_dec_eq(v_val_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2));
v___x_2405_ = lean_string_dec_eq(v_val_2401_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3));
v___x_2407_ = lean_string_dec_eq(v_val_2401_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4));
v___x_2409_ = lean_string_dec_eq(v_val_2401_, v___x_2408_);
lean_dec(v_val_2401_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; 
v___x_2410_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5));
return v___x_2410_;
}
else
{
lean_object* v___x_2411_; 
v___x_2411_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6));
return v___x_2411_;
}
}
else
{
lean_object* v___x_2412_; 
lean_dec(v_val_2401_);
v___x_2412_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7));
return v___x_2412_;
}
}
else
{
lean_object* v___x_2413_; 
lean_dec(v_val_2401_);
v___x_2413_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8));
return v___x_2413_;
}
}
else
{
lean_object* v___x_2414_; 
lean_dec(v_val_2401_);
v___x_2414_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9));
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t v_x_2425_){
_start:
{
switch(v_x_2425_)
{
case 0:
{
lean_object* v___x_2426_; 
v___x_2426_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0));
return v___x_2426_;
}
case 1:
{
lean_object* v___x_2427_; 
v___x_2427_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1));
return v___x_2427_;
}
case 2:
{
lean_object* v___x_2428_; 
v___x_2428_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2));
return v___x_2428_;
}
default: 
{
lean_object* v___x_2429_; 
v___x_2429_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3));
return v___x_2429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object* v_x_2430_){
_start:
{
uint8_t v_x_84__boxed_2431_; lean_object* v_res_2432_; 
v_x_84__boxed_2431_ = lean_unbox(v_x_2430_);
v_res_2432_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_x_84__boxed_2431_);
return v_res_2432_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object* v_x_2435_){
_start:
{
switch(lean_obj_tag(v_x_2435_))
{
case 0:
{
uint8_t v___x_2436_; 
v___x_2436_ = 0;
return v___x_2436_;
}
case 1:
{
uint8_t v___x_2437_; 
v___x_2437_ = 1;
return v___x_2437_;
}
case 2:
{
uint8_t v___x_2438_; 
v___x_2438_ = 2;
return v___x_2438_;
}
default: 
{
uint8_t v___x_2439_; 
v___x_2439_ = 3;
return v___x_2439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object* v_x_2440_){
_start:
{
uint8_t v_res_2441_; lean_object* v_r_2442_; 
v_res_2441_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_x_2440_);
lean_dec_ref(v_x_2440_);
v_r_2442_ = lean_box(v_res_2441_);
return v_r_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(lean_object* v_j_2443_, lean_object* v_k_2444_){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = l_Lean_Json_getObjValD(v_j_2443_, v_k_2444_);
v___x_2446_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0___boxed(lean_object* v_j_2447_, lean_object* v_k_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_j_2447_, v_k_2448_);
lean_dec_ref(v_k_2448_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage(lean_object* v_h_2452_, lean_object* v_nBytes_2453_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_IO_FS_Stream_readJson(v_h_2452_, v_nBytes_2453_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2575_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2575_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2575_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
uint8_t v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v_a_2475_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_a_2456_);
v___x_2487_ = l_Lean_Json_getObjVal_x3f(v_a_2456_, v___x_2486_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; 
lean_del_object(v___x_2458_);
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 1);
v_a_2475_ = v_a_2488_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2489_; 
v_a_2489_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2487_, 1);
if (lean_obj_tag(v_a_2489_) == 3)
{
lean_object* v_s_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v_s_2490_ = lean_ctor_get(v_a_2489_, 0);
lean_inc_ref(v_s_2490_);
lean_dec_ref_known(v_a_2489_, 1);
v___x_2491_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_2492_ = lean_string_dec_eq(v_s_2490_, v___x_2491_);
lean_dec_ref(v_s_2490_);
if (v___x_2492_ == 0)
{
lean_del_object(v___x_2458_);
goto v___jp_2484_;
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_a_2456_);
v___x_2494_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_2456_, v___x_2493_);
if (lean_obj_tag(v___x_2494_) == 0)
{
goto v___jp_2523_;
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v_a_2550_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2550_);
v___x_2551_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2456_);
v___x_2552_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2456_, v___x_2551_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_dec_ref_known(v___x_2552_, 1);
lean_dec(v_a_2550_);
goto v___jp_2523_;
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2574_; 
lean_dec_ref_known(v___x_2494_, 1);
lean_del_object(v___x_2458_);
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2574_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2574_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___y_2558_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2564_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2456_, v___x_2563_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v___x_2565_; 
lean_dec_ref_known(v___x_2564_, 1);
v___x_2565_ = lean_box(0);
v___y_2558_ = v___x_2565_;
goto v___jp_2557_;
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
v_a_2566_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2564_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2564_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
v___y_2558_ = v___x_2571_;
goto v___jp_2557_;
}
}
}
v___jp_2557_:
{
lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2559_, 0, v_a_2550_);
lean_ctor_set(v___x_2559_, 1, v_a_2553_);
lean_ctor_set(v___x_2559_, 2, v___y_2558_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set_tag(v___x_2555_, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2559_);
v___x_2561_ = v___x_2555_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
v___jp_2495_:
{
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2496_; 
lean_del_object(v___x_2458_);
v_a_2496_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2494_, 1);
v_a_2475_ = v_a_2496_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_a_2497_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2494_, 1);
v___x_2498_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
lean_inc(v_a_2456_);
v___x_2499_ = l_Lean_Json_getObjVal_x3f(v_a_2456_, v___x_2498_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; 
lean_dec(v_a_2497_);
lean_del_object(v___x_2458_);
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v_a_2475_ = v_a_2500_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v_a_2501_ = lean_ctor_get(v___x_2499_, 0);
lean_inc_n(v_a_2501_, 2);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2502_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_2503_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_2501_, v___x_2502_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; 
lean_dec(v_a_2501_);
lean_dec(v_a_2497_);
lean_del_object(v___x_2458_);
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
v_a_2475_ = v_a_2504_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_a_2505_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2506_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_2501_);
v___x_2507_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2501_, v___x_2506_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; 
lean_dec(v_a_2505_);
lean_dec(v_a_2501_);
lean_dec(v_a_2497_);
lean_del_object(v___x_2458_);
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v_a_2475_ = v_a_2508_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_dec(v_a_2456_);
v_a_2509_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2507_, 1);
v___x_2510_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2511_ = l_Lean_Json_getObjVal_x3f(v_a_2501_, v___x_2510_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v___x_2512_; uint8_t v___x_2513_; 
lean_dec_ref_known(v___x_2511_, 1);
v___x_2512_ = lean_box(0);
v___x_2513_ = lean_unbox(v_a_2505_);
lean_dec(v_a_2505_);
v___y_2461_ = v___x_2513_;
v___y_2462_ = v_a_2509_;
v___y_2463_ = v_a_2497_;
v___y_2464_ = v___x_2512_;
goto v___jp_2460_;
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2522_; 
v_a_2514_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2516_ = v___x_2511_;
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2511_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_unbox(v_a_2505_);
lean_dec(v_a_2505_);
v___y_2461_ = v___x_2520_;
v___y_2462_ = v_a_2509_;
v___y_2463_ = v_a_2497_;
v___y_2464_ = v___x_2519_;
goto v___jp_2460_;
}
}
}
}
}
}
}
}
v___jp_2523_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2456_);
v___x_2525_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2456_, v___x_2524_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_dec_ref_known(v___x_2525_, 1);
if (lean_obj_tag(v___x_2494_) == 0)
{
goto v___jp_2495_;
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v_a_2526_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2526_);
v___x_2527_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_2456_);
v___x_2528_ = l_Lean_Json_getObjVal_x3f(v_a_2456_, v___x_2527_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_dec_ref_known(v___x_2528_, 1);
lean_dec(v_a_2526_);
goto v___jp_2495_;
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref_known(v___x_2494_, 1);
lean_del_object(v___x_2458_);
lean_dec(v_a_2456_);
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2537_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2533_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2533_, 0, v_a_2526_);
lean_ctor_set(v___x_2533_, 1, v_a_2529_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set_tag(v___x_2531_, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2533_);
v___x_2535_ = v___x_2531_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
lean_dec_ref(v___x_2494_);
lean_del_object(v___x_2458_);
v_a_2538_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2525_, 1);
v___x_2539_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2540_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2456_, v___x_2539_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2541_; 
lean_dec_ref_known(v___x_2540_, 1);
v___x_2541_ = lean_box(0);
v___y_2470_ = v_a_2538_;
v___y_2471_ = v___x_2541_;
goto v___jp_2469_;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
v_a_2542_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2540_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2540_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
v___y_2470_ = v_a_2538_;
v___y_2471_ = v___x_2547_;
goto v___jp_2469_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2489_);
lean_del_object(v___x_2458_);
goto v___jp_2484_;
}
}
v___jp_2460_:
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2465_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2465_, 0, v___y_2463_);
lean_ctor_set(v___x_2465_, 1, v___y_2462_);
lean_ctor_set(v___x_2465_, 2, v___y_2464_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*3, v___y_2461_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2465_);
v___x_2467_ = v___x_2458_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
v___jp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___y_2470_);
lean_ctor_set(v___x_2472_, 1, v___y_2471_);
v___x_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
return v___x_2473_;
}
v___jp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2476_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__0));
v___x_2477_ = l_Lean_Json_compress(v_a_2456_);
v___x_2478_ = lean_string_append(v___x_2476_, v___x_2477_);
lean_dec_ref(v___x_2477_);
v___x_2479_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__1));
v___x_2480_ = lean_string_append(v___x_2478_, v___x_2479_);
v___x_2481_ = lean_string_append(v___x_2480_, v_a_2475_);
lean_dec_ref(v_a_2475_);
v___x_2482_ = lean_mk_io_user_error(v___x_2481_);
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
v___jp_2484_:
{
lean_object* v___x_2485_; 
v___x_2485_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_2475_ = v___x_2485_;
goto v___jp_2474_;
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
v_a_2576_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2455_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2455_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage___boxed(lean_object* v_h_2584_, lean_object* v_nBytes_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_IO_FS_Stream_readMessage(v_h_2584_, v_nBytes_2585_);
lean_dec(v_nBytes_2585_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg(lean_object* v_h_2595_, lean_object* v_nBytes_2596_, lean_object* v_expectedMethod_2597_, lean_object* v_inst_2598_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = l_Lean_IO_FS_Stream_readMessage(v_h_2595_, v_nBytes_2596_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2787_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2603_ = v___x_2600_;
v_isShared_2604_ = v_isSharedCheck_2787_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2600_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2787_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; 
v___x_2605_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
if (lean_obj_tag(v_a_2601_) == 0)
{
lean_object* v_id_2606_; lean_object* v_method_2607_; lean_object* v_params_x3f_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2647_; 
v_id_2606_ = lean_ctor_get(v_a_2601_, 0);
v_method_2607_ = lean_ctor_get(v_a_2601_, 1);
v_params_x3f_2608_ = lean_ctor_get(v_a_2601_, 2);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_a_2601_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2610_ = v_a_2601_;
v_isShared_2611_ = v_isSharedCheck_2647_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_params_x3f_2608_);
lean_inc(v_method_2607_);
lean_inc(v_id_2606_);
lean_dec(v_a_2601_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2647_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
uint8_t v___x_2612_; 
v___x_2612_ = lean_string_dec_eq(v_method_2607_, v_expectedMethod_2597_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2622_; 
lean_del_object(v___x_2610_);
lean_dec(v_params_x3f_2608_);
lean_dec(v_id_2606_);
lean_dec_ref(v_inst_2598_);
v___x_2613_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2614_ = lean_string_append(v___x_2613_, v_expectedMethod_2597_);
lean_dec_ref(v_expectedMethod_2597_);
v___x_2615_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2616_ = lean_string_append(v___x_2614_, v___x_2615_);
v___x_2617_ = lean_string_append(v___x_2616_, v_method_2607_);
lean_dec_ref(v_method_2607_);
v___x_2618_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2619_ = lean_string_append(v___x_2617_, v___x_2618_);
v___x_2620_ = lean_mk_io_user_error(v___x_2619_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2620_);
v___x_2622_ = v___x_2603_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
lean_dec_ref(v_method_2607_);
v___x_2624_ = l_Lean_Option_toJson___redArg(v___x_2605_, v_params_x3f_2608_);
lean_inc(v___x_2624_);
v___x_2625_ = lean_apply_1(v_inst_2598_, v___x_2624_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
lean_del_object(v___x_2610_);
lean_dec(v_id_2606_);
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2628_ = l_Lean_Json_compress(v___x_2624_);
v___x_2629_ = lean_string_append(v___x_2627_, v___x_2628_);
lean_dec_ref(v___x_2628_);
v___x_2630_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2631_ = lean_string_append(v___x_2629_, v___x_2630_);
v___x_2632_ = lean_string_append(v___x_2631_, v_expectedMethod_2597_);
lean_dec_ref(v_expectedMethod_2597_);
v___x_2633_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2634_ = lean_string_append(v___x_2632_, v___x_2633_);
v___x_2635_ = lean_string_append(v___x_2634_, v_a_2626_);
lean_dec(v_a_2626_);
v___x_2636_ = lean_mk_io_user_error(v___x_2635_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2636_);
v___x_2638_ = v___x_2603_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; 
lean_dec(v___x_2624_);
v_a_2640_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2625_, 1);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 2, v_a_2640_);
lean_ctor_set(v___x_2610_, 1, v_expectedMethod_2597_);
v___x_2642_ = v___x_2610_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_id_2606_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_expectedMethod_2597_);
lean_ctor_set(v_reuseFailAlloc_2646_, 2, v_a_2640_);
v___x_2642_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2644_; 
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2642_);
v___x_2644_ = v___x_2603_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___y_2651_; 
lean_dec_ref(v_inst_2598_);
lean_dec_ref(v_expectedMethod_2597_);
v___x_2648_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__6));
v___x_2649_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2601_))
{
case 0:
{
lean_object* v_id_2662_; lean_object* v_method_2663_; lean_object* v_params_x3f_2664_; lean_object* v___x_2665_; lean_object* v___y_2667_; 
v_id_2662_ = lean_ctor_get(v_a_2601_, 0);
lean_inc(v_id_2662_);
v_method_2663_ = lean_ctor_get(v_a_2601_, 1);
lean_inc_ref(v_method_2663_);
v_params_x3f_2664_ = lean_ctor_get(v_a_2601_, 2);
lean_inc(v_params_x3f_2664_);
lean_dec_ref_known(v_a_2601_, 3);
v___x_2665_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2662_) == 0)
{
lean_object* v_s_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_s_2678_ = lean_ctor_get(v_id_2662_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_id_2662_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v_id_2662_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_s_2678_);
lean_dec(v_id_2662_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 3);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_s_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
v___y_2667_ = v___x_2683_;
goto v___jp_2666_;
}
}
}
else
{
lean_object* v_n_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_n_2686_ = lean_ctor_get(v_id_2662_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_id_2662_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v_id_2662_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_n_2686_);
lean_dec(v_id_2662_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set_tag(v___x_2688_, 2);
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_n_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
v___y_2667_ = v___x_2691_;
goto v___jp_2666_;
}
}
}
v___jp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2665_);
lean_ctor_set(v___x_2668_, 1, v___y_2667_);
v___x_2669_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2670_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_method_2663_);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = lean_box(0);
v___x_2673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2668_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2676_ = l_Lean_Json_opt___redArg(v___x_2605_, v___x_2675_, v_params_x3f_2664_);
v___x_2677_ = l_List_appendTR___redArg(v___x_2674_, v___x_2676_);
v___y_2651_ = v___x_2677_;
goto v___jp_2650_;
}
}
case 1:
{
lean_object* v_method_2694_; lean_object* v_params_x3f_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_method_2694_ = lean_ctor_get(v_a_2601_, 0);
lean_inc_ref(v_method_2694_);
v_params_x3f_2695_ = lean_ctor_get(v_a_2601_, 1);
lean_inc(v_params_x3f_2695_);
lean_dec_ref_known(v_a_2601_, 2);
v___x_2696_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2697_, 0, v_method_2694_);
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2700_ = l_Lean_Json_opt___redArg(v___x_2605_, v___x_2699_, v_params_x3f_2695_);
v___x_2701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2698_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___y_2651_ = v___x_2701_;
goto v___jp_2650_;
}
case 2:
{
lean_object* v_id_2702_; lean_object* v_result_2703_; lean_object* v___x_2704_; lean_object* v___y_2706_; 
v_id_2702_ = lean_ctor_get(v_a_2601_, 0);
lean_inc(v_id_2702_);
v_result_2703_ = lean_ctor_get(v_a_2601_, 1);
lean_inc(v_result_2703_);
lean_dec_ref_known(v_a_2601_, 2);
v___x_2704_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2702_) == 0)
{
lean_object* v_s_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_s_2713_ = lean_ctor_get(v_id_2702_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_id_2702_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v_id_2702_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_s_2713_);
lean_dec(v_id_2702_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
lean_ctor_set_tag(v___x_2715_, 3);
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_s_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
v___y_2706_ = v___x_2718_;
goto v___jp_2705_;
}
}
}
else
{
lean_object* v_n_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
v_n_2721_ = lean_ctor_get(v_id_2702_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_id_2702_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v_id_2702_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_n_2721_);
lean_dec(v_id_2702_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
lean_ctor_set_tag(v___x_2723_, 2);
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_n_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
v___y_2706_ = v___x_2726_;
goto v___jp_2705_;
}
}
}
v___jp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2704_);
lean_ctor_set(v___x_2707_, 1, v___y_2706_);
v___x_2708_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v_result_2703_);
v___x_2710_ = lean_box(0);
v___x_2711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2707_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___y_2651_ = v___x_2712_;
goto v___jp_2650_;
}
}
default: 
{
lean_object* v_id_2729_; uint8_t v_code_2730_; lean_object* v_message_2731_; lean_object* v_data_x3f_2732_; lean_object* v___x_2733_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___x_2753_; lean_object* v___y_2755_; 
v_id_2729_ = lean_ctor_get(v_a_2601_, 0);
lean_inc(v_id_2729_);
v_code_2730_ = lean_ctor_get_uint8(v_a_2601_, sizeof(void*)*3);
v_message_2731_ = lean_ctor_get(v_a_2601_, 1);
lean_inc_ref(v_message_2731_);
v_data_x3f_2732_ = lean_ctor_get(v_a_2601_, 2);
lean_inc(v_data_x3f_2732_);
lean_dec_ref_known(v_a_2601_, 3);
v___x_2733_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2753_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2729_) == 0)
{
lean_object* v_s_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
v_s_2771_ = lean_ctor_get(v_id_2729_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_id_2729_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v_id_2729_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_s_2771_);
lean_dec(v_id_2729_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set_tag(v___x_2773_, 3);
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_s_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
v___y_2755_ = v___x_2776_;
goto v___jp_2754_;
}
}
}
else
{
lean_object* v_n_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
v_n_2779_ = lean_ctor_get(v_id_2729_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_id_2729_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v_id_2729_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_n_2779_);
lean_dec(v_id_2729_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set_tag(v___x_2781_, 2);
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_n_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
v___y_2755_ = v___x_2784_;
goto v___jp_2754_;
}
}
}
v___jp_2734_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_inc(v___y_2738_);
lean_inc_ref(v___y_2735_);
v___x_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___y_2735_);
lean_ctor_set(v___x_2739_, 1, v___y_2738_);
v___x_2740_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2741_, 0, v_message_2731_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_box(0);
v___x_2744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2739_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2747_ = l_Lean_Json_opt___redArg(v___x_2733_, v___x_2746_, v_data_x3f_2732_);
v___x_2748_ = l_List_appendTR___redArg(v___x_2745_, v___x_2747_);
v___x_2749_ = l_Lean_Json_mkObj(v___x_2748_);
lean_dec(v___x_2748_);
lean_inc_ref(v___y_2737_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___y_2737_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
lean_ctor_set(v___x_2751_, 1, v___x_2743_);
v___x_2752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___y_2736_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___y_2651_ = v___x_2752_;
goto v___jp_2650_;
}
v___jp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2753_);
lean_ctor_set(v___x_2756_, 1, v___y_2755_);
v___x_2757_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2758_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2730_)
{
case 0:
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2759_;
goto v___jp_2734_;
}
case 1:
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2760_;
goto v___jp_2734_;
}
case 2:
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2761_;
goto v___jp_2734_;
}
case 3:
{
lean_object* v___x_2762_; 
v___x_2762_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2762_;
goto v___jp_2734_;
}
case 4:
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2763_;
goto v___jp_2734_;
}
case 5:
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2764_;
goto v___jp_2734_;
}
case 6:
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2765_;
goto v___jp_2734_;
}
case 7:
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2766_;
goto v___jp_2734_;
}
case 8:
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2767_;
goto v___jp_2734_;
}
case 9:
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2768_;
goto v___jp_2734_;
}
case 10:
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2769_;
goto v___jp_2734_;
}
default: 
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2735_ = v___x_2758_;
v___y_2736_ = v___x_2756_;
v___y_2737_ = v___x_2757_;
v___y_2738_ = v___x_2770_;
goto v___jp_2734_;
}
}
}
}
}
v___jp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2649_);
lean_ctor_set(v___x_2652_, 1, v___y_2651_);
v___x_2653_ = l_Lean_Json_mkObj(v___x_2652_);
lean_dec_ref_known(v___x_2652_, 2);
v___x_2654_ = l_Lean_Json_compress(v___x_2653_);
v___x_2655_ = lean_string_append(v___x_2648_, v___x_2654_);
lean_dec_ref(v___x_2654_);
v___x_2656_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2657_ = lean_string_append(v___x_2655_, v___x_2656_);
v___x_2658_ = lean_mk_io_user_error(v___x_2657_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 1);
lean_ctor_set(v___x_2603_, 0, v___x_2658_);
v___x_2660_ = v___x_2603_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec_ref(v_inst_2598_);
lean_dec_ref(v_expectedMethod_2597_);
v_a_2788_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2600_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2600_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* v_h_2796_, lean_object* v_nBytes_2797_, lean_object* v_expectedMethod_2798_, lean_object* v_inst_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2796_, v_nBytes_2797_, v_expectedMethod_2798_, v_inst_2799_);
lean_dec(v_nBytes_2797_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs(lean_object* v_h_2802_, lean_object* v_nBytes_2803_, lean_object* v_expectedMethod_2804_, lean_object* v_00_u03b1_2805_, lean_object* v_inst_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2802_, v_nBytes_2803_, v_expectedMethod_2804_, v_inst_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___boxed(lean_object* v_h_2809_, lean_object* v_nBytes_2810_, lean_object* v_expectedMethod_2811_, lean_object* v_00_u03b1_2812_, lean_object* v_inst_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_IO_FS_Stream_readRequestAs(v_h_2809_, v_nBytes_2810_, v_expectedMethod_2811_, v_00_u03b1_2812_, v_inst_2813_);
lean_dec(v_nBytes_2810_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg(lean_object* v_h_2817_, lean_object* v_nBytes_2818_, lean_object* v_expectedMethod_2819_, lean_object* v_inst_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_Lean_IO_FS_Stream_readMessage(v_h_2817_, v_nBytes_2818_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_3008_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_3008_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_3008_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; 
v___x_2827_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
if (lean_obj_tag(v_a_2823_) == 1)
{
lean_object* v_method_2828_; lean_object* v_params_x3f_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2868_; 
v_method_2828_ = lean_ctor_get(v_a_2823_, 0);
v_params_x3f_2829_ = lean_ctor_get(v_a_2823_, 1);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_a_2823_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2831_ = v_a_2823_;
v_isShared_2832_ = v_isSharedCheck_2868_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_params_x3f_2829_);
lean_inc(v_method_2828_);
lean_dec(v_a_2823_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2868_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_string_dec_eq(v_method_2828_, v_expectedMethod_2819_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
lean_del_object(v___x_2831_);
lean_dec(v_params_x3f_2829_);
lean_dec_ref(v_inst_2820_);
v___x_2834_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2835_ = lean_string_append(v___x_2834_, v_expectedMethod_2819_);
lean_dec_ref(v_expectedMethod_2819_);
v___x_2836_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2837_ = lean_string_append(v___x_2835_, v___x_2836_);
v___x_2838_ = lean_string_append(v___x_2837_, v_method_2828_);
lean_dec_ref(v_method_2828_);
v___x_2839_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2840_ = lean_string_append(v___x_2838_, v___x_2839_);
v___x_2841_ = lean_mk_io_user_error(v___x_2840_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set_tag(v___x_2825_, 1);
lean_ctor_set(v___x_2825_, 0, v___x_2841_);
v___x_2843_ = v___x_2825_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec_ref(v_method_2828_);
v___x_2845_ = l_Lean_Option_toJson___redArg(v___x_2827_, v_params_x3f_2829_);
lean_inc(v___x_2845_);
v___x_2846_ = lean_apply_1(v_inst_2820_, v___x_2845_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
lean_del_object(v___x_2831_);
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2849_ = l_Lean_Json_compress(v___x_2845_);
v___x_2850_ = lean_string_append(v___x_2848_, v___x_2849_);
lean_dec_ref(v___x_2849_);
v___x_2851_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2852_ = lean_string_append(v___x_2850_, v___x_2851_);
v___x_2853_ = lean_string_append(v___x_2852_, v_expectedMethod_2819_);
lean_dec_ref(v_expectedMethod_2819_);
v___x_2854_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2855_ = lean_string_append(v___x_2853_, v___x_2854_);
v___x_2856_ = lean_string_append(v___x_2855_, v_a_2847_);
lean_dec(v_a_2847_);
v___x_2857_ = lean_mk_io_user_error(v___x_2856_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set_tag(v___x_2825_, 1);
lean_ctor_set(v___x_2825_, 0, v___x_2857_);
v___x_2859_ = v___x_2825_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; 
lean_dec(v___x_2845_);
v_a_2861_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2846_, 1);
if (v_isShared_2832_ == 0)
{
lean_ctor_set_tag(v___x_2831_, 0);
lean_ctor_set(v___x_2831_, 1, v_a_2861_);
lean_ctor_set(v___x_2831_, 0, v_expectedMethod_2819_);
v___x_2863_ = v___x_2831_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_expectedMethod_2819_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_a_2861_);
v___x_2863_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2865_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___x_2863_);
v___x_2865_ = v___x_2825_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___y_2872_; 
lean_dec_ref(v_inst_2820_);
lean_dec_ref(v_expectedMethod_2819_);
v___x_2869_ = ((lean_object*)(l_Lean_IO_FS_Stream_readNotificationAs___redArg___closed__0));
v___x_2870_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2823_))
{
case 0:
{
lean_object* v_id_2883_; lean_object* v_method_2884_; lean_object* v_params_x3f_2885_; lean_object* v___x_2886_; lean_object* v___y_2888_; 
v_id_2883_ = lean_ctor_get(v_a_2823_, 0);
lean_inc(v_id_2883_);
v_method_2884_ = lean_ctor_get(v_a_2823_, 1);
lean_inc_ref(v_method_2884_);
v_params_x3f_2885_ = lean_ctor_get(v_a_2823_, 2);
lean_inc(v_params_x3f_2885_);
lean_dec_ref_known(v_a_2823_, 3);
v___x_2886_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2883_) == 0)
{
lean_object* v_s_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
v_s_2899_ = lean_ctor_get(v_id_2883_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_id_2883_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v_id_2883_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_s_2899_);
lean_dec(v_id_2883_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
lean_ctor_set_tag(v___x_2901_, 3);
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_s_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
v___y_2888_ = v___x_2904_;
goto v___jp_2887_;
}
}
}
else
{
lean_object* v_n_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
v_n_2907_ = lean_ctor_get(v_id_2883_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_id_2883_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v_id_2883_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_n_2907_);
lean_dec(v_id_2883_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set_tag(v___x_2909_, 2);
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_n_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
v___y_2888_ = v___x_2912_;
goto v___jp_2887_;
}
}
}
v___jp_2887_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2886_);
lean_ctor_set(v___x_2889_, 1, v___y_2888_);
v___x_2890_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2891_, 0, v_method_2884_);
v___x_2892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = lean_box(0);
v___x_2894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2889_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2897_ = l_Lean_Json_opt___redArg(v___x_2827_, v___x_2896_, v_params_x3f_2885_);
v___x_2898_ = l_List_appendTR___redArg(v___x_2895_, v___x_2897_);
v___y_2872_ = v___x_2898_;
goto v___jp_2871_;
}
}
case 1:
{
lean_object* v_method_2915_; lean_object* v_params_x3f_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v_method_2915_ = lean_ctor_get(v_a_2823_, 0);
lean_inc_ref(v_method_2915_);
v_params_x3f_2916_ = lean_ctor_get(v_a_2823_, 1);
lean_inc(v_params_x3f_2916_);
lean_dec_ref_known(v_a_2823_, 2);
v___x_2917_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2918_, 0, v_method_2915_);
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2917_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2921_ = l_Lean_Json_opt___redArg(v___x_2827_, v___x_2920_, v_params_x3f_2916_);
v___x_2922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2919_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___y_2872_ = v___x_2922_;
goto v___jp_2871_;
}
case 2:
{
lean_object* v_id_2923_; lean_object* v_result_2924_; lean_object* v___x_2925_; lean_object* v___y_2927_; 
v_id_2923_ = lean_ctor_get(v_a_2823_, 0);
lean_inc(v_id_2923_);
v_result_2924_ = lean_ctor_get(v_a_2823_, 1);
lean_inc(v_result_2924_);
lean_dec_ref_known(v_a_2823_, 2);
v___x_2925_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2923_) == 0)
{
lean_object* v_s_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
v_s_2934_ = lean_ctor_get(v_id_2923_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_id_2923_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v_id_2923_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_s_2934_);
lean_dec(v_id_2923_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
lean_ctor_set_tag(v___x_2936_, 3);
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_s_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
v___y_2927_ = v___x_2939_;
goto v___jp_2926_;
}
}
}
else
{
lean_object* v_n_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
v_n_2942_ = lean_ctor_get(v_id_2923_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_id_2923_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v_id_2923_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_n_2942_);
lean_dec(v_id_2923_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set_tag(v___x_2944_, 2);
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_n_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
v___y_2927_ = v___x_2947_;
goto v___jp_2926_;
}
}
}
v___jp_2926_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2925_);
lean_ctor_set(v___x_2928_, 1, v___y_2927_);
v___x_2929_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
lean_ctor_set(v___x_2930_, 1, v_result_2924_);
v___x_2931_ = lean_box(0);
v___x_2932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2930_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___x_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2928_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___y_2872_ = v___x_2933_;
goto v___jp_2871_;
}
}
default: 
{
lean_object* v_id_2950_; uint8_t v_code_2951_; lean_object* v_message_2952_; lean_object* v_data_x3f_2953_; lean_object* v___x_2954_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___x_2974_; lean_object* v___y_2976_; 
v_id_2950_ = lean_ctor_get(v_a_2823_, 0);
lean_inc(v_id_2950_);
v_code_2951_ = lean_ctor_get_uint8(v_a_2823_, sizeof(void*)*3);
v_message_2952_ = lean_ctor_get(v_a_2823_, 1);
lean_inc_ref(v_message_2952_);
v_data_x3f_2953_ = lean_ctor_get(v_a_2823_, 2);
lean_inc(v_data_x3f_2953_);
lean_dec_ref_known(v_a_2823_, 3);
v___x_2954_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2974_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2950_) == 0)
{
lean_object* v_s_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
v_s_2992_ = lean_ctor_get(v_id_2950_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_id_2950_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v_id_2950_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_s_2992_);
lean_dec(v_id_2950_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
lean_ctor_set_tag(v___x_2994_, 3);
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_s_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
v___y_2976_ = v___x_2997_;
goto v___jp_2975_;
}
}
}
else
{
lean_object* v_n_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
v_n_3000_ = lean_ctor_get(v_id_2950_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_id_2950_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v_id_2950_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_n_3000_);
lean_dec(v_id_2950_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set_tag(v___x_3002_, 2);
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_n_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
v___y_2976_ = v___x_3005_;
goto v___jp_2975_;
}
}
}
v___jp_2955_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
v___x_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___y_2958_);
lean_ctor_set(v___x_2960_, 1, v___y_2959_);
v___x_2961_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2962_, 0, v_message_2952_);
v___x_2963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = lean_box(0);
v___x_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2960_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2968_ = l_Lean_Json_opt___redArg(v___x_2954_, v___x_2967_, v_data_x3f_2953_);
v___x_2969_ = l_List_appendTR___redArg(v___x_2966_, v___x_2968_);
v___x_2970_ = l_Lean_Json_mkObj(v___x_2969_);
lean_dec(v___x_2969_);
lean_inc_ref(v___y_2956_);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___y_2956_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
lean_ctor_set(v___x_2972_, 1, v___x_2964_);
v___x_2973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___y_2957_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___y_2872_ = v___x_2973_;
goto v___jp_2871_;
}
v___jp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2974_);
lean_ctor_set(v___x_2977_, 1, v___y_2976_);
v___x_2978_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2979_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2951_)
{
case 0:
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2980_;
goto v___jp_2955_;
}
case 1:
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2981_;
goto v___jp_2955_;
}
case 2:
{
lean_object* v___x_2982_; 
v___x_2982_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2982_;
goto v___jp_2955_;
}
case 3:
{
lean_object* v___x_2983_; 
v___x_2983_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2983_;
goto v___jp_2955_;
}
case 4:
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2984_;
goto v___jp_2955_;
}
case 5:
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2985_;
goto v___jp_2955_;
}
case 6:
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2986_;
goto v___jp_2955_;
}
case 7:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2987_;
goto v___jp_2955_;
}
case 8:
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2988_;
goto v___jp_2955_;
}
case 9:
{
lean_object* v___x_2989_; 
v___x_2989_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2989_;
goto v___jp_2955_;
}
case 10:
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2990_;
goto v___jp_2955_;
}
default: 
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2956_ = v___x_2978_;
v___y_2957_ = v___x_2977_;
v___y_2958_ = v___x_2979_;
v___y_2959_ = v___x_2991_;
goto v___jp_2955_;
}
}
}
}
}
v___jp_2871_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2870_);
lean_ctor_set(v___x_2873_, 1, v___y_2872_);
v___x_2874_ = l_Lean_Json_mkObj(v___x_2873_);
lean_dec_ref_known(v___x_2873_, 2);
v___x_2875_ = l_Lean_Json_compress(v___x_2874_);
v___x_2876_ = lean_string_append(v___x_2869_, v___x_2875_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2878_ = lean_string_append(v___x_2876_, v___x_2877_);
v___x_2879_ = lean_mk_io_user_error(v___x_2878_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set_tag(v___x_2825_, 1);
lean_ctor_set(v___x_2825_, 0, v___x_2879_);
v___x_2881_ = v___x_2825_;
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
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref(v_inst_2820_);
lean_dec_ref(v_expectedMethod_2819_);
v_a_3009_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2822_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2822_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* v_h_3017_, lean_object* v_nBytes_3018_, lean_object* v_expectedMethod_3019_, lean_object* v_inst_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3017_, v_nBytes_3018_, v_expectedMethod_3019_, v_inst_3020_);
lean_dec(v_nBytes_3018_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs(lean_object* v_h_3023_, lean_object* v_nBytes_3024_, lean_object* v_expectedMethod_3025_, lean_object* v_00_u03b1_3026_, lean_object* v_inst_3027_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3023_, v_nBytes_3024_, v_expectedMethod_3025_, v_inst_3027_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___boxed(lean_object* v_h_3030_, lean_object* v_nBytes_3031_, lean_object* v_expectedMethod_3032_, lean_object* v_00_u03b1_3033_, lean_object* v_inst_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lean_IO_FS_Stream_readNotificationAs(v_h_3030_, v_nBytes_3031_, v_expectedMethod_3032_, v_00_u03b1_3033_, v_inst_3034_);
lean_dec(v_nBytes_3031_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg(lean_object* v_h_3041_, lean_object* v_nBytes_3042_, lean_object* v_expectedID_3043_, lean_object* v_inst_3044_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_IO_FS_Stream_readMessage(v_h_3041_, v_nBytes_3042_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3250_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3049_ = v___x_3046_;
v_isShared_3050_ = v_isSharedCheck_3250_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3046_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3250_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___y_3052_; lean_object* v___y_3053_; 
if (lean_obj_tag(v_a_3047_) == 2)
{
lean_object* v_id_3059_; lean_object* v_result_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3111_; 
v_id_3059_ = lean_ctor_get(v_a_3047_, 0);
v_result_3060_ = lean_ctor_get(v_a_3047_, 1);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_a_3047_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3062_ = v_a_3047_;
v_isShared_3063_ = v_isSharedCheck_3111_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_result_3060_);
lean_inc(v_id_3059_);
lean_dec(v_a_3047_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3111_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
uint8_t v___x_3064_; 
v___x_3064_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3059_, v_expectedID_3043_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; lean_object* v___y_3067_; 
lean_del_object(v___x_3062_);
lean_dec(v_result_3060_);
lean_dec_ref(v_inst_3044_);
v___x_3065_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__0));
switch(lean_obj_tag(v_expectedID_3043_))
{
case 0:
{
lean_object* v_s_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_s_3077_ = lean_ctor_get(v_expectedID_3043_, 0);
lean_inc_ref(v_s_3077_);
lean_dec_ref_known(v_expectedID_3043_, 1);
v___x_3078_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3079_ = lean_string_append(v___x_3078_, v_s_3077_);
lean_dec_ref(v_s_3077_);
v___x_3080_ = lean_string_append(v___x_3079_, v___x_3078_);
v___y_3067_ = v___x_3080_;
goto v___jp_3066_;
}
case 1:
{
lean_object* v_n_3081_; lean_object* v___x_3082_; 
v_n_3081_ = lean_ctor_get(v_expectedID_3043_, 0);
lean_inc_ref(v_n_3081_);
lean_dec_ref_known(v_expectedID_3043_, 1);
v___x_3082_ = l_Lean_JsonNumber_toString(v_n_3081_);
v___y_3067_ = v___x_3082_;
goto v___jp_3066_;
}
default: 
{
lean_object* v___x_3083_; 
v___x_3083_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___y_3067_ = v___x_3083_;
goto v___jp_3066_;
}
}
v___jp_3066_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = lean_string_append(v___x_3065_, v___y_3067_);
lean_dec_ref(v___y_3067_);
v___x_3069_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__1));
v___x_3070_ = lean_string_append(v___x_3068_, v___x_3069_);
if (lean_obj_tag(v_id_3059_) == 0)
{
lean_object* v_s_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v_s_3071_ = lean_ctor_get(v_id_3059_, 0);
lean_inc_ref(v_s_3071_);
lean_dec_ref_known(v_id_3059_, 1);
v___x_3072_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3073_ = lean_string_append(v___x_3072_, v_s_3071_);
lean_dec_ref(v_s_3071_);
v___x_3074_ = lean_string_append(v___x_3073_, v___x_3072_);
v___y_3052_ = v___x_3070_;
v___y_3053_ = v___x_3074_;
goto v___jp_3051_;
}
else
{
lean_object* v_n_3075_; lean_object* v___x_3076_; 
v_n_3075_ = lean_ctor_get(v_id_3059_, 0);
lean_inc_ref(v_n_3075_);
lean_dec_ref_known(v_id_3059_, 1);
v___x_3076_ = l_Lean_JsonNumber_toString(v_n_3075_);
v___y_3052_ = v___x_3070_;
v___y_3053_ = v___x_3076_;
goto v___jp_3051_;
}
}
}
else
{
lean_object* v___x_3084_; 
lean_dec(v_id_3059_);
lean_del_object(v___x_3049_);
lean_inc(v_result_3060_);
v___x_3084_ = lean_apply_1(v_inst_3044_, v_result_3060_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3099_; 
lean_del_object(v___x_3062_);
lean_dec(v_expectedID_3043_);
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3099_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3099_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3089_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__2));
v___x_3090_ = l_Lean_Json_compress(v_result_3060_);
v___x_3091_ = lean_string_append(v___x_3089_, v___x_3090_);
lean_dec_ref(v___x_3090_);
v___x_3092_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_3093_ = lean_string_append(v___x_3091_, v___x_3092_);
v___x_3094_ = lean_string_append(v___x_3093_, v_a_3085_);
lean_dec(v_a_3085_);
v___x_3095_ = lean_mk_io_user_error(v___x_3094_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set_tag(v___x_3087_, 1);
lean_ctor_set(v___x_3087_, 0, v___x_3095_);
v___x_3097_ = v___x_3087_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3110_; 
lean_dec(v_result_3060_);
v_a_3100_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3102_ = v___x_3084_;
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3084_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3110_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set_tag(v___x_3062_, 0);
lean_ctor_set(v___x_3062_, 1, v_a_3100_);
lean_ctor_set(v___x_3062_, 0, v_expectedID_3043_);
v___x_3105_ = v___x_3062_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_expectedID_3043_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3107_; 
if (v_isShared_3103_ == 0)
{
lean_ctor_set_tag(v___x_3102_, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3105_);
v___x_3107_ = v___x_3102_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___y_3116_; 
lean_del_object(v___x_3049_);
lean_dec_ref(v_inst_3044_);
lean_dec(v_expectedID_3043_);
v___x_3112_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__3));
v___x_3113_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_3114_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_3047_))
{
case 0:
{
lean_object* v_id_3125_; lean_object* v_method_3126_; lean_object* v_params_x3f_3127_; lean_object* v___x_3128_; lean_object* v___y_3130_; 
v_id_3125_ = lean_ctor_get(v_a_3047_, 0);
lean_inc(v_id_3125_);
v_method_3126_ = lean_ctor_get(v_a_3047_, 1);
lean_inc_ref(v_method_3126_);
v_params_x3f_3127_ = lean_ctor_get(v_a_3047_, 2);
lean_inc(v_params_x3f_3127_);
lean_dec_ref_known(v_a_3047_, 3);
v___x_3128_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3125_) == 0)
{
lean_object* v_s_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
v_s_3141_ = lean_ctor_get(v_id_3125_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_id_3125_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v_id_3125_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_s_3141_);
lean_dec(v_id_3125_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
lean_ctor_set_tag(v___x_3143_, 3);
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_s_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
v___y_3130_ = v___x_3146_;
goto v___jp_3129_;
}
}
}
else
{
lean_object* v_n_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
v_n_3149_ = lean_ctor_get(v_id_3125_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_id_3125_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v_id_3125_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_n_3149_);
lean_dec(v_id_3125_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
lean_ctor_set_tag(v___x_3151_, 2);
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_n_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
v___y_3130_ = v___x_3154_;
goto v___jp_3129_;
}
}
}
v___jp_3129_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3128_);
lean_ctor_set(v___x_3131_, 1, v___y_3130_);
v___x_3132_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3133_, 0, v_method_3126_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = lean_box(0);
v___x_3136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3131_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3139_ = l_Lean_Json_opt___redArg(v___x_3113_, v___x_3138_, v_params_x3f_3127_);
v___x_3140_ = l_List_appendTR___redArg(v___x_3137_, v___x_3139_);
v___y_3116_ = v___x_3140_;
goto v___jp_3115_;
}
}
case 1:
{
lean_object* v_method_3157_; lean_object* v_params_x3f_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_method_3157_ = lean_ctor_get(v_a_3047_, 0);
lean_inc_ref(v_method_3157_);
v_params_x3f_3158_ = lean_ctor_get(v_a_3047_, 1);
lean_inc(v_params_x3f_3158_);
lean_dec_ref_known(v_a_3047_, 2);
v___x_3159_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3160_, 0, v_method_3157_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3163_ = l_Lean_Json_opt___redArg(v___x_3113_, v___x_3162_, v_params_x3f_3158_);
v___x_3164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3161_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___y_3116_ = v___x_3164_;
goto v___jp_3115_;
}
case 2:
{
lean_object* v_id_3165_; lean_object* v_result_3166_; lean_object* v___x_3167_; lean_object* v___y_3169_; 
v_id_3165_ = lean_ctor_get(v_a_3047_, 0);
lean_inc(v_id_3165_);
v_result_3166_ = lean_ctor_get(v_a_3047_, 1);
lean_inc(v_result_3166_);
lean_dec_ref_known(v_a_3047_, 2);
v___x_3167_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3165_) == 0)
{
lean_object* v_s_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
v_s_3176_ = lean_ctor_get(v_id_3165_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_id_3165_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v_id_3165_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_s_3176_);
lean_dec(v_id_3165_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
lean_ctor_set_tag(v___x_3178_, 3);
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_s_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
v___y_3169_ = v___x_3181_;
goto v___jp_3168_;
}
}
}
else
{
lean_object* v_n_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
v_n_3184_ = lean_ctor_get(v_id_3165_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_id_3165_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v_id_3165_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_n_3184_);
lean_dec(v_id_3165_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
lean_ctor_set_tag(v___x_3186_, 2);
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_n_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
v___y_3169_ = v___x_3189_;
goto v___jp_3168_;
}
}
}
v___jp_3168_:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3167_);
lean_ctor_set(v___x_3170_, 1, v___y_3169_);
v___x_3171_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
lean_ctor_set(v___x_3172_, 1, v_result_3166_);
v___x_3173_ = lean_box(0);
v___x_3174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3172_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3170_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___y_3116_ = v___x_3175_;
goto v___jp_3115_;
}
}
default: 
{
lean_object* v_id_3192_; uint8_t v_code_3193_; lean_object* v_message_3194_; lean_object* v_data_x3f_3195_; lean_object* v___x_3196_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___x_3216_; lean_object* v___y_3218_; 
v_id_3192_ = lean_ctor_get(v_a_3047_, 0);
lean_inc(v_id_3192_);
v_code_3193_ = lean_ctor_get_uint8(v_a_3047_, sizeof(void*)*3);
v_message_3194_ = lean_ctor_get(v_a_3047_, 1);
lean_inc_ref(v_message_3194_);
v_data_x3f_3195_ = lean_ctor_get(v_a_3047_, 2);
lean_inc(v_data_x3f_3195_);
lean_dec_ref_known(v_a_3047_, 3);
v___x_3196_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_3216_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3192_) == 0)
{
lean_object* v_s_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
v_s_3234_ = lean_ctor_get(v_id_3192_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_id_3192_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v_id_3192_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_s_3234_);
lean_dec(v_id_3192_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
lean_ctor_set_tag(v___x_3236_, 3);
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_s_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
v___y_3218_ = v___x_3239_;
goto v___jp_3217_;
}
}
}
else
{
lean_object* v_n_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
v_n_3242_ = lean_ctor_get(v_id_3192_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_id_3192_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v_id_3192_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_n_3242_);
lean_dec(v_id_3192_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
lean_ctor_set_tag(v___x_3244_, 2);
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_n_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
v___y_3218_ = v___x_3247_;
goto v___jp_3217_;
}
}
}
v___jp_3197_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_inc(v___y_3201_);
lean_inc_ref(v___y_3198_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___y_3198_);
lean_ctor_set(v___x_3202_, 1, v___y_3201_);
v___x_3203_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3204_, 0, v_message_3194_);
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3203_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = lean_box(0);
v___x_3207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3205_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3202_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3210_ = l_Lean_Json_opt___redArg(v___x_3196_, v___x_3209_, v_data_x3f_3195_);
v___x_3211_ = l_List_appendTR___redArg(v___x_3208_, v___x_3210_);
v___x_3212_ = l_Lean_Json_mkObj(v___x_3211_);
lean_dec(v___x_3211_);
lean_inc_ref(v___y_3200_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___y_3200_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
lean_ctor_set(v___x_3214_, 1, v___x_3206_);
v___x_3215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___y_3199_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___y_3116_ = v___x_3215_;
goto v___jp_3115_;
}
v___jp_3217_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3216_);
lean_ctor_set(v___x_3219_, 1, v___y_3218_);
v___x_3220_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3221_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3193_)
{
case 0:
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3222_;
goto v___jp_3197_;
}
case 1:
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3223_;
goto v___jp_3197_;
}
case 2:
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3224_;
goto v___jp_3197_;
}
case 3:
{
lean_object* v___x_3225_; 
v___x_3225_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3225_;
goto v___jp_3197_;
}
case 4:
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3226_;
goto v___jp_3197_;
}
case 5:
{
lean_object* v___x_3227_; 
v___x_3227_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3227_;
goto v___jp_3197_;
}
case 6:
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3228_;
goto v___jp_3197_;
}
case 7:
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3229_;
goto v___jp_3197_;
}
case 8:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3230_;
goto v___jp_3197_;
}
case 9:
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3231_;
goto v___jp_3197_;
}
case 10:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3232_;
goto v___jp_3197_;
}
default: 
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3198_ = v___x_3221_;
v___y_3199_ = v___x_3219_;
v___y_3200_ = v___x_3220_;
v___y_3201_ = v___x_3233_;
goto v___jp_3197_;
}
}
}
}
}
v___jp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3114_);
lean_ctor_set(v___x_3117_, 1, v___y_3116_);
v___x_3118_ = l_Lean_Json_mkObj(v___x_3117_);
lean_dec_ref_known(v___x_3117_, 2);
v___x_3119_ = l_Lean_Json_compress(v___x_3118_);
v___x_3120_ = lean_string_append(v___x_3112_, v___x_3119_);
lean_dec_ref(v___x_3119_);
v___x_3121_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_3122_ = lean_string_append(v___x_3120_, v___x_3121_);
v___x_3123_ = lean_mk_io_user_error(v___x_3122_);
v___x_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
return v___x_3124_;
}
}
v___jp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v___x_3054_ = lean_string_append(v___y_3052_, v___y_3053_);
lean_dec_ref(v___y_3053_);
v___x_3055_ = lean_mk_io_user_error(v___x_3054_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set_tag(v___x_3049_, 1);
lean_ctor_set(v___x_3049_, 0, v___x_3055_);
v___x_3057_ = v___x_3049_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec_ref(v_inst_3044_);
lean_dec(v_expectedID_3043_);
v_a_3251_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3046_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3046_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* v_h_3259_, lean_object* v_nBytes_3260_, lean_object* v_expectedID_3261_, lean_object* v_inst_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3259_, v_nBytes_3260_, v_expectedID_3261_, v_inst_3262_);
lean_dec(v_nBytes_3260_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs(lean_object* v_h_3265_, lean_object* v_nBytes_3266_, lean_object* v_expectedID_3267_, lean_object* v_00_u03b1_3268_, lean_object* v_inst_3269_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3265_, v_nBytes_3266_, v_expectedID_3267_, v_inst_3269_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___boxed(lean_object* v_h_3272_, lean_object* v_nBytes_3273_, lean_object* v_expectedID_3274_, lean_object* v_00_u03b1_3275_, lean_object* v_inst_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_IO_FS_Stream_readResponseAs(v_h_3272_, v_nBytes_3273_, v_expectedID_3274_, v_00_u03b1_3275_, v_inst_3276_);
lean_dec(v_nBytes_3273_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(lean_object* v_k_3279_, lean_object* v_x_3280_){
_start:
{
if (lean_obj_tag(v_x_3280_) == 0)
{
lean_object* v___x_3281_; 
lean_dec_ref(v_k_3279_);
v___x_3281_ = lean_box(0);
return v___x_3281_;
}
else
{
lean_object* v_val_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_val_3282_ = lean_ctor_get(v_x_3280_, 0);
lean_inc(v_val_3282_);
lean_dec_ref_known(v_x_3280_, 1);
v___x_3283_ = l_Lean_Json_Structured_toJson(v_val_3282_);
v___x_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3284_, 0, v_k_3279_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = lean_box(0);
v___x_3286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
return v___x_3286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(lean_object* v_k_3287_, lean_object* v_x_3288_){
_start:
{
if (lean_obj_tag(v_x_3288_) == 0)
{
lean_object* v___x_3289_; 
lean_dec_ref(v_k_3287_);
v___x_3289_ = lean_box(0);
return v___x_3289_;
}
else
{
lean_object* v_val_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_val_3290_ = lean_ctor_get(v_x_3288_, 0);
lean_inc(v_val_3290_);
v___x_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3291_, 0, v_k_3287_);
lean_ctor_set(v___x_3291_, 1, v_val_3290_);
v___x_3292_ = lean_box(0);
v___x_3293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* v_k_3294_, lean_object* v_x_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v_k_3294_, v_x_3295_);
lean_dec(v_x_3295_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage(lean_object* v_h_3297_, lean_object* v_m_3298_){
_start:
{
lean_object* v___x_3300_; lean_object* v___y_3302_; 
v___x_3300_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_3298_))
{
case 0:
{
lean_object* v_id_3306_; lean_object* v_method_3307_; lean_object* v_params_x3f_3308_; lean_object* v___x_3309_; lean_object* v___y_3311_; 
v_id_3306_ = lean_ctor_get(v_m_3298_, 0);
lean_inc(v_id_3306_);
v_method_3307_ = lean_ctor_get(v_m_3298_, 1);
lean_inc_ref(v_method_3307_);
v_params_x3f_3308_ = lean_ctor_get(v_m_3298_, 2);
lean_inc(v_params_x3f_3308_);
lean_dec_ref_known(v_m_3298_, 3);
v___x_3309_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3306_))
{
case 0:
{
lean_object* v_s_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
v_s_3322_ = lean_ctor_get(v_id_3306_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_id_3306_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v_id_3306_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_s_3322_);
lean_dec(v_id_3306_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
lean_ctor_set_tag(v___x_3324_, 3);
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_s_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
v___y_3311_ = v___x_3327_;
goto v___jp_3310_;
}
}
}
case 1:
{
lean_object* v_n_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
v_n_3330_ = lean_ctor_get(v_id_3306_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_id_3306_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v_id_3306_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_n_3330_);
lean_dec(v_id_3306_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set_tag(v___x_3332_, 2);
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_n_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
v___y_3311_ = v___x_3335_;
goto v___jp_3310_;
}
}
}
default: 
{
lean_object* v___x_3338_; 
v___x_3338_ = lean_box(0);
v___y_3311_ = v___x_3338_;
goto v___jp_3310_;
}
}
v___jp_3310_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3309_);
lean_ctor_set(v___x_3312_, 1, v___y_3311_);
v___x_3313_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3314_, 0, v_method_3307_);
v___x_3315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = lean_box(0);
v___x_3317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
v___x_3318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3312_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3320_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3319_, v_params_x3f_3308_);
v___x_3321_ = l_List_appendTR___redArg(v___x_3318_, v___x_3320_);
v___y_3302_ = v___x_3321_;
goto v___jp_3301_;
}
}
case 1:
{
lean_object* v_method_3339_; lean_object* v_params_x3f_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3352_; 
v_method_3339_ = lean_ctor_get(v_m_3298_, 0);
v_params_x3f_3340_ = lean_ctor_get(v_m_3298_, 1);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_m_3298_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3342_ = v_m_3298_;
v_isShared_3343_ = v_isSharedCheck_3352_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_params_x3f_3340_);
lean_inc(v_method_3339_);
lean_dec(v_m_3298_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3352_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3347_; 
v___x_3344_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3345_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3345_, 0, v_method_3339_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set_tag(v___x_3342_, 0);
lean_ctor_set(v___x_3342_, 1, v___x_3345_);
lean_ctor_set(v___x_3342_, 0, v___x_3344_);
v___x_3347_ = v___x_3342_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3344_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3349_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3348_, v_params_x3f_3340_);
v___x_3350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3347_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___y_3302_ = v___x_3350_;
goto v___jp_3301_;
}
}
}
case 2:
{
lean_object* v_id_3353_; lean_object* v_result_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3386_; 
v_id_3353_ = lean_ctor_get(v_m_3298_, 0);
v_result_3354_ = lean_ctor_get(v_m_3298_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_m_3298_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3356_ = v_m_3298_;
v_isShared_3357_ = v_isSharedCheck_3386_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_result_3354_);
lean_inc(v_id_3353_);
lean_dec(v_m_3298_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3386_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3358_; lean_object* v___y_3360_; 
v___x_3358_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3353_))
{
case 0:
{
lean_object* v_s_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
v_s_3369_ = lean_ctor_get(v_id_3353_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v_id_3353_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v_id_3353_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_s_3369_);
lean_dec(v_id_3353_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
lean_ctor_set_tag(v___x_3371_, 3);
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_s_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
v___y_3360_ = v___x_3374_;
goto v___jp_3359_;
}
}
}
case 1:
{
lean_object* v_n_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
v_n_3377_ = lean_ctor_get(v_id_3353_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_id_3353_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v_id_3353_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_n_3377_);
lean_dec(v_id_3353_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set_tag(v___x_3379_, 2);
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_n_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
v___y_3360_ = v___x_3382_;
goto v___jp_3359_;
}
}
}
default: 
{
lean_object* v___x_3385_; 
v___x_3385_ = lean_box(0);
v___y_3360_ = v___x_3385_;
goto v___jp_3359_;
}
}
v___jp_3359_:
{
lean_object* v___x_3362_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set_tag(v___x_3356_, 0);
lean_ctor_set(v___x_3356_, 1, v___y_3360_);
lean_ctor_set(v___x_3356_, 0, v___x_3358_);
v___x_3362_ = v___x_3356_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v___y_3360_);
v___x_3362_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3363_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v_result_3354_);
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3364_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3362_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___y_3302_ = v___x_3367_;
goto v___jp_3301_;
}
}
}
}
default: 
{
lean_object* v_id_3387_; uint8_t v_code_3388_; lean_object* v_message_3389_; lean_object* v_data_x3f_3390_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___x_3410_; lean_object* v___y_3412_; 
v_id_3387_ = lean_ctor_get(v_m_3298_, 0);
lean_inc(v_id_3387_);
v_code_3388_ = lean_ctor_get_uint8(v_m_3298_, sizeof(void*)*3);
v_message_3389_ = lean_ctor_get(v_m_3298_, 1);
lean_inc_ref(v_message_3389_);
v_data_x3f_3390_ = lean_ctor_get(v_m_3298_, 2);
lean_inc(v_data_x3f_3390_);
lean_dec_ref_known(v_m_3298_, 3);
v___x_3410_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3387_))
{
case 0:
{
lean_object* v_s_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
v_s_3428_ = lean_ctor_get(v_id_3387_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_id_3387_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v_id_3387_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_s_3428_);
lean_dec(v_id_3387_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set_tag(v___x_3430_, 3);
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_s_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
v___y_3412_ = v___x_3433_;
goto v___jp_3411_;
}
}
}
case 1:
{
lean_object* v_n_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
v_n_3436_ = lean_ctor_get(v_id_3387_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_id_3387_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v_id_3387_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_n_3436_);
lean_dec(v_id_3387_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set_tag(v___x_3438_, 2);
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_n_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
v___y_3412_ = v___x_3441_;
goto v___jp_3411_;
}
}
}
default: 
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_box(0);
v___y_3412_ = v___x_3444_;
goto v___jp_3411_;
}
}
v___jp_3391_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
lean_inc(v___y_3395_);
lean_inc_ref(v___y_3392_);
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___y_3392_);
lean_ctor_set(v___x_3396_, 1, v___y_3395_);
v___x_3397_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3398_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3398_, 0, v_message_3389_);
v___x_3399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = lean_box(0);
v___x_3401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3396_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3404_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v___x_3403_, v_data_x3f_3390_);
lean_dec(v_data_x3f_3390_);
v___x_3405_ = l_List_appendTR___redArg(v___x_3402_, v___x_3404_);
v___x_3406_ = l_Lean_Json_mkObj(v___x_3405_);
lean_dec(v___x_3405_);
lean_inc_ref(v___y_3394_);
v___x_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___y_3394_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v___x_3400_);
v___x_3409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___y_3393_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___y_3302_ = v___x_3409_;
goto v___jp_3301_;
}
v___jp_3411_:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3410_);
lean_ctor_set(v___x_3413_, 1, v___y_3412_);
v___x_3414_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3415_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3388_)
{
case 0:
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3416_;
goto v___jp_3391_;
}
case 1:
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3417_;
goto v___jp_3391_;
}
case 2:
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3418_;
goto v___jp_3391_;
}
case 3:
{
lean_object* v___x_3419_; 
v___x_3419_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3419_;
goto v___jp_3391_;
}
case 4:
{
lean_object* v___x_3420_; 
v___x_3420_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3420_;
goto v___jp_3391_;
}
case 5:
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3421_;
goto v___jp_3391_;
}
case 6:
{
lean_object* v___x_3422_; 
v___x_3422_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3422_;
goto v___jp_3391_;
}
case 7:
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3423_;
goto v___jp_3391_;
}
case 8:
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3424_;
goto v___jp_3391_;
}
case 9:
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3425_;
goto v___jp_3391_;
}
case 10:
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3426_;
goto v___jp_3391_;
}
default: 
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3392_ = v___x_3415_;
v___y_3393_ = v___x_3413_;
v___y_3394_ = v___x_3414_;
v___y_3395_ = v___x_3427_;
goto v___jp_3391_;
}
}
}
}
}
v___jp_3301_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3300_);
lean_ctor_set(v___x_3303_, 1, v___y_3302_);
v___x_3304_ = l_Lean_Json_mkObj(v___x_3303_);
lean_dec_ref_known(v___x_3303_, 2);
v___x_3305_ = l_Lean_IO_FS_Stream_writeJson(v_h_3297_, v___x_3304_);
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage___boxed(lean_object* v_h_3445_, lean_object* v_m_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3445_, v_m_3446_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg(lean_object* v_inst_3449_, lean_object* v_h_3450_, lean_object* v_r_3451_){
_start:
{
lean_object* v_id_3453_; lean_object* v_method_3454_; lean_object* v_param_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3475_; 
v_id_3453_ = lean_ctor_get(v_r_3451_, 0);
v_method_3454_ = lean_ctor_get(v_r_3451_, 1);
v_param_3455_ = lean_ctor_get(v_r_3451_, 2);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_r_3451_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3457_ = v_r_3451_;
v_isShared_3458_ = v_isSharedCheck_3475_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_param_3455_);
lean_inc(v_method_3454_);
lean_inc(v_id_3453_);
lean_dec(v_r_3451_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3475_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___y_3460_; lean_object* v___x_3465_; 
v___x_3465_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3449_, v_param_3455_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v___x_3466_; 
lean_dec_ref_known(v___x_3465_, 1);
v___x_3466_ = lean_box(0);
v___y_3460_ = v___x_3466_;
goto v___jp_3459_;
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
v_a_3467_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3465_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3465_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
v___y_3460_ = v___x_3472_;
goto v___jp_3459_;
}
}
}
v___jp_3459_:
{
lean_object* v___x_3462_; 
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 2, v___y_3460_);
v___x_3462_ = v___x_3457_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_id_3453_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_method_3454_);
lean_ctor_set(v_reuseFailAlloc_3464_, 2, v___y_3460_);
v___x_3462_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3450_, v___x_3462_);
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg___boxed(lean_object* v_inst_3476_, lean_object* v_h_3477_, lean_object* v_r_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3476_, v_h_3477_, v_r_3478_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest(lean_object* v_00_u03b1_3481_, lean_object* v_inst_3482_, lean_object* v_h_3483_, lean_object* v_r_3484_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3482_, v_h_3483_, v_r_3484_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___boxed(lean_object* v_00_u03b1_3487_, lean_object* v_inst_3488_, lean_object* v_h_3489_, lean_object* v_r_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_IO_FS_Stream_writeRequest(v_00_u03b1_3487_, v_inst_3488_, v_h_3489_, v_r_3490_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg(lean_object* v_inst_3493_, lean_object* v_h_3494_, lean_object* v_n_3495_){
_start:
{
lean_object* v_method_3497_; lean_object* v_param_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3518_; 
v_method_3497_ = lean_ctor_get(v_n_3495_, 0);
v_param_3498_ = lean_ctor_get(v_n_3495_, 1);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_n_3495_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3500_ = v_n_3495_;
v_isShared_3501_ = v_isSharedCheck_3518_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_param_3498_);
lean_inc(v_method_3497_);
lean_dec(v_n_3495_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3518_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___y_3503_; lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3493_, v_param_3498_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v___x_3509_; 
lean_dec_ref_known(v___x_3508_, 1);
v___x_3509_ = lean_box(0);
v___y_3503_ = v___x_3509_;
goto v___jp_3502_;
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
v_a_3510_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3508_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3508_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
v___y_3503_ = v___x_3515_;
goto v___jp_3502_;
}
}
}
v___jp_3502_:
{
lean_object* v___x_3505_; 
if (v_isShared_3501_ == 0)
{
lean_ctor_set_tag(v___x_3500_, 1);
lean_ctor_set(v___x_3500_, 1, v___y_3503_);
v___x_3505_ = v___x_3500_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_method_3497_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v___y_3503_);
v___x_3505_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3494_, v___x_3505_);
return v___x_3506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg___boxed(lean_object* v_inst_3519_, lean_object* v_h_3520_, lean_object* v_n_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3519_, v_h_3520_, v_n_3521_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification(lean_object* v_00_u03b1_3524_, lean_object* v_inst_3525_, lean_object* v_h_3526_, lean_object* v_n_3527_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3525_, v_h_3526_, v_n_3527_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___boxed(lean_object* v_00_u03b1_3530_, lean_object* v_inst_3531_, lean_object* v_h_3532_, lean_object* v_n_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_IO_FS_Stream_writeNotification(v_00_u03b1_3530_, v_inst_3531_, v_h_3532_, v_n_3533_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg(lean_object* v_inst_3536_, lean_object* v_h_3537_, lean_object* v_r_3538_){
_start:
{
lean_object* v_id_3540_; lean_object* v_result_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3550_; 
v_id_3540_ = lean_ctor_get(v_r_3538_, 0);
v_result_3541_ = lean_ctor_get(v_r_3538_, 1);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_r_3538_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3543_ = v_r_3538_;
v_isShared_3544_ = v_isSharedCheck_3550_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_result_3541_);
lean_inc(v_id_3540_);
lean_dec(v_r_3538_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3550_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3545_; lean_object* v___x_3547_; 
v___x_3545_ = lean_apply_1(v_inst_3536_, v_result_3541_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set_tag(v___x_3543_, 2);
lean_ctor_set(v___x_3543_, 1, v___x_3545_);
v___x_3547_ = v___x_3543_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_id_3540_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3537_, v___x_3547_);
return v___x_3548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg___boxed(lean_object* v_inst_3551_, lean_object* v_h_3552_, lean_object* v_r_3553_, lean_object* v_a_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3551_, v_h_3552_, v_r_3553_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse(lean_object* v_00_u03b1_3556_, lean_object* v_inst_3557_, lean_object* v_h_3558_, lean_object* v_r_3559_){
_start:
{
lean_object* v___x_3561_; 
v___x_3561_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3557_, v_h_3558_, v_r_3559_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___boxed(lean_object* v_00_u03b1_3562_, lean_object* v_inst_3563_, lean_object* v_h_3564_, lean_object* v_r_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_IO_FS_Stream_writeResponse(v_00_u03b1_3562_, v_inst_3563_, v_h_3564_, v_r_3565_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError(lean_object* v_h_3568_, lean_object* v_e_3569_){
_start:
{
lean_object* v_id_3571_; uint8_t v_code_3572_; lean_object* v_message_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3582_; 
v_id_3571_ = lean_ctor_get(v_e_3569_, 0);
v_code_3572_ = lean_ctor_get_uint8(v_e_3569_, sizeof(void*)*3);
v_message_3573_ = lean_ctor_get(v_e_3569_, 1);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_e_3569_);
if (v_isSharedCheck_3582_ == 0)
{
lean_object* v_unused_3583_; 
v_unused_3583_ = lean_ctor_get(v_e_3569_, 2);
lean_dec(v_unused_3583_);
v___x_3575_ = v_e_3569_;
v_isShared_3576_ = v_isSharedCheck_3582_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_message_3573_);
lean_inc(v_id_3571_);
lean_dec(v_e_3569_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3582_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3577_ = lean_box(0);
if (v_isShared_3576_ == 0)
{
lean_ctor_set_tag(v___x_3575_, 3);
lean_ctor_set(v___x_3575_, 2, v___x_3577_);
v___x_3579_ = v___x_3575_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_id_3571_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_message_3573_);
lean_ctor_set(v_reuseFailAlloc_3581_, 2, v___x_3577_);
lean_ctor_set_uint8(v_reuseFailAlloc_3581_, sizeof(void*)*3, v_code_3572_);
v___x_3579_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3568_, v___x_3579_);
return v___x_3580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError___boxed(lean_object* v_h_3584_, lean_object* v_e_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_IO_FS_Stream_writeResponseError(v_h_3584_, v_e_3585_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* v_inst_3588_, lean_object* v_h_3589_, lean_object* v_e_3590_){
_start:
{
lean_object* v_id_3592_; uint8_t v_code_3593_; lean_object* v_message_3594_; lean_object* v_data_x3f_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3615_; 
v_id_3592_ = lean_ctor_get(v_e_3590_, 0);
v_code_3593_ = lean_ctor_get_uint8(v_e_3590_, sizeof(void*)*3);
v_message_3594_ = lean_ctor_get(v_e_3590_, 1);
v_data_x3f_3595_ = lean_ctor_get(v_e_3590_, 2);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_e_3590_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3597_ = v_e_3590_;
v_isShared_3598_ = v_isSharedCheck_3615_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_data_x3f_3595_);
lean_inc(v_message_3594_);
lean_inc(v_id_3592_);
lean_dec(v_e_3590_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3615_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___y_3600_; 
if (lean_obj_tag(v_data_x3f_3595_) == 0)
{
lean_object* v___x_3605_; 
lean_dec_ref(v_inst_3588_);
v___x_3605_ = lean_box(0);
v___y_3600_ = v___x_3605_;
goto v___jp_3599_;
}
else
{
lean_object* v_val_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3614_; 
v_val_3606_ = lean_ctor_get(v_data_x3f_3595_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v_data_x3f_3595_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3608_ = v_data_x3f_3595_;
v_isShared_3609_ = v_isSharedCheck_3614_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_val_3606_);
lean_dec(v_data_x3f_3595_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3614_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3610_ = lean_apply_1(v_inst_3588_, v_val_3606_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3610_);
v___x_3612_ = v___x_3608_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
v___y_3600_ = v___x_3612_;
goto v___jp_3599_;
}
}
}
v___jp_3599_:
{
lean_object* v___x_3602_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set_tag(v___x_3597_, 3);
lean_ctor_set(v___x_3597_, 2, v___y_3600_);
v___x_3602_ = v___x_3597_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_id_3592_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_message_3594_);
lean_ctor_set(v_reuseFailAlloc_3604_, 2, v___y_3600_);
lean_ctor_set_uint8(v_reuseFailAlloc_3604_, sizeof(void*)*3, v_code_3593_);
v___x_3602_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3589_, v___x_3602_);
return v___x_3603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object* v_inst_3616_, lean_object* v_h_3617_, lean_object* v_e_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3616_, v_h_3617_, v_e_3618_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData(lean_object* v_00_u03b1_3621_, lean_object* v_inst_3622_, lean_object* v_h_3623_, lean_object* v_e_3624_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3622_, v_h_3623_, v_e_3624_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object* v_00_u03b1_3627_, lean_object* v_inst_3628_, lean_object* v_h_3629_, lean_object* v_e_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData(v_00_u03b1_3627_, v_inst_3628_, v_h_3629_, v_e_3630_);
return v_res_3632_;
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
