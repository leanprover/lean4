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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___redArg(){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___closed__0));
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___boxed(lean_object* v___dummy_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_JsonRpc_instInhabitedResponseError_default___redArg();
return v_res_881_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0(void){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_JsonRpc_instInhabitedResponseError_default___redArg();
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object* v_00_u03b1_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError___redArg(){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError___redArg___boxed(lean_object* v___dummy_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_JsonRpc_instInhabitedResponseError___redArg();
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object* v_a_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_890_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq___redArg(lean_object* v_inst_891_, lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
lean_object* v_id_894_; uint8_t v_code_895_; lean_object* v_message_896_; lean_object* v_data_x3f_897_; lean_object* v_id_898_; uint8_t v_code_899_; lean_object* v_message_900_; lean_object* v_data_x3f_901_; uint8_t v___x_902_; 
v_id_894_ = lean_ctor_get(v_x_892_, 0);
lean_inc(v_id_894_);
v_code_895_ = lean_ctor_get_uint8(v_x_892_, sizeof(void*)*3);
v_message_896_ = lean_ctor_get(v_x_892_, 1);
lean_inc_ref(v_message_896_);
v_data_x3f_897_ = lean_ctor_get(v_x_892_, 2);
lean_inc(v_data_x3f_897_);
lean_dec_ref(v_x_892_);
v_id_898_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_id_898_);
v_code_899_ = lean_ctor_get_uint8(v_x_893_, sizeof(void*)*3);
v_message_900_ = lean_ctor_get(v_x_893_, 1);
lean_inc_ref(v_message_900_);
v_data_x3f_901_ = lean_ctor_get(v_x_893_, 2);
lean_inc(v_data_x3f_901_);
lean_dec_ref(v_x_893_);
v___x_902_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_894_, v_id_898_);
lean_dec(v_id_898_);
lean_dec(v_id_894_);
if (v___x_902_ == 0)
{
lean_dec(v_data_x3f_901_);
lean_dec_ref(v_message_900_);
lean_dec(v_data_x3f_897_);
lean_dec_ref(v_message_896_);
lean_dec_ref(v_inst_891_);
return v___x_902_;
}
else
{
uint8_t v___x_903_; 
v___x_903_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_code_895_, v_code_899_);
if (v___x_903_ == 0)
{
lean_dec(v_data_x3f_901_);
lean_dec_ref(v_message_900_);
lean_dec(v_data_x3f_897_);
lean_dec_ref(v_message_896_);
lean_dec_ref(v_inst_891_);
return v___x_903_;
}
else
{
uint8_t v___x_904_; 
v___x_904_ = lean_string_dec_eq(v_message_896_, v_message_900_);
lean_dec_ref(v_message_900_);
lean_dec_ref(v_message_896_);
if (v___x_904_ == 0)
{
lean_dec(v_data_x3f_901_);
lean_dec(v_data_x3f_897_);
lean_dec_ref(v_inst_891_);
return v___x_904_;
}
else
{
uint8_t v___x_905_; 
v___x_905_ = l_Option_instBEq_beq___redArg(v_inst_891_, v_data_x3f_897_, v_data_x3f_901_);
return v___x_905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(lean_object* v_inst_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
uint8_t v_res_909_; lean_object* v_r_910_; 
v_res_909_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_906_, v_x_907_, v_x_908_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object* v_00_u03b1_911_, lean_object* v_inst_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_912_, v_x_913_, v_x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___boxed(lean_object* v_00_u03b1_916_, lean_object* v_inst_917_, lean_object* v_x_918_, lean_object* v_x_919_){
_start:
{
uint8_t v_res_920_; lean_object* v_r_921_; 
v_res_920_ = l_Lean_JsonRpc_instBEqResponseError_beq(v_00_u03b1_916_, v_inst_917_, v_x_918_, v_x_919_);
v_r_921_ = lean_box(v_res_920_);
return v_r_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object* v_inst_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_923_, 0, lean_box(0));
lean_closure_set(v___x_923_, 1, v_inst_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object* v_00_u03b1_924_, lean_object* v_inst_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_926_, 0, lean_box(0));
lean_closure_set(v___x_926_, 1, v_inst_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object* v_inst_927_, lean_object* v_r_928_){
_start:
{
lean_object* v_data_x3f_929_; 
v_data_x3f_929_ = lean_ctor_get(v_r_928_, 2);
lean_inc(v_data_x3f_929_);
if (lean_obj_tag(v_data_x3f_929_) == 0)
{
lean_object* v_id_930_; uint8_t v_code_931_; lean_object* v_message_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v_inst_927_);
v_id_930_ = lean_ctor_get(v_r_928_, 0);
v_code_931_ = lean_ctor_get_uint8(v_r_928_, sizeof(void*)*3);
v_message_932_ = lean_ctor_get(v_r_928_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_r_928_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v_r_928_, 2);
lean_dec(v_unused_941_);
v___x_934_ = v_r_928_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_message_932_);
lean_inc(v_id_930_);
lean_dec(v_r_928_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = lean_box(0);
if (v_isShared_935_ == 0)
{
lean_ctor_set_tag(v___x_934_, 3);
lean_ctor_set(v___x_934_, 2, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_id_930_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_message_932_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v___x_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_939_, sizeof(void*)*3, v_code_931_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
lean_object* v_id_942_; uint8_t v_code_943_; lean_object* v_message_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_960_; 
v_id_942_ = lean_ctor_get(v_r_928_, 0);
v_code_943_ = lean_ctor_get_uint8(v_r_928_, sizeof(void*)*3);
v_message_944_ = lean_ctor_get(v_r_928_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v_r_928_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; 
v_unused_961_ = lean_ctor_get(v_r_928_, 2);
lean_dec(v_unused_961_);
v___x_946_ = v_r_928_;
v_isShared_947_ = v_isSharedCheck_960_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_message_944_);
lean_inc(v_id_942_);
lean_dec(v_r_928_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_960_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_val_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_959_; 
v_val_948_ = lean_ctor_get(v_data_x3f_929_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v_data_x3f_929_);
if (v_isSharedCheck_959_ == 0)
{
v___x_950_ = v_data_x3f_929_;
v_isShared_951_ = v_isSharedCheck_959_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_val_948_);
lean_dec(v_data_x3f_929_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_959_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_apply_1(v_inst_927_, v_val_948_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_956_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 3);
lean_ctor_set(v___x_946_, 2, v___x_954_);
v___x_956_ = v___x_946_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_id_942_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_message_944_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v___x_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_957_, sizeof(void*)*3, v_code_943_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object* v_inst_962_){
_start:
{
lean_object* v___f_963_; 
v___f_963_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_963_, 0, v_inst_962_);
return v___f_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object* v_00_u03b1_964_, lean_object* v_inst_965_){
_start:
{
lean_object* v___f_966_; 
v___f_966_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_966_, 0, v_inst_965_);
return v___f_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object* v_r_967_){
_start:
{
lean_object* v_id_968_; uint8_t v_code_969_; lean_object* v_message_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
v_id_968_ = lean_ctor_get(v_r_967_, 0);
v_code_969_ = lean_ctor_get_uint8(v_r_967_, sizeof(void*)*3);
v_message_970_ = lean_ctor_get(v_r_967_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_r_967_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v_r_967_, 2);
lean_dec(v_unused_979_);
v___x_972_ = v_r_967_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_message_970_);
lean_inc(v_id_968_);
lean_dec(v_r_967_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = lean_box(0);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 3);
lean_ctor_set(v___x_972_, 2, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_id_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_message_970_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v___x_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*3, v_code_969_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ofMessage_x3f(lean_object* v_x_982_){
_start:
{
if (lean_obj_tag(v_x_982_) == 3)
{
lean_object* v_id_983_; uint8_t v_code_984_; lean_object* v_message_985_; lean_object* v_data_x3f_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_994_; 
v_id_983_ = lean_ctor_get(v_x_982_, 0);
v_code_984_ = lean_ctor_get_uint8(v_x_982_, sizeof(void*)*3);
v_message_985_ = lean_ctor_get(v_x_982_, 1);
v_data_x3f_986_ = lean_ctor_get(v_x_982_, 2);
v_isSharedCheck_994_ = !lean_is_exclusive(v_x_982_);
if (v_isSharedCheck_994_ == 0)
{
v___x_988_ = v_x_982_;
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_data_x3f_986_);
lean_inc(v_message_985_);
lean_inc(v_id_983_);
lean_dec(v_x_982_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set_tag(v___x_988_, 0);
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_id_983_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_message_985_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_data_x3f_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_993_, sizeof(void*)*3, v_code_984_);
v___x_991_ = v_reuseFailAlloc_993_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
}
else
{
lean_object* v___x_995_; 
lean_dec_ref(v_x_982_);
v___x_995_ = lean_box(0);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object* v_s_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v_s_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object* v_n_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1001_, 0, v_n_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_RequestID_lt(lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
switch(lean_obj_tag(v_x_1004_))
{
case 0:
{
if (lean_obj_tag(v_x_1005_) == 0)
{
lean_object* v_s_1006_; lean_object* v_s_1007_; uint8_t v___x_1008_; 
v_s_1006_ = lean_ctor_get(v_x_1004_, 0);
lean_inc_ref(v_s_1006_);
lean_dec_ref_known(v_x_1004_, 1);
v_s_1007_ = lean_ctor_get(v_x_1005_, 0);
lean_inc_ref(v_s_1007_);
lean_dec_ref_known(v_x_1005_, 1);
v___x_1008_ = lean_string_dec_lt(v_s_1006_, v_s_1007_);
lean_dec_ref(v_s_1007_);
lean_dec_ref(v_s_1006_);
return v___x_1008_;
}
else
{
uint8_t v___x_1009_; 
lean_dec_ref_known(v_x_1004_, 1);
lean_dec(v_x_1005_);
v___x_1009_ = 0;
return v___x_1009_;
}
}
case 1:
{
switch(lean_obj_tag(v_x_1005_))
{
case 1:
{
lean_object* v_n_1010_; lean_object* v_n_1011_; uint8_t v___x_1012_; 
v_n_1010_ = lean_ctor_get(v_x_1004_, 0);
lean_inc_ref(v_n_1010_);
lean_dec_ref_known(v_x_1004_, 1);
v_n_1011_ = lean_ctor_get(v_x_1005_, 0);
lean_inc_ref(v_n_1011_);
lean_dec_ref_known(v_x_1005_, 1);
v___x_1012_ = l_Lean_JsonNumber_lt(v_n_1010_, v_n_1011_);
return v___x_1012_;
}
case 0:
{
uint8_t v___x_1013_; 
lean_dec_ref_known(v_x_1005_, 1);
lean_dec_ref_known(v_x_1004_, 1);
v___x_1013_ = 1;
return v___x_1013_;
}
default: 
{
uint8_t v___x_1014_; 
lean_dec_ref_known(v_x_1004_, 1);
lean_dec(v_x_1005_);
v___x_1014_ = 0;
return v___x_1014_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_1005_))
{
case 1:
{
uint8_t v___x_1015_; 
lean_dec_ref_known(v_x_1005_, 1);
v___x_1015_ = 1;
return v___x_1015_;
}
case 0:
{
uint8_t v___x_1016_; 
lean_dec_ref_known(v_x_1005_, 1);
v___x_1016_ = 1;
return v___x_1016_;
}
default: 
{
uint8_t v___x_1017_; 
lean_dec(v_x_1005_);
v___x_1017_ = 0;
return v___x_1017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_lt___boxed(lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = l_Lean_JsonRpc_RequestID_lt(v_x_1018_, v_x_1019_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
static lean_object* _init_l_Lean_JsonRpc_RequestID_ltProp(void){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_box(0);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instLTRequestID(void){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = lean_box(0);
return v___x_1023_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object* v_a_1024_, lean_object* v_b_1025_){
_start:
{
uint8_t v___x_1026_; 
v___x_1026_ = l_Lean_JsonRpc_RequestID_lt(v_a_1024_, v_b_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object* v_a_1027_, lean_object* v_b_1028_){
_start:
{
uint8_t v_res_1029_; lean_object* v_r_1030_; 
v_res_1029_ = l_Lean_JsonRpc_instDecidableLtRequestID(v_a_1027_, v_b_1028_);
v_r_1030_ = lean_box(v_res_1029_);
return v_r_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object* v_j_1034_){
_start:
{
switch(lean_obj_tag(v_j_1034_))
{
case 3:
{
lean_object* v_s_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1043_; 
v_s_1035_ = lean_ctor_get(v_j_1034_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_j_1034_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1037_ = v_j_1034_;
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_s_1035_);
lean_dec(v_j_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 0);
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_s_1035_);
v___x_1040_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
}
case 2:
{
lean_object* v_n_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1052_; 
v_n_1044_ = lean_ctor_get(v_j_1034_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_j_1034_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1046_ = v_j_1034_;
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_n_1044_);
lean_dec(v_j_1034_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 1);
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_n_1044_);
v___x_1049_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
}
}
default: 
{
lean_object* v___x_1053_; 
lean_dec(v_j_1034_);
v___x_1053_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object* v_rid_1056_){
_start:
{
switch(lean_obj_tag(v_rid_1056_))
{
case 0:
{
lean_object* v_s_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_s_1057_ = lean_ctor_get(v_rid_1056_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_rid_1056_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v_rid_1056_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_s_1057_);
lean_dec(v_rid_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 3);
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_s_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
case 1:
{
lean_object* v_n_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_n_1065_ = lean_ctor_get(v_rid_1056_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_rid_1056_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v_rid_1056_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_n_1065_);
lean_dec(v_rid_1056_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 2);
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_n_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
default: 
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_box(0);
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object* v___x_1091_, lean_object* v___x_1092_, lean_object* v_m_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v___y_1096_; 
v___x_1094_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_1093_))
{
case 0:
{
lean_object* v_id_1099_; lean_object* v_method_1100_; lean_object* v_params_x3f_1101_; lean_object* v___x_1102_; lean_object* v___y_1104_; 
lean_dec_ref(v___x_1092_);
v_id_1099_ = lean_ctor_get(v_m_1093_, 0);
lean_inc(v_id_1099_);
v_method_1100_ = lean_ctor_get(v_m_1093_, 1);
lean_inc_ref(v_method_1100_);
v_params_x3f_1101_ = lean_ctor_get(v_m_1093_, 2);
lean_inc(v_params_x3f_1101_);
lean_dec_ref_known(v_m_1093_, 3);
v___x_1102_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1099_))
{
case 0:
{
lean_object* v_s_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_s_1115_ = lean_ctor_get(v_id_1099_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_id_1099_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v_id_1099_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_s_1115_);
lean_dec(v_id_1099_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 3);
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_s_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
v___y_1104_ = v___x_1120_;
goto v___jp_1103_;
}
}
}
case 1:
{
lean_object* v_n_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_n_1123_ = lean_ctor_get(v_id_1099_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_id_1099_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v_id_1099_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_n_1123_);
lean_dec(v_id_1099_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 2);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_n_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
v___y_1104_ = v___x_1128_;
goto v___jp_1103_;
}
}
}
default: 
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_box(0);
v___y_1104_ = v___x_1131_;
goto v___jp_1103_;
}
}
v___jp_1103_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1102_);
lean_ctor_set(v___x_1105_, 1, v___y_1104_);
v___x_1106_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1107_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1107_, 0, v_method_1100_);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1105_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1113_ = l_Lean_Json_opt___redArg(v___x_1091_, v___x_1112_, v_params_x3f_1101_);
v___x_1114_ = l_List_appendTR___redArg(v___x_1111_, v___x_1113_);
v___y_1096_ = v___x_1114_;
goto v___jp_1095_;
}
}
case 1:
{
lean_object* v_method_1132_; lean_object* v_params_x3f_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v___x_1092_);
v_method_1132_ = lean_ctor_get(v_m_1093_, 0);
v_params_x3f_1133_ = lean_ctor_get(v_m_1093_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_m_1093_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1135_ = v_m_1093_;
v_isShared_1136_ = v_isSharedCheck_1145_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_params_x3f_1133_);
lean_inc(v_method_1132_);
lean_dec(v_m_1093_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1145_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1137_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_method_1132_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 0);
lean_ctor_set(v___x_1135_, 1, v___x_1138_);
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1140_ = v___x_1135_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1142_ = l_Lean_Json_opt___redArg(v___x_1091_, v___x_1141_, v_params_x3f_1133_);
v___x_1143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1140_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___y_1096_ = v___x_1143_;
goto v___jp_1095_;
}
}
}
case 2:
{
lean_object* v_id_1146_; lean_object* v_result_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1179_; 
lean_dec_ref(v___x_1092_);
lean_dec_ref(v___x_1091_);
v_id_1146_ = lean_ctor_get(v_m_1093_, 0);
v_result_1147_ = lean_ctor_get(v_m_1093_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_m_1093_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1149_ = v_m_1093_;
v_isShared_1150_ = v_isSharedCheck_1179_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_result_1147_);
lean_inc(v_id_1146_);
lean_dec(v_m_1093_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1179_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___y_1153_; 
v___x_1151_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1146_))
{
case 0:
{
lean_object* v_s_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
v_s_1162_ = lean_ctor_get(v_id_1146_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_id_1146_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v_id_1146_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_s_1162_);
lean_dec(v_id_1146_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 3);
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_s_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
v___y_1153_ = v___x_1167_;
goto v___jp_1152_;
}
}
}
case 1:
{
lean_object* v_n_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_n_1170_ = lean_ctor_get(v_id_1146_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_id_1146_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v_id_1146_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_n_1170_);
lean_dec(v_id_1146_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set_tag(v___x_1172_, 2);
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_n_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
v___y_1153_ = v___x_1175_;
goto v___jp_1152_;
}
}
}
default: 
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_box(0);
v___y_1153_ = v___x_1178_;
goto v___jp_1152_;
}
}
v___jp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 0);
lean_ctor_set(v___x_1149_, 1, v___y_1153_);
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1155_ = v___x_1149_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___y_1153_);
v___x_1155_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1156_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v_result_1147_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1155_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___y_1096_ = v___x_1160_;
goto v___jp_1095_;
}
}
}
}
default: 
{
lean_object* v_id_1180_; uint8_t v_code_1181_; lean_object* v_message_1182_; lean_object* v_data_x3f_1183_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___x_1203_; lean_object* v___y_1205_; 
lean_dec_ref(v___x_1091_);
v_id_1180_ = lean_ctor_get(v_m_1093_, 0);
lean_inc(v_id_1180_);
v_code_1181_ = lean_ctor_get_uint8(v_m_1093_, sizeof(void*)*3);
v_message_1182_ = lean_ctor_get(v_m_1093_, 1);
lean_inc_ref(v_message_1182_);
v_data_x3f_1183_ = lean_ctor_get(v_m_1093_, 2);
lean_inc(v_data_x3f_1183_);
lean_dec_ref_known(v_m_1093_, 3);
v___x_1203_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1180_))
{
case 0:
{
lean_object* v_s_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v_s_1221_ = lean_ctor_get(v_id_1180_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_id_1180_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v_id_1180_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_s_1221_);
lean_dec(v_id_1180_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 3);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_s_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
v___y_1205_ = v___x_1226_;
goto v___jp_1204_;
}
}
}
case 1:
{
lean_object* v_n_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_n_1229_ = lean_ctor_get(v_id_1180_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_id_1180_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v_id_1180_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_n_1229_);
lean_dec(v_id_1180_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set_tag(v___x_1231_, 2);
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_n_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
v___y_1205_ = v___x_1234_;
goto v___jp_1204_;
}
}
}
default: 
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_box(0);
v___y_1205_ = v___x_1237_;
goto v___jp_1204_;
}
}
v___jp_1184_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1186_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___y_1186_);
lean_ctor_set(v___x_1189_, 1, v___y_1188_);
v___x_1190_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_message_1182_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = lean_box(0);
v___x_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1189_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1197_ = l_Lean_Json_opt___redArg(v___x_1092_, v___x_1196_, v_data_x3f_1183_);
v___x_1198_ = l_List_appendTR___redArg(v___x_1195_, v___x_1197_);
v___x_1199_ = l_Lean_Json_mkObj(v___x_1198_);
lean_dec(v___x_1198_);
lean_inc_ref(v___y_1187_);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___y_1187_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
lean_ctor_set(v___x_1201_, 1, v___x_1193_);
v___x_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___y_1185_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___y_1096_ = v___x_1202_;
goto v___jp_1095_;
}
v___jp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1203_);
lean_ctor_set(v___x_1206_, 1, v___y_1205_);
v___x_1207_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1208_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_1181_)
{
case 0:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1209_;
goto v___jp_1184_;
}
case 1:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1210_;
goto v___jp_1184_;
}
case 2:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1211_;
goto v___jp_1184_;
}
case 3:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1212_;
goto v___jp_1184_;
}
case 4:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1213_;
goto v___jp_1184_;
}
case 5:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1214_;
goto v___jp_1184_;
}
case 6:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1215_;
goto v___jp_1184_;
}
case 7:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1216_;
goto v___jp_1184_;
}
case 8:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1217_;
goto v___jp_1184_;
}
case 9:
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1218_;
goto v___jp_1184_;
}
case 10:
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1219_;
goto v___jp_1184_;
}
default: 
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_1185_ = v___x_1206_;
v___y_1186_ = v___x_1208_;
v___y_1187_ = v___x_1207_;
v___y_1188_ = v___x_1220_;
goto v___jp_1184_;
}
}
}
}
}
v___jp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1094_);
lean_ctor_set(v___x_1097_, 1, v___y_1096_);
v___x_1098_ = l_Lean_Json_mkObj(v___x_1097_);
lean_dec_ref_known(v___x_1097_, 2);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object* v___f_1247_, lean_object* v___f_1248_, lean_object* v___x_1249_, lean_object* v___x_1250_, lean_object* v_j_1251_){
_start:
{
lean_object* v___y_1255_; lean_object* v___y_1256_; uint8_t v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1251_);
v___x_1267_ = l_Lean_Json_getObjVal_x3f(v_j_1251_, v___x_1266_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v_j_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v___f_1248_);
lean_dec_ref(v___f_1247_);
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
else
{
lean_object* v_a_1276_; 
v_a_1276_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1267_, 1);
if (lean_obj_tag(v_a_1276_) == 3)
{
lean_object* v_s_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_s_1277_ = lean_ctor_get(v_a_1276_, 0);
lean_inc_ref(v_s_1277_);
lean_dec_ref_known(v_a_1276_, 1);
v___x_1278_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1279_ = lean_string_dec_eq(v_s_1277_, v___x_1278_);
lean_dec_ref(v_s_1277_);
if (v___x_1279_ == 0)
{
lean_dec(v_j_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v___f_1248_);
lean_dec_ref(v___f_1247_);
goto v___jp_1252_;
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1251_);
v___x_1281_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1251_, v___f_1247_, v___x_1280_);
if (lean_obj_tag(v___x_1281_) == 0)
{
goto v___jp_1338_;
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_a_1365_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1365_);
v___x_1366_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1249_);
lean_inc(v_j_1251_);
v___x_1367_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1251_, v___x_1249_, v___x_1366_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_dec_ref_known(v___x_1367_, 1);
lean_dec(v_a_1365_);
goto v___jp_1338_;
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref_known(v___x_1281_, 1);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v___f_1248_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1389_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1389_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___y_1373_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1379_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1251_, v___x_1250_, v___x_1378_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v___x_1380_; 
lean_dec_ref_known(v___x_1379_, 1);
v___x_1380_ = lean_box(0);
v___y_1373_ = v___x_1380_;
goto v___jp_1372_;
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1379_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1379_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
v___y_1373_ = v___x_1386_;
goto v___jp_1372_;
}
}
}
v___jp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1374_, 0, v_a_1365_);
lean_ctor_set(v___x_1374_, 1, v_a_1368_);
lean_ctor_set(v___x_1374_, 2, v___y_1373_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1374_);
v___x_1376_ = v___x_1370_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
v___jp_1282_:
{
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_j_1251_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v___f_1248_);
v_a_1283_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1281_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v_a_1291_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1281_, 1);
v___x_1292_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1293_ = l_Lean_Json_getObjVal_x3f(v_j_1251_, v___x_1292_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_a_1291_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v___f_1248_);
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_a_1302_ = lean_ctor_get(v___x_1293_, 0);
lean_inc_n(v_a_1302_, 2);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1303_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1304_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1302_, v___f_1248_, v___x_1303_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_a_1302_);
lean_dec(v_a_1291_);
lean_dec_ref(v___x_1249_);
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v_a_1313_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1314_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1302_);
v___x_1315_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1302_, v___x_1249_, v___x_1314_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v_a_1313_);
lean_dec(v_a_1302_);
lean_dec(v_a_1291_);
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_a_1324_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1325_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1326_ = l_Lean_Json_getObjVal_x3f(v_a_1302_, v___x_1325_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
lean_dec_ref_known(v___x_1326_, 1);
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_unbox(v_a_1313_);
lean_dec(v_a_1313_);
v___y_1255_ = v_a_1291_;
v___y_1256_ = v_a_1324_;
v___y_1257_ = v___x_1328_;
v___y_1258_ = v___x_1327_;
goto v___jp_1254_;
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1337_; 
v_a_1329_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1331_ = v___x_1326_;
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1326_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
uint8_t v___x_1335_; 
v___x_1335_ = lean_unbox(v_a_1313_);
lean_dec(v_a_1313_);
v___y_1255_ = v_a_1291_;
v___y_1256_ = v_a_1324_;
v___y_1257_ = v___x_1335_;
v___y_1258_ = v___x_1334_;
goto v___jp_1254_;
}
}
}
}
}
}
}
}
v___jp_1338_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1249_);
lean_inc(v_j_1251_);
v___x_1340_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1251_, v___x_1249_, v___x_1339_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_dec_ref_known(v___x_1340_, 1);
lean_dec_ref(v___x_1250_);
if (lean_obj_tag(v___x_1281_) == 0)
{
goto v___jp_1282_;
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_a_1341_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1341_);
v___x_1342_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1251_);
v___x_1343_ = l_Lean_Json_getObjVal_x3f(v_j_1251_, v___x_1342_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_dec_ref_known(v___x_1343_, 1);
lean_dec(v_a_1341_);
goto v___jp_1282_;
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref_known(v___x_1281_, 1);
lean_dec(v_j_1251_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v___f_1248_);
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_a_1341_);
lean_ctor_set(v___x_1348_, 1, v_a_1344_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1348_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec_ref(v___x_1281_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v___f_1248_);
v_a_1353_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1340_, 1);
v___x_1354_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1355_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1251_, v___x_1250_, v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v___x_1356_; 
lean_dec_ref_known(v___x_1355_, 1);
v___x_1356_ = lean_box(0);
v___y_1262_ = v_a_1353_;
v___y_1263_ = v___x_1356_;
goto v___jp_1261_;
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
v_a_1357_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1355_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1355_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
v___y_1262_ = v_a_1353_;
v___y_1263_ = v___x_1362_;
goto v___jp_1261_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1276_);
lean_dec(v_j_1251_);
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v___f_1248_);
lean_dec_ref(v___f_1247_);
goto v___jp_1252_;
}
}
v___jp_1252_:
{
lean_object* v___x_1253_; 
v___x_1253_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1));
return v___x_1253_;
}
v___jp_1254_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1259_, 0, v___y_1255_);
lean_ctor_set(v___x_1259_, 1, v___y_1256_);
lean_ctor_set(v___x_1259_, 2, v___y_1258_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*3, v___y_1257_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
v___jp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___y_1262_);
lean_ctor_set(v___x_1264_, 1, v___y_1263_);
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object* v___x_1403_, lean_object* v_inst_1404_, lean_object* v_j_1405_){
_start:
{
lean_object* v_method_1409_; lean_object* v_params_x3f_1410_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1405_);
v___x_1433_ = l_Lean_Json_getObjVal_x3f(v_j_1405_, v___x_1432_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_j_1405_);
lean_dec_ref(v_inst_1404_);
lean_dec_ref(v___x_1403_);
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
else
{
lean_object* v_a_1442_; 
v_a_1442_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1433_, 1);
if (lean_obj_tag(v_a_1442_) == 3)
{
lean_object* v_s_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_s_1443_ = lean_ctor_get(v_a_1442_, 0);
lean_inc_ref(v_s_1443_);
lean_dec_ref_known(v_a_1442_, 1);
v___x_1444_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1445_ = lean_string_dec_eq(v_s_1443_, v___x_1444_);
lean_dec_ref(v_s_1443_);
if (v___x_1445_ == 0)
{
lean_dec(v_j_1405_);
lean_dec_ref(v_inst_1404_);
lean_dec_ref(v___x_1403_);
goto v___jp_1430_;
}
else
{
lean_object* v___f_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___f_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___f_1446_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___closed__0));
v___x_1447_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__0));
v___x_1448_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__1));
v___f_1449_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___closed__0));
v___x_1450_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1405_);
v___x_1451_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1405_, v___f_1446_, v___x_1450_);
if (lean_obj_tag(v___x_1451_) == 0)
{
goto v___jp_1492_;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1405_);
v___x_1510_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1405_, v___x_1447_, v___x_1509_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_dec_ref_known(v___x_1510_, 1);
goto v___jp_1492_;
}
else
{
lean_dec_ref_known(v___x_1510_, 1);
lean_dec_ref_known(v___x_1451_, 1);
lean_dec(v_j_1405_);
lean_dec_ref(v_inst_1404_);
lean_dec_ref(v___x_1403_);
goto v___jp_1406_;
}
}
v___jp_1452_:
{
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_j_1405_);
v_a_1453_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1451_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1451_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref_known(v___x_1451_, 1);
v___x_1461_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1462_ = l_Lean_Json_getObjVal_x3f(v_j_1405_, v___x_1461_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_a_1471_ = lean_ctor_get(v___x_1462_, 0);
lean_inc_n(v_a_1471_, 2);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1472_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1473_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1471_, v___f_1449_, v___x_1472_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec(v_a_1471_);
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec_ref_known(v___x_1473_, 1);
v___x_1482_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1483_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1471_, v___x_1447_, v___x_1482_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
else
{
lean_dec_ref_known(v___x_1483_, 1);
goto v___jp_1406_;
}
}
}
}
}
v___jp_1492_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1405_);
v___x_1494_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1405_, v___x_1447_, v___x_1493_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_dec_ref_known(v___x_1494_, 1);
lean_dec_ref(v_inst_1404_);
lean_dec_ref(v___x_1403_);
if (lean_obj_tag(v___x_1451_) == 0)
{
goto v___jp_1452_;
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1405_);
v___x_1496_ = l_Lean_Json_getObjVal_x3f(v_j_1405_, v___x_1495_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_dec_ref_known(v___x_1496_, 1);
goto v___jp_1452_;
}
else
{
lean_dec_ref_known(v___x_1496_, 1);
lean_dec_ref_known(v___x_1451_, 1);
lean_dec(v_j_1405_);
goto v___jp_1406_;
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec_ref(v___x_1451_);
v_a_1497_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1494_, 1);
v___x_1498_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1499_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1405_, v___x_1448_, v___x_1498_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v___x_1500_; 
lean_dec_ref_known(v___x_1499_, 1);
v___x_1500_ = lean_box(0);
v_method_1409_ = v_a_1497_;
v_params_x3f_1410_ = v___x_1500_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
v_a_1501_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1499_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1499_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
v_method_1409_ = v_a_1497_;
v_params_x3f_1410_ = v___x_1506_;
goto v___jp_1408_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1442_);
lean_dec(v_j_1405_);
lean_dec_ref(v_inst_1404_);
lean_dec_ref(v___x_1403_);
goto v___jp_1430_;
}
}
v___jp_1406_:
{
lean_object* v___x_1407_; 
v___x_1407_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1));
return v___x_1407_;
}
v___jp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = l_Lean_Option_toJson___redArg(v___x_1403_, v_params_x3f_1410_);
v___x_1412_ = lean_apply_1(v_inst_1404_, v___x_1411_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_method_1409_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1429_; 
v_a_1421_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1423_ = v___x_1412_;
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1412_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_method_1409_);
lean_ctor_set(v___x_1425_, 1, v_a_1421_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1425_);
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
v___jp_1430_:
{
lean_object* v___x_1431_; 
v___x_1431_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2));
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object* v_inst_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v___f_1513_; 
v___x_1512_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___f_1513_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1513_, 0, v___x_1512_);
lean_closure_set(v___f_1513_, 1, v_inst_1511_);
return v___f_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object* v_00_u03b1_1514_, lean_object* v_inst_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_JsonRpc_instFromJsonNotification___redArg(v_inst_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx(lean_object* v_x_1517_){
_start:
{
switch(lean_obj_tag(v_x_1517_))
{
case 0:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_unsigned_to_nat(0u);
return v___x_1518_;
}
case 1:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_unsigned_to_nat(1u);
return v___x_1519_;
}
case 2:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_unsigned_to_nat(2u);
return v___x_1520_;
}
default: 
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_unsigned_to_nat(3u);
return v___x_1521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___boxed(lean_object* v_x_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_JsonRpc_MessageMetaData_ctorIdx(v_x_1522_);
lean_dec_ref(v_x_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(lean_object* v_t_1524_, lean_object* v_k_1525_){
_start:
{
switch(lean_obj_tag(v_t_1524_))
{
case 0:
{
lean_object* v_id_1526_; lean_object* v_method_1527_; lean_object* v___x_1528_; 
v_id_1526_ = lean_ctor_get(v_t_1524_, 0);
lean_inc(v_id_1526_);
v_method_1527_ = lean_ctor_get(v_t_1524_, 1);
lean_inc_ref(v_method_1527_);
lean_dec_ref_known(v_t_1524_, 2);
v___x_1528_ = lean_apply_2(v_k_1525_, v_id_1526_, v_method_1527_);
return v___x_1528_;
}
case 1:
{
lean_object* v_method_1529_; lean_object* v___x_1530_; 
v_method_1529_ = lean_ctor_get(v_t_1524_, 0);
lean_inc_ref(v_method_1529_);
lean_dec_ref_known(v_t_1524_, 1);
v___x_1530_ = lean_apply_1(v_k_1525_, v_method_1529_);
return v___x_1530_;
}
case 2:
{
lean_object* v_id_1531_; lean_object* v___x_1532_; 
v_id_1531_ = lean_ctor_get(v_t_1524_, 0);
lean_inc(v_id_1531_);
lean_dec_ref_known(v_t_1524_, 1);
v___x_1532_ = lean_apply_1(v_k_1525_, v_id_1531_);
return v___x_1532_;
}
default: 
{
lean_object* v_id_1533_; uint8_t v_code_1534_; lean_object* v_message_1535_; lean_object* v_data_x3f_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_id_1533_ = lean_ctor_get(v_t_1524_, 0);
lean_inc(v_id_1533_);
v_code_1534_ = lean_ctor_get_uint8(v_t_1524_, sizeof(void*)*3);
v_message_1535_ = lean_ctor_get(v_t_1524_, 1);
lean_inc_ref(v_message_1535_);
v_data_x3f_1536_ = lean_ctor_get(v_t_1524_, 2);
lean_inc(v_data_x3f_1536_);
lean_dec_ref_known(v_t_1524_, 3);
v___x_1537_ = lean_box(v_code_1534_);
v___x_1538_ = lean_apply_4(v_k_1525_, v_id_1533_, v___x_1537_, v_message_1535_, v_data_x3f_1536_);
return v___x_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim(lean_object* v_motive_1539_, lean_object* v_ctorIdx_1540_, lean_object* v_t_1541_, lean_object* v_h_1542_, lean_object* v_k_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1541_, v_k_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(lean_object* v_motive_1545_, lean_object* v_ctorIdx_1546_, lean_object* v_t_1547_, lean_object* v_h_1548_, lean_object* v_k_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_JsonRpc_MessageMetaData_ctorElim(v_motive_1545_, v_ctorIdx_1546_, v_t_1547_, v_h_1548_, v_k_1549_);
lean_dec(v_ctorIdx_1546_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim___redArg(lean_object* v_t_1551_, lean_object* v_request_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1551_, v_request_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim(lean_object* v_motive_1554_, lean_object* v_t_1555_, lean_object* v_h_1556_, lean_object* v_request_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1555_, v_request_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(lean_object* v_t_1559_, lean_object* v_notification_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1559_, v_notification_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim(lean_object* v_motive_1562_, lean_object* v_t_1563_, lean_object* v_h_1564_, lean_object* v_notification_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1563_, v_notification_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(lean_object* v_t_1567_, lean_object* v_response_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1567_, v_response_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim(lean_object* v_motive_1570_, lean_object* v_t_1571_, lean_object* v_h_1572_, lean_object* v_response_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1571_, v_response_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim___redArg(lean_object* v_t_1575_, lean_object* v_responseError_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1575_, v_responseError_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim(lean_object* v_motive_1578_, lean_object* v_t_1579_, lean_object* v_h_1580_, lean_object* v_responseError_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1579_, v_responseError_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_metaData(lean_object* v_x_1588_){
_start:
{
switch(lean_obj_tag(v_x_1588_))
{
case 0:
{
lean_object* v_id_1589_; lean_object* v_method_1590_; lean_object* v___x_1591_; 
v_id_1589_ = lean_ctor_get(v_x_1588_, 0);
lean_inc(v_id_1589_);
v_method_1590_ = lean_ctor_get(v_x_1588_, 1);
lean_inc_ref(v_method_1590_);
lean_dec_ref_known(v_x_1588_, 3);
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v_id_1589_);
lean_ctor_set(v___x_1591_, 1, v_method_1590_);
return v___x_1591_;
}
case 1:
{
lean_object* v_method_1592_; lean_object* v___x_1593_; 
v_method_1592_ = lean_ctor_get(v_x_1588_, 0);
lean_inc_ref(v_method_1592_);
lean_dec_ref_known(v_x_1588_, 2);
v___x_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1593_, 0, v_method_1592_);
return v___x_1593_;
}
case 2:
{
lean_object* v_id_1594_; lean_object* v___x_1595_; 
v_id_1594_ = lean_ctor_get(v_x_1588_, 0);
lean_inc(v_id_1594_);
lean_dec_ref_known(v_x_1588_, 2);
v___x_1595_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1595_, 0, v_id_1594_);
return v___x_1595_;
}
default: 
{
lean_object* v_id_1596_; uint8_t v_code_1597_; lean_object* v_message_1598_; lean_object* v_data_x3f_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_id_1596_ = lean_ctor_get(v_x_1588_, 0);
v_code_1597_ = lean_ctor_get_uint8(v_x_1588_, sizeof(void*)*3);
v_message_1598_ = lean_ctor_get(v_x_1588_, 1);
v_data_x3f_1599_ = lean_ctor_get(v_x_1588_, 2);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_x_1588_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v_x_1588_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_data_x3f_1599_);
lean_inc(v_message_1598_);
lean_inc(v_id_1596_);
lean_dec(v_x_1588_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_id_1596_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_message_1598_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_data_x3f_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1605_, sizeof(void*)*3, v_code_1597_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_toMessage(lean_object* v_x_1607_){
_start:
{
switch(lean_obj_tag(v_x_1607_))
{
case 0:
{
lean_object* v_id_1608_; lean_object* v_method_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v_id_1608_ = lean_ctor_get(v_x_1607_, 0);
lean_inc(v_id_1608_);
v_method_1609_ = lean_ctor_get(v_x_1607_, 1);
lean_inc_ref(v_method_1609_);
lean_dec_ref_known(v_x_1607_, 2);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1611_, 0, v_id_1608_);
lean_ctor_set(v___x_1611_, 1, v_method_1609_);
lean_ctor_set(v___x_1611_, 2, v___x_1610_);
return v___x_1611_;
}
case 1:
{
lean_object* v_method_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_method_1612_ = lean_ctor_get(v_x_1607_, 0);
lean_inc_ref(v_method_1612_);
lean_dec_ref_known(v_x_1607_, 1);
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1614_, 0, v_method_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
return v___x_1614_;
}
case 2:
{
lean_object* v_id_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v_id_1615_ = lean_ctor_get(v_x_1607_, 0);
lean_inc(v_id_1615_);
lean_dec_ref_known(v_x_1607_, 1);
v___x_1616_ = lean_box(0);
v___x_1617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1617_, 0, v_id_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
return v___x_1617_;
}
default: 
{
lean_object* v_id_1618_; uint8_t v_code_1619_; lean_object* v_message_1620_; lean_object* v_data_x3f_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
v_id_1618_ = lean_ctor_get(v_x_1607_, 0);
v_code_1619_ = lean_ctor_get_uint8(v_x_1607_, sizeof(void*)*3);
v_message_1620_ = lean_ctor_get(v_x_1607_, 1);
v_data_x3f_1621_ = lean_ctor_get(v_x_1607_, 2);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_x_1607_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v_x_1607_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_data_x3f_1621_);
lean_inc(v_message_1620_);
lean_inc(v_id_1618_);
lean_dec(v_x_1607_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_id_1618_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_message_1620_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_data_x3f_1621_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*3, v_code_1619_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(lean_object* v_a_1632_){
_start:
{
lean_object* v_fst_1633_; lean_object* v_snd_1634_; lean_object* v___x_1635_; uint8_t v_decide_1636_; 
v_fst_1633_ = lean_ctor_get(v_a_1632_, 0);
v_snd_1634_ = lean_ctor_get(v_a_1632_, 1);
v___x_1635_ = lean_string_utf8_byte_size(v_fst_1633_);
v_decide_1636_ = lean_nat_dec_eq(v_snd_1634_, v___x_1635_);
if (v_decide_1636_ == 0)
{
uint32_t v___x_1637_; uint32_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1637_ = lean_string_utf8_get_fast(v_fst_1633_, v_snd_1634_);
v___x_1638_ = 34;
v___x_1639_ = lean_uint32_dec_eq(v___x_1637_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1));
v___x_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1641_, 0, v_a_1632_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
return v___x_1641_;
}
else
{
lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1651_; 
lean_inc(v_snd_1634_);
lean_inc(v_fst_1633_);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_a_1632_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; lean_object* v_unused_1653_; 
v_unused_1652_ = lean_ctor_get(v_a_1632_, 1);
lean_dec(v_unused_1652_);
v_unused_1653_ = lean_ctor_get(v_a_1632_, 0);
lean_dec(v_unused_1653_);
v___x_1643_ = v_a_1632_;
v_isShared_1644_ = v_isSharedCheck_1651_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v_a_1632_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1651_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = lean_string_utf8_next_fast(v_fst_1633_, v_snd_1634_);
lean_dec(v_snd_1634_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 1, v___x_1645_);
v___x_1647_ = v___x_1643_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_fst_1633_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_1649_ = l_Lean_Json_Parser_strCore(v___x_1648_, v___x_1647_);
return v___x_1649_;
}
}
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_box(0);
v___x_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1655_, 0, v_a_1632_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
return v___x_1655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(lean_object* v_a_1656_){
_start:
{
lean_object* v___x_1657_; 
lean_inc_ref(v_a_1656_);
v___x_1657_ = l_Lean_Json_Parser_num(v_a_1656_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_pos_1658_; lean_object* v_res_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v_a_1656_);
v_pos_1658_ = lean_ctor_get(v___x_1657_, 0);
v_res_1659_ = lean_ctor_get(v___x_1657_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1661_ = v___x_1657_;
v_isShared_1662_ = v_isSharedCheck_1667_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_res_1659_);
lean_inc(v_pos_1658_);
lean_dec(v___x_1657_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1667_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_res_1659_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 1, v___x_1663_);
v___x_1665_ = v___x_1661_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_pos_1658_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v_pos_1668_; lean_object* v_err_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1722_; 
v_pos_1668_ = lean_ctor_get(v___x_1657_, 0);
v_err_1669_ = lean_ctor_get(v___x_1657_, 1);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1671_ = v___x_1657_;
v_isShared_1672_ = v_isSharedCheck_1722_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_err_1669_);
lean_inc(v_pos_1668_);
lean_dec(v___x_1657_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1722_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v_snd_1673_; lean_object* v_snd_1674_; uint8_t v_decide_1675_; 
v_snd_1673_ = lean_ctor_get(v_a_1656_, 1);
lean_inc(v_snd_1673_);
lean_dec_ref(v_a_1656_);
v_snd_1674_ = lean_ctor_get(v_pos_1668_, 1);
v_decide_1675_ = lean_nat_dec_eq(v_snd_1673_, v_snd_1674_);
lean_dec(v_snd_1673_);
if (v_decide_1675_ == 0)
{
lean_object* v___x_1677_; 
if (v_isShared_1672_ == 0)
{
v___x_1677_ = v___x_1671_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_pos_1668_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_err_1669_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
else
{
lean_object* v___x_1679_; 
lean_inc(v_snd_1674_);
lean_del_object(v___x_1671_);
lean_dec(v_err_1669_);
v___x_1679_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v_pos_1668_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_pos_1680_; lean_object* v_res_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_snd_1674_);
v_pos_1680_ = lean_ctor_get(v___x_1679_, 0);
v_res_1681_ = lean_ctor_get(v___x_1679_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1683_ = v___x_1679_;
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_res_1681_);
lean_inc(v_pos_1680_);
lean_dec(v___x_1679_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_res_1681_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 1, v___x_1685_);
v___x_1687_ = v___x_1683_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_pos_1680_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
else
{
lean_object* v_pos_1690_; lean_object* v_err_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1721_; 
v_pos_1690_ = lean_ctor_get(v___x_1679_, 0);
v_err_1691_ = lean_ctor_get(v___x_1679_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1693_ = v___x_1679_;
v_isShared_1694_ = v_isSharedCheck_1721_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_err_1691_);
lean_inc(v_pos_1690_);
lean_dec(v___x_1679_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1721_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_snd_1695_; uint8_t v_decide_1696_; 
v_snd_1695_ = lean_ctor_get(v_pos_1690_, 1);
v_decide_1696_ = lean_nat_dec_eq(v_snd_1674_, v_snd_1695_);
lean_dec(v_snd_1674_);
if (v_decide_1696_ == 0)
{
lean_object* v___x_1698_; 
if (v_isShared_1694_ == 0)
{
v___x_1698_ = v___x_1693_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_pos_1690_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_err_1691_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_del_object(v___x_1693_);
lean_dec(v_err_1691_);
v___x_1700_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___x_1701_ = l_Std_Internal_Parsec_String_pstring(v___x_1700_, v_pos_1690_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_pos_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1710_; 
v_pos_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v___x_1701_, 1);
lean_dec(v_unused_1711_);
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_pos_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = lean_box(2);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_pos_1702_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
else
{
lean_object* v_pos_1712_; lean_object* v_err_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v_pos_1712_ = lean_ctor_get(v___x_1701_, 0);
v_err_1713_ = lean_ctor_get(v___x_1701_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1701_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_err_1713_);
lean_inc(v_pos_1712_);
lean_dec(v___x_1701_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_pos_1712_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_err_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object* v_j_1723_, lean_object* v_k_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_Json_getObjValD(v_j_1723_, v_k_1724_);
switch(lean_obj_tag(v___x_1725_))
{
case 3:
{
lean_object* v_s_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
v_s_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_s_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set_tag(v___x_1728_, 0);
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_s_1726_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
}
case 2:
{
lean_object* v_n_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1743_; 
v_n_1735_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1737_ = v___x_1725_;
v_isShared_1738_ = v_isSharedCheck_1743_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_n_1735_);
lean_dec(v___x_1725_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1743_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 1);
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_n_1735_);
v___x_1740_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
}
}
default: 
{
lean_object* v___x_1744_; 
lean_dec(v___x_1725_);
v___x_1744_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object* v_j_1745_, lean_object* v_k_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_j_1745_, v_k_1746_);
lean_dec_ref(v_k_1746_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object* v_j_1748_, lean_object* v_k_1749_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_Json_getObjValD(v_j_1748_, v_k_1749_);
if (lean_obj_tag(v___x_1752_) == 2)
{
lean_object* v_n_1753_; lean_object* v_mantissa_1754_; lean_object* v_exponent_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_n_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc_ref(v_n_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v_mantissa_1754_ = lean_ctor_get(v_n_1753_, 0);
lean_inc(v_mantissa_1754_);
v_exponent_1755_ = lean_ctor_get(v_n_1753_, 1);
lean_inc(v_exponent_1755_);
lean_dec_ref(v_n_1753_);
v___x_1756_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_1757_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_1759_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_1761_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_1763_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_1765_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_1767_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_1769_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_1771_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_1773_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_1775_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_1777_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_1779_ = lean_int_dec_eq(v_mantissa_1754_, v___x_1778_);
lean_dec(v_mantissa_1754_);
if (v___x_1779_ == 0)
{
lean_dec(v_exponent_1755_);
goto v___jp_1750_;
}
else
{
lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = lean_unsigned_to_nat(0u);
v___x_1781_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1780_);
lean_dec(v_exponent_1755_);
if (v___x_1781_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1782_; 
v___x_1782_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_1782_;
}
}
}
else
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
lean_dec(v_mantissa_1754_);
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1783_);
lean_dec(v_exponent_1755_);
if (v___x_1784_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1785_; 
v___x_1785_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_1785_;
}
}
}
else
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
lean_dec(v_mantissa_1754_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1786_);
lean_dec(v_exponent_1755_);
if (v___x_1787_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1788_; 
v___x_1788_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_1788_;
}
}
}
else
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
lean_dec(v_mantissa_1754_);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1789_);
lean_dec(v_exponent_1755_);
if (v___x_1790_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1791_; 
v___x_1791_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_1791_;
}
}
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
lean_dec(v_mantissa_1754_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1792_);
lean_dec(v_exponent_1755_);
if (v___x_1793_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1794_; 
v___x_1794_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_1794_;
}
}
}
else
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
lean_dec(v_mantissa_1754_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1795_);
lean_dec(v_exponent_1755_);
if (v___x_1796_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1797_; 
v___x_1797_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_1797_;
}
}
}
else
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
lean_dec(v_mantissa_1754_);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1798_);
lean_dec(v_exponent_1755_);
if (v___x_1799_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_1800_;
}
}
}
else
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
lean_dec(v_mantissa_1754_);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1801_);
lean_dec(v_exponent_1755_);
if (v___x_1802_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1803_; 
v___x_1803_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_1803_;
}
}
}
else
{
lean_object* v___x_1804_; uint8_t v___x_1805_; 
lean_dec(v_mantissa_1754_);
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1804_);
lean_dec(v_exponent_1755_);
if (v___x_1805_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1806_; 
v___x_1806_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_1806_;
}
}
}
else
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
lean_dec(v_mantissa_1754_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1807_);
lean_dec(v_exponent_1755_);
if (v___x_1808_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1809_; 
v___x_1809_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_1809_;
}
}
}
else
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
lean_dec(v_mantissa_1754_);
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1810_);
lean_dec(v_exponent_1755_);
if (v___x_1811_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1812_; 
v___x_1812_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_1812_;
}
}
}
else
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
lean_dec(v_mantissa_1754_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_nat_dec_eq(v_exponent_1755_, v___x_1813_);
lean_dec(v_exponent_1755_);
if (v___x_1814_ == 0)
{
goto v___jp_1750_;
}
else
{
lean_object* v___x_1815_; 
v___x_1815_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_1815_;
}
}
}
else
{
lean_dec(v___x_1752_);
goto v___jp_1750_;
}
v___jp_1750_:
{
lean_object* v___x_1751_; 
v___x_1751_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object* v_j_1816_, lean_object* v_k_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_j_1816_, v_k_1817_);
lean_dec_ref(v_k_1817_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object* v_j_1819_, lean_object* v_k_1820_){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = l_Lean_Json_getObjValD(v_j_1819_, v_k_1820_);
v___x_1822_ = l_Lean_Json_getStr_x3f(v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object* v_j_1823_, lean_object* v_k_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_j_1823_, v_k_1824_);
lean_dec_ref(v_k_1824_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object* v_input_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v_fst_1862_; lean_object* v_snd_1863_; lean_object* v___x_1864_; uint8_t v_decide_1865_; 
v_fst_1862_ = lean_ctor_get(v_a_1836_, 0);
v_snd_1863_ = lean_ctor_get(v_a_1836_, 1);
v___x_1864_ = lean_string_utf8_byte_size(v_fst_1862_);
v_decide_1865_ = lean_nat_dec_eq(v_snd_1863_, v___x_1864_);
if (v_decide_1865_ == 0)
{
lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_2215_; 
lean_inc(v_snd_1863_);
lean_inc(v_fst_1862_);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_a_1836_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; lean_object* v_unused_2217_; 
v_unused_2216_ = lean_ctor_get(v_a_1836_, 1);
lean_dec(v_unused_2216_);
v_unused_2217_ = lean_ctor_get(v_a_1836_, 0);
lean_dec(v_unused_2217_);
v___x_1867_ = v_a_1836_;
v_isShared_1868_ = v_isSharedCheck_2215_;
goto v_resetjp_1866_;
}
else
{
lean_dec(v_a_1836_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_2215_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1869_ = lean_string_utf8_next_fast(v_fst_1862_, v_snd_1863_);
lean_dec(v_snd_1863_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v___x_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_fst_1862_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_2214_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; 
v___x_1872_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1871_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_pos_1873_; lean_object* v_res_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_2204_; 
v_pos_1873_ = lean_ctor_get(v___x_1872_, 0);
v_res_1874_ = lean_ctor_get(v___x_1872_, 1);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_1876_ = v___x_1872_;
v_isShared_1877_ = v_isSharedCheck_2204_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_res_1874_);
lean_inc(v_pos_1873_);
lean_dec(v___x_1872_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_2204_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v_fst_1878_; lean_object* v_snd_1879_; lean_object* v___x_1880_; uint8_t v_decide_1881_; 
v_fst_1878_ = lean_ctor_get(v_pos_1873_, 0);
v_snd_1879_ = lean_ctor_get(v_pos_1873_, 1);
v___x_1880_ = lean_string_utf8_byte_size(v_fst_1878_);
v_decide_1881_ = lean_nat_dec_eq(v_snd_1879_, v___x_1880_);
if (v_decide_1881_ == 0)
{
lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_2197_; 
lean_inc(v_snd_1879_);
lean_inc(v_fst_1878_);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_pos_1873_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; lean_object* v_unused_2199_; 
v_unused_2198_ = lean_ctor_get(v_pos_1873_, 1);
lean_dec(v_unused_2198_);
v_unused_2199_ = lean_ctor_get(v_pos_1873_, 0);
lean_dec(v_unused_2199_);
v___x_1883_ = v_pos_1873_;
v_isShared_1884_ = v_isSharedCheck_2197_;
goto v_resetjp_1882_;
}
else
{
lean_dec(v_pos_1873_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_2197_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_string_utf8_next_fast(v_fst_1878_, v_snd_1879_);
lean_dec(v_snd_1879_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 1, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_fst_1878_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_2196_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v_id_1889_; uint8_t v_code_1890_; lean_object* v_message_1891_; lean_object* v_data_x3f_1892_; lean_object* v_a_1901_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
v___x_1907_ = lean_string_dec_eq(v_res_1874_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1908_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
v___x_1909_ = lean_string_dec_eq(v_res_1874_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1910_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1911_ = lean_string_dec_eq(v_res_1874_, v___x_1910_);
lean_dec(v_res_1874_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_del_object(v___x_1876_);
lean_dec_ref(v_input_1835_);
v___x_1912_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3));
v___x_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1887_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Json_parse(v_input_1835_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1923_; 
lean_del_object(v___x_1876_);
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1923_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1923_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 1);
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1887_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
return v___x_1921_;
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___x_1914_, 0);
lean_inc_n(v_a_1924_, 2);
lean_dec_ref_known(v___x_1914_, 1);
v___x_1925_ = l_Lean_Json_getObjVal_x3f(v_a_1924_, v___x_1908_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; 
lean_dec(v_a_1924_);
lean_del_object(v___x_1876_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v_a_1901_ = v_a_1926_;
goto v___jp_1900_;
}
else
{
lean_object* v_a_1927_; 
v_a_1927_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1925_, 1);
if (lean_obj_tag(v_a_1927_) == 3)
{
lean_object* v_s_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v_s_1928_ = lean_ctor_get(v_a_1927_, 0);
lean_inc_ref(v_s_1928_);
lean_dec_ref_known(v_a_1927_, 1);
v___x_1929_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1930_ = lean_string_dec_eq(v_s_1928_, v___x_1929_);
lean_dec_ref(v_s_1928_);
if (v___x_1930_ == 0)
{
lean_dec(v_a_1924_);
lean_del_object(v___x_1876_);
goto v___jp_1904_;
}
else
{
lean_object* v___x_1931_; 
lean_inc(v_a_1924_);
v___x_1931_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_1924_, v___x_1906_);
if (lean_obj_tag(v___x_1931_) == 0)
{
goto v___jp_1959_;
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1924_);
v___x_1965_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1924_, v___x_1964_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_dec_ref_known(v___x_1965_, 1);
goto v___jp_1959_;
}
else
{
lean_dec_ref_known(v___x_1965_, 1);
lean_dec_ref_known(v___x_1931_, 1);
lean_dec(v_a_1924_);
lean_del_object(v___x_1876_);
goto v___jp_1897_;
}
}
v___jp_1932_:
{
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1933_; 
lean_dec(v_a_1924_);
lean_del_object(v___x_1876_);
v_a_1933_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1931_, 1);
v_a_1901_ = v_a_1933_;
goto v___jp_1900_;
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1935_; 
v_a_1934_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1935_ = l_Lean_Json_getObjVal_x3f(v_a_1924_, v___x_1910_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; 
lean_dec(v_a_1934_);
lean_del_object(v___x_1876_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v_a_1901_ = v_a_1936_;
goto v___jp_1900_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_a_1937_ = lean_ctor_get(v___x_1935_, 0);
lean_inc_n(v_a_1937_, 2);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1938_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1939_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_1937_, v___x_1938_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; 
lean_dec(v_a_1937_);
lean_dec(v_a_1934_);
lean_del_object(v___x_1876_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v_a_1901_ = v_a_1940_;
goto v___jp_1900_;
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_a_1941_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1939_, 1);
v___x_1942_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1937_);
v___x_1943_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1937_, v___x_1942_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; 
lean_dec(v_a_1941_);
lean_dec(v_a_1937_);
lean_dec(v_a_1934_);
lean_del_object(v___x_1876_);
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v_a_1901_ = v_a_1944_;
goto v___jp_1900_;
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_a_1945_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1943_, 1);
v___x_1946_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1947_ = l_Lean_Json_getObjVal_x3f(v_a_1937_, v___x_1946_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v___x_1948_; uint8_t v___x_1949_; 
lean_dec_ref_known(v___x_1947_, 1);
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_unbox(v_a_1941_);
lean_dec(v_a_1941_);
v_id_1889_ = v_a_1934_;
v_code_1890_ = v___x_1949_;
v_message_1891_ = v_a_1945_;
v_data_x3f_1892_ = v___x_1948_;
goto v___jp_1888_;
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1958_; 
v_a_1950_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1952_ = v___x_1947_;
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1947_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
uint8_t v___x_1956_; 
v___x_1956_ = lean_unbox(v_a_1941_);
lean_dec(v_a_1941_);
v_id_1889_ = v_a_1934_;
v_code_1890_ = v___x_1956_;
v_message_1891_ = v_a_1945_;
v_data_x3f_1892_ = v___x_1955_;
goto v___jp_1888_;
}
}
}
}
}
}
}
}
v___jp_1959_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1924_);
v___x_1961_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1924_, v___x_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_dec_ref_known(v___x_1961_, 1);
if (lean_obj_tag(v___x_1931_) == 0)
{
goto v___jp_1932_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_1924_);
v___x_1963_ = l_Lean_Json_getObjVal_x3f(v_a_1924_, v___x_1962_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_dec_ref_known(v___x_1963_, 1);
goto v___jp_1932_;
}
else
{
lean_dec_ref_known(v___x_1963_, 1);
lean_dec_ref_known(v___x_1931_, 1);
lean_dec(v_a_1924_);
lean_del_object(v___x_1876_);
goto v___jp_1897_;
}
}
}
else
{
lean_dec_ref_known(v___x_1961_, 1);
lean_dec_ref(v___x_1931_);
lean_dec(v_a_1924_);
lean_del_object(v___x_1876_);
goto v___jp_1897_;
}
}
}
}
else
{
lean_dec(v_a_1927_);
lean_dec(v_a_1924_);
lean_del_object(v___x_1876_);
goto v___jp_1904_;
}
}
}
}
}
else
{
lean_object* v___x_1966_; 
lean_del_object(v___x_1876_);
lean_dec(v_res_1874_);
lean_dec_ref(v_input_1835_);
v___x_1966_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1887_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_pos_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2015_; 
v_pos_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v___x_1966_, 1);
lean_dec(v_unused_2016_);
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_2015_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_pos_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2015_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v_fst_1971_; lean_object* v_snd_1972_; uint8_t v___y_1974_; lean_object* v___x_2013_; uint8_t v_decide_2014_; 
v_fst_1971_ = lean_ctor_get(v_pos_1967_, 0);
v_snd_1972_ = lean_ctor_get(v_pos_1967_, 1);
v___x_2013_ = lean_string_utf8_byte_size(v_fst_1971_);
v_decide_2014_ = lean_nat_dec_eq(v_snd_1972_, v___x_2013_);
if (v_decide_2014_ == 0)
{
v___y_1974_ = v___x_1909_;
goto v___jp_1973_;
}
else
{
v___y_1974_ = v___x_1907_;
goto v___jp_1973_;
}
v___jp_1973_:
{
if (v___y_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1975_ = lean_box(0);
if (v_isShared_1970_ == 0)
{
lean_ctor_set_tag(v___x_1969_, 1);
lean_ctor_set(v___x_1969_, 1, v___x_1975_);
v___x_1977_ = v___x_1969_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_pos_1967_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
else
{
lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2010_; 
lean_inc(v_snd_1972_);
lean_inc(v_fst_1971_);
lean_del_object(v___x_1969_);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_pos_1967_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; lean_object* v_unused_2012_; 
v_unused_2011_ = lean_ctor_get(v_pos_1967_, 1);
lean_dec(v_unused_2011_);
v_unused_2012_ = lean_ctor_get(v_pos_1967_, 0);
lean_dec(v_unused_2012_);
v___x_1980_ = v_pos_1967_;
v_isShared_1981_ = v_isSharedCheck_2010_;
goto v_resetjp_1979_;
}
else
{
lean_dec(v_pos_1967_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2010_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = lean_string_utf8_next_fast(v_fst_1971_, v_snd_1972_);
lean_dec(v_snd_1972_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v___x_1982_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_fst_1971_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_2009_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; 
v___x_1985_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1984_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_pos_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1998_; 
v_pos_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v___x_1985_, 1);
lean_dec(v_unused_1999_);
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_pos_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v_fst_1990_; lean_object* v_snd_1991_; lean_object* v___x_1992_; uint8_t v_decide_1993_; 
v_fst_1990_ = lean_ctor_get(v_pos_1986_, 0);
v_snd_1991_ = lean_ctor_get(v_pos_1986_, 1);
v___x_1992_ = lean_string_utf8_byte_size(v_fst_1990_);
v_decide_1993_ = lean_nat_dec_eq(v_snd_1991_, v___x_1992_);
if (v_decide_1993_ == 0)
{
lean_inc(v_snd_1991_);
lean_inc(v_fst_1990_);
lean_del_object(v___x_1988_);
lean_dec(v_pos_1986_);
v___y_1838_ = v_snd_1991_;
v___y_1839_ = v_fst_1990_;
goto v___jp_1837_;
}
else
{
if (v___x_1907_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = lean_box(0);
if (v_isShared_1989_ == 0)
{
lean_ctor_set_tag(v___x_1988_, 1);
lean_ctor_set(v___x_1988_, 1, v___x_1994_);
v___x_1996_ = v___x_1988_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_pos_1986_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
else
{
lean_inc(v_snd_1991_);
lean_inc(v_fst_1990_);
lean_del_object(v___x_1988_);
lean_dec(v_pos_1986_);
v___y_1838_ = v_snd_1991_;
v___y_1839_ = v_fst_1990_;
goto v___jp_1837_;
}
}
}
}
else
{
lean_object* v_pos_2000_; lean_object* v_err_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
v_pos_2000_ = lean_ctor_get(v___x_1985_, 0);
v_err_2001_ = lean_ctor_get(v___x_1985_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1985_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_err_2001_);
lean_inc(v_pos_2000_);
lean_dec(v___x_1985_);
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
}
}
}
}
else
{
lean_object* v_pos_2017_; lean_object* v_err_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
v_pos_2017_ = lean_ctor_get(v___x_1966_, 0);
v_err_2018_ = lean_ctor_get(v___x_1966_, 1);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_1966_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_err_2018_);
lean_inc(v_pos_2017_);
lean_dec(v___x_1966_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_pos_2017_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_err_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
else
{
lean_object* v___x_2026_; 
lean_del_object(v___x_1876_);
lean_dec(v_res_1874_);
lean_dec_ref(v_input_1835_);
v___x_2026_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(v___x_1887_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_pos_2027_; lean_object* v_res_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2186_; 
v_pos_2027_ = lean_ctor_get(v___x_2026_, 0);
v_res_2028_ = lean_ctor_get(v___x_2026_, 1);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2030_ = v___x_2026_;
v_isShared_2031_ = v_isSharedCheck_2186_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_res_2028_);
lean_inc(v_pos_2027_);
lean_dec(v___x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2186_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v_fst_2037_; lean_object* v_snd_2038_; lean_object* v___x_2039_; uint8_t v_decide_2040_; 
v_fst_2037_ = lean_ctor_get(v_pos_2027_, 0);
v_snd_2038_ = lean_ctor_get(v_pos_2027_, 1);
v___x_2039_ = lean_string_utf8_byte_size(v_fst_2037_);
v_decide_2040_ = lean_nat_dec_eq(v_snd_2038_, v___x_2039_);
if (v_decide_2040_ == 0)
{
if (v___x_1907_ == 0)
{
lean_dec(v_res_2028_);
goto v___jp_2032_;
}
else
{
lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2183_; 
lean_inc(v_snd_2038_);
lean_inc(v_fst_2037_);
lean_del_object(v___x_2030_);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_pos_2027_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; lean_object* v_unused_2185_; 
v_unused_2184_ = lean_ctor_get(v_pos_2027_, 1);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_pos_2027_, 0);
lean_dec(v_unused_2185_);
v___x_2042_ = v_pos_2027_;
v_isShared_2043_ = v_isSharedCheck_2183_;
goto v_resetjp_2041_;
}
else
{
lean_dec(v_pos_2027_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2183_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2044_ = lean_string_utf8_next_fast(v_fst_2037_, v_snd_2038_);
lean_dec(v_snd_2038_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 1, v___x_2044_);
v___x_2046_ = v___x_2042_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_fst_2037_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; 
v___x_2047_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2046_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_pos_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2171_; 
v_pos_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; 
v_unused_2172_ = lean_ctor_get(v___x_2047_, 1);
lean_dec(v_unused_2172_);
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2171_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_pos_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2171_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v_fst_2052_; lean_object* v_snd_2053_; lean_object* v___x_2054_; uint8_t v_decide_2055_; 
v_fst_2052_ = lean_ctor_get(v_pos_2048_, 0);
v_snd_2053_ = lean_ctor_get(v_pos_2048_, 1);
v___x_2054_ = lean_string_utf8_byte_size(v_fst_2052_);
v_decide_2055_ = lean_nat_dec_eq(v_snd_2053_, v___x_2054_);
if (v_decide_2055_ == 0)
{
lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2164_; 
lean_inc(v_snd_2053_);
lean_inc(v_fst_2052_);
lean_del_object(v___x_2050_);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_pos_2048_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; lean_object* v_unused_2166_; 
v_unused_2165_ = lean_ctor_get(v_pos_2048_, 1);
lean_dec(v_unused_2165_);
v_unused_2166_ = lean_ctor_get(v_pos_2048_, 0);
lean_dec(v_unused_2166_);
v___x_2057_ = v_pos_2048_;
v_isShared_2058_ = v_isSharedCheck_2164_;
goto v_resetjp_2056_;
}
else
{
lean_dec(v_pos_2048_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2164_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = lean_string_utf8_next_fast(v_fst_2052_, v_snd_2053_);
lean_dec(v_snd_2053_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v___x_2059_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_fst_2052_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2062_; 
v___x_2062_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2061_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_pos_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2152_; 
v_pos_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v___x_2062_, 1);
lean_dec(v_unused_2153_);
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2152_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_pos_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2152_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v_fst_2067_; lean_object* v_snd_2068_; lean_object* v___x_2069_; uint8_t v_decide_2070_; 
v_fst_2067_ = lean_ctor_get(v_pos_2063_, 0);
v_snd_2068_ = lean_ctor_get(v_pos_2063_, 1);
v___x_2069_ = lean_string_utf8_byte_size(v_fst_2067_);
v_decide_2070_ = lean_nat_dec_eq(v_snd_2068_, v___x_2069_);
if (v_decide_2070_ == 0)
{
lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2145_; 
lean_inc(v_snd_2068_);
lean_inc(v_fst_2067_);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_pos_2063_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; lean_object* v_unused_2147_; 
v_unused_2146_ = lean_ctor_get(v_pos_2063_, 1);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_pos_2063_, 0);
lean_dec(v_unused_2147_);
v___x_2072_ = v_pos_2063_;
v_isShared_2073_ = v_isSharedCheck_2145_;
goto v_resetjp_2071_;
}
else
{
lean_dec(v_pos_2063_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2145_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = lean_string_utf8_next_fast(v_fst_2067_, v_snd_2068_);
lean_dec(v_snd_2068_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 1, v___x_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_fst_2067_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2077_; 
v___x_2077_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2076_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_pos_2078_; lean_object* v_res_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2134_; 
v_pos_2078_ = lean_ctor_get(v___x_2077_, 0);
v_res_2079_ = lean_ctor_get(v___x_2077_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2081_ = v___x_2077_;
v_isShared_2082_ = v_isSharedCheck_2134_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_res_2079_);
lean_inc(v_pos_2078_);
lean_dec(v___x_2077_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2134_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2089_ = lean_string_dec_eq(v_res_2079_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
lean_del_object(v___x_2081_);
v___x_2090_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2091_ = lean_string_dec_eq(v_res_2079_, v___x_2090_);
lean_dec(v_res_2079_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
lean_dec(v_res_2028_);
v___x_2092_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5));
if (v_isShared_2066_ == 0)
{
lean_ctor_set_tag(v___x_2065_, 1);
lean_ctor_set(v___x_2065_, 1, v___x_2092_);
lean_ctor_set(v___x_2065_, 0, v_pos_2078_);
v___x_2094_ = v___x_2065_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_pos_2078_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2096_, 0, v_res_2028_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 1, v___x_2096_);
lean_ctor_set(v___x_2065_, 0, v_pos_2078_);
v___x_2098_ = v___x_2065_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_pos_2078_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
else
{
lean_object* v_fst_2100_; lean_object* v_snd_2101_; lean_object* v___x_2102_; uint8_t v_decide_2103_; 
lean_dec(v_res_2079_);
lean_del_object(v___x_2065_);
v_fst_2100_ = lean_ctor_get(v_pos_2078_, 0);
v_snd_2101_ = lean_ctor_get(v_pos_2078_, 1);
v___x_2102_ = lean_string_utf8_byte_size(v_fst_2100_);
v_decide_2103_ = lean_nat_dec_eq(v_snd_2101_, v___x_2102_);
if (v_decide_2103_ == 0)
{
if (v___x_2089_ == 0)
{
lean_dec(v_res_2028_);
goto v___jp_2083_;
}
else
{
lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2131_; 
lean_inc(v_snd_2101_);
lean_inc(v_fst_2100_);
lean_del_object(v___x_2081_);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_pos_2078_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; lean_object* v_unused_2133_; 
v_unused_2132_ = lean_ctor_get(v_pos_2078_, 1);
lean_dec(v_unused_2132_);
v_unused_2133_ = lean_ctor_get(v_pos_2078_, 0);
lean_dec(v_unused_2133_);
v___x_2105_ = v_pos_2078_;
v_isShared_2106_ = v_isSharedCheck_2131_;
goto v_resetjp_2104_;
}
else
{
lean_dec(v_pos_2078_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2131_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = lean_string_utf8_next_fast(v_fst_2100_, v_snd_2101_);
lean_dec(v_snd_2101_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 1, v___x_2107_);
v___x_2109_ = v___x_2105_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_fst_2100_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; 
v___x_2110_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2109_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_pos_2111_; lean_object* v_res_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2120_; 
v_pos_2111_ = lean_ctor_get(v___x_2110_, 0);
v_res_2112_ = lean_ctor_get(v___x_2110_, 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2114_ = v___x_2110_;
v_isShared_2115_ = v_isSharedCheck_2120_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_res_2112_);
lean_inc(v_pos_2111_);
lean_dec(v___x_2110_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2120_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v_res_2028_);
lean_ctor_set(v___x_2116_, 1, v_res_2112_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 1, v___x_2116_);
v___x_2118_ = v___x_2114_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_pos_2111_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
else
{
lean_object* v_pos_2121_; lean_object* v_err_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_res_2028_);
v_pos_2121_ = lean_ctor_get(v___x_2110_, 0);
v_err_2122_ = lean_ctor_get(v___x_2110_, 1);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2110_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_err_2122_);
lean_inc(v_pos_2121_);
lean_dec(v___x_2110_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_pos_2121_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_err_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2028_);
goto v___jp_2083_;
}
}
v___jp_2083_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = lean_box(0);
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 1);
lean_ctor_set(v___x_2081_, 1, v___x_2084_);
v___x_2086_ = v___x_2081_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_pos_2078_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_pos_2135_; lean_object* v_err_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_del_object(v___x_2065_);
lean_dec(v_res_2028_);
v_pos_2135_ = lean_ctor_get(v___x_2077_, 0);
v_err_2136_ = lean_ctor_get(v___x_2077_, 1);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2077_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_err_2136_);
lean_inc(v_pos_2135_);
lean_dec(v___x_2077_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_pos_2135_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_err_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec(v_res_2028_);
v___x_2148_ = lean_box(0);
if (v_isShared_2066_ == 0)
{
lean_ctor_set_tag(v___x_2065_, 1);
lean_ctor_set(v___x_2065_, 1, v___x_2148_);
v___x_2150_ = v___x_2065_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_pos_2063_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
else
{
lean_object* v_pos_2154_; lean_object* v_err_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_res_2028_);
v_pos_2154_ = lean_ctor_get(v___x_2062_, 0);
v_err_2155_ = lean_ctor_get(v___x_2062_, 1);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2062_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_err_2155_);
lean_inc(v_pos_2154_);
lean_dec(v___x_2062_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_pos_2154_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_err_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
lean_dec(v_res_2028_);
v___x_2167_ = lean_box(0);
if (v_isShared_2051_ == 0)
{
lean_ctor_set_tag(v___x_2050_, 1);
lean_ctor_set(v___x_2050_, 1, v___x_2167_);
v___x_2169_ = v___x_2050_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_pos_2048_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_pos_2173_; lean_object* v_err_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_res_2028_);
v_pos_2173_ = lean_ctor_get(v___x_2047_, 0);
v_err_2174_ = lean_ctor_get(v___x_2047_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2047_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_err_2174_);
lean_inc(v_pos_2173_);
lean_dec(v___x_2047_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_pos_2173_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_err_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2028_);
goto v___jp_2032_;
}
v___jp_2032_:
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2033_ = lean_box(0);
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 1);
lean_ctor_set(v___x_2030_, 1, v___x_2033_);
v___x_2035_ = v___x_2030_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_pos_2027_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2033_);
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
else
{
lean_object* v_pos_2187_; lean_object* v_err_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
v_pos_2187_ = lean_ctor_get(v___x_2026_, 0);
v_err_2188_ = lean_ctor_get(v___x_2026_, 1);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2026_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_err_2188_);
lean_inc(v_pos_2187_);
lean_dec(v___x_2026_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_pos_2187_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_err_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
v___jp_1888_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1893_, 0, v_id_1889_);
lean_ctor_set(v___x_1893_, 1, v_message_1891_);
lean_ctor_set(v___x_1893_, 2, v_data_x3f_1892_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3, v_code_1890_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 1, v___x_1893_);
lean_ctor_set(v___x_1876_, 0, v___x_1887_);
v___x_1895_ = v___x_1876_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
v___jp_1897_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1));
v___x_1899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1887_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
return v___x_1899_;
}
v___jp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1902_, 0, v_a_1901_);
v___x_1903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1887_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
return v___x_1903_;
}
v___jp_1904_:
{
lean_object* v___x_1905_; 
v___x_1905_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_1901_ = v___x_1905_;
goto v___jp_1900_;
}
}
}
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
lean_dec(v_res_1874_);
lean_dec_ref(v_input_1835_);
v___x_2200_ = lean_box(0);
if (v_isShared_1877_ == 0)
{
lean_ctor_set_tag(v___x_1876_, 1);
lean_ctor_set(v___x_1876_, 1, v___x_2200_);
v___x_2202_ = v___x_1876_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_pos_1873_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_pos_2205_; lean_object* v_err_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec_ref(v_input_1835_);
v_pos_2205_ = lean_ctor_get(v___x_1872_, 0);
v_err_2206_ = lean_ctor_get(v___x_1872_, 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_1872_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_err_2206_);
lean_inc(v_pos_2205_);
lean_dec(v___x_1872_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_pos_2205_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_err_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec_ref(v_input_1835_);
v___x_2218_ = lean_box(0);
v___x_2219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2219_, 0, v_a_1836_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
return v___x_2219_;
}
v___jp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_string_utf8_next_fast(v___y_1839_, v___y_1838_);
lean_dec(v___y_1838_);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___y_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1841_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_pos_1843_; lean_object* v_res_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1852_; 
v_pos_1843_ = lean_ctor_get(v___x_1842_, 0);
v_res_1844_ = lean_ctor_get(v___x_1842_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1846_ = v___x_1842_;
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_res_1844_);
lean_inc(v_pos_1843_);
lean_dec(v___x_1842_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1848_, 0, v_res_1844_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___x_1848_);
v___x_1850_ = v___x_1846_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_pos_1843_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
else
{
lean_object* v_pos_1853_; lean_object* v_err_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_pos_1853_ = lean_ctor_get(v___x_1842_, 0);
v_err_1854_ = lean_ctor_get(v___x_1842_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1842_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_err_1854_);
lean_inc(v_pos_1853_);
lean_dec(v___x_1842_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_pos_1853_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_err_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object* v_input_2220_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_inc_ref(v_input_2220_);
v___x_2221_ = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser), 2, 1);
lean_closure_set(v___x_2221_, 0, v_input_2220_);
v___x_2222_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2221_, v_input_2220_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx(uint8_t v_x_2223_){
_start:
{
if (v_x_2223_ == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_unsigned_to_nat(0u);
return v___x_2224_;
}
else
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_unsigned_to_nat(1u);
return v___x_2225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___boxed(lean_object* v_x_2226_){
_start:
{
uint8_t v_x_boxed_2227_; lean_object* v_res_2228_; 
v_x_boxed_2227_ = lean_unbox(v_x_2226_);
v_res_2228_ = l_Lean_JsonRpc_MessageDirection_ctorIdx(v_x_boxed_2227_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object* v_k_2229_){
_start:
{
lean_inc(v_k_2229_);
return v_k_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object* v_k_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(v_k_2230_);
lean_dec(v_k_2230_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object* v_motive_2232_, lean_object* v_ctorIdx_2233_, uint8_t v_t_2234_, lean_object* v_h_2235_, lean_object* v_k_2236_){
_start:
{
lean_inc(v_k_2236_);
return v_k_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object* v_motive_2237_, lean_object* v_ctorIdx_2238_, lean_object* v_t_2239_, lean_object* v_h_2240_, lean_object* v_k_2241_){
_start:
{
uint8_t v_t_boxed_2242_; lean_object* v_res_2243_; 
v_t_boxed_2242_ = lean_unbox(v_t_2239_);
v_res_2243_ = l_Lean_JsonRpc_MessageDirection_ctorElim(v_motive_2237_, v_ctorIdx_2238_, v_t_boxed_2242_, v_h_2240_, v_k_2241_);
lean_dec(v_k_2241_);
lean_dec(v_ctorIdx_2238_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object* v_clientToServer_2244_){
_start:
{
lean_inc(v_clientToServer_2244_);
return v_clientToServer_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object* v_clientToServer_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(v_clientToServer_2245_);
lean_dec(v_clientToServer_2245_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object* v_motive_2247_, uint8_t v_t_2248_, lean_object* v_h_2249_, lean_object* v_clientToServer_2250_){
_start:
{
lean_inc(v_clientToServer_2250_);
return v_clientToServer_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object* v_motive_2251_, lean_object* v_t_2252_, lean_object* v_h_2253_, lean_object* v_clientToServer_2254_){
_start:
{
uint8_t v_t_boxed_2255_; lean_object* v_res_2256_; 
v_t_boxed_2255_ = lean_unbox(v_t_2252_);
v_res_2256_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(v_motive_2251_, v_t_boxed_2255_, v_h_2253_, v_clientToServer_2254_);
lean_dec(v_clientToServer_2254_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object* v_serverToClient_2257_){
_start:
{
lean_inc(v_serverToClient_2257_);
return v_serverToClient_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object* v_serverToClient_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(v_serverToClient_2258_);
lean_dec(v_serverToClient_2258_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object* v_motive_2260_, uint8_t v_t_2261_, lean_object* v_h_2262_, lean_object* v_serverToClient_2263_){
_start:
{
lean_inc(v_serverToClient_2263_);
return v_serverToClient_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object* v_motive_2264_, lean_object* v_t_2265_, lean_object* v_h_2266_, lean_object* v_serverToClient_2267_){
_start:
{
uint8_t v_t_boxed_2268_; lean_object* v_res_2269_; 
v_t_boxed_2268_ = lean_unbox(v_t_2265_);
v_res_2269_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(v_motive_2264_, v_t_boxed_2268_, v_h_2266_, v_serverToClient_2267_);
lean_dec(v_serverToClient_2267_);
return v_res_2269_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default(void){
_start:
{
uint8_t v___x_2270_; 
v___x_2270_ = 0;
return v___x_2270_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection(void){
_start:
{
uint8_t v___x_2271_; 
v___x_2271_ = 0;
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object* v_json_2286_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l_Lean_Json_getTag_x3f(v_json_2286_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v___x_2288_; 
v___x_2288_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1));
return v___x_2288_;
}
else
{
lean_object* v_val_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v_val_2289_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_val_2289_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2290_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2));
v___x_2291_ = lean_string_dec_eq(v_val_2289_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; uint8_t v___x_2293_; 
v___x_2292_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3));
v___x_2293_ = lean_string_dec_eq(v_val_2289_, v___x_2292_);
lean_dec(v_val_2289_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; 
v___x_2294_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5));
return v___x_2294_;
}
else
{
lean_object* v___x_2295_; 
v___x_2295_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6));
return v___x_2295_;
}
}
else
{
lean_object* v___x_2296_; 
lean_dec(v_val_2289_);
v___x_2296_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7));
return v___x_2296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t v_x_2303_){
_start:
{
if (v_x_2303_ == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0));
return v___x_2304_;
}
else
{
lean_object* v___x_2305_; 
v___x_2305_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1));
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object* v_x_2306_){
_start:
{
uint8_t v_x_44__boxed_2307_; lean_object* v_res_2308_; 
v_x_44__boxed_2307_ = lean_unbox(v_x_2306_);
v_res_2308_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_x_44__boxed_2307_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx(uint8_t v_x_2311_){
_start:
{
switch(v_x_2311_)
{
case 0:
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_unsigned_to_nat(0u);
return v___x_2312_;
}
case 1:
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_unsigned_to_nat(1u);
return v___x_2313_;
}
case 2:
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_unsigned_to_nat(2u);
return v___x_2314_;
}
default: 
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_unsigned_to_nat(3u);
return v___x_2315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___boxed(lean_object* v_x_2316_){
_start:
{
uint8_t v_x_boxed_2317_; lean_object* v_res_2318_; 
v_x_boxed_2317_ = lean_unbox(v_x_2316_);
v_res_2318_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_boxed_2317_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object* v_k_2319_){
_start:
{
lean_inc(v_k_2319_);
return v_k_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object* v_k_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_JsonRpc_MessageKind_ctorElim___redArg(v_k_2320_);
lean_dec(v_k_2320_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object* v_motive_2322_, lean_object* v_ctorIdx_2323_, uint8_t v_t_2324_, lean_object* v_h_2325_, lean_object* v_k_2326_){
_start:
{
lean_inc(v_k_2326_);
return v_k_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object* v_motive_2327_, lean_object* v_ctorIdx_2328_, lean_object* v_t_2329_, lean_object* v_h_2330_, lean_object* v_k_2331_){
_start:
{
uint8_t v_t_boxed_2332_; lean_object* v_res_2333_; 
v_t_boxed_2332_ = lean_unbox(v_t_2329_);
v_res_2333_ = l_Lean_JsonRpc_MessageKind_ctorElim(v_motive_2327_, v_ctorIdx_2328_, v_t_boxed_2332_, v_h_2330_, v_k_2331_);
lean_dec(v_k_2331_);
lean_dec(v_ctorIdx_2328_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object* v_request_2334_){
_start:
{
lean_inc(v_request_2334_);
return v_request_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object* v_request_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Lean_JsonRpc_MessageKind_request_elim___redArg(v_request_2335_);
lean_dec(v_request_2335_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object* v_motive_2337_, uint8_t v_t_2338_, lean_object* v_h_2339_, lean_object* v_request_2340_){
_start:
{
lean_inc(v_request_2340_);
return v_request_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object* v_motive_2341_, lean_object* v_t_2342_, lean_object* v_h_2343_, lean_object* v_request_2344_){
_start:
{
uint8_t v_t_boxed_2345_; lean_object* v_res_2346_; 
v_t_boxed_2345_ = lean_unbox(v_t_2342_);
v_res_2346_ = l_Lean_JsonRpc_MessageKind_request_elim(v_motive_2341_, v_t_boxed_2345_, v_h_2343_, v_request_2344_);
lean_dec(v_request_2344_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object* v_notification_2347_){
_start:
{
lean_inc(v_notification_2347_);
return v_notification_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object* v_notification_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_JsonRpc_MessageKind_notification_elim___redArg(v_notification_2348_);
lean_dec(v_notification_2348_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object* v_motive_2350_, uint8_t v_t_2351_, lean_object* v_h_2352_, lean_object* v_notification_2353_){
_start:
{
lean_inc(v_notification_2353_);
return v_notification_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object* v_motive_2354_, lean_object* v_t_2355_, lean_object* v_h_2356_, lean_object* v_notification_2357_){
_start:
{
uint8_t v_t_boxed_2358_; lean_object* v_res_2359_; 
v_t_boxed_2358_ = lean_unbox(v_t_2355_);
v_res_2359_ = l_Lean_JsonRpc_MessageKind_notification_elim(v_motive_2354_, v_t_boxed_2358_, v_h_2356_, v_notification_2357_);
lean_dec(v_notification_2357_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object* v_response_2360_){
_start:
{
lean_inc(v_response_2360_);
return v_response_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object* v_response_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_JsonRpc_MessageKind_response_elim___redArg(v_response_2361_);
lean_dec(v_response_2361_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object* v_motive_2363_, uint8_t v_t_2364_, lean_object* v_h_2365_, lean_object* v_response_2366_){
_start:
{
lean_inc(v_response_2366_);
return v_response_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object* v_motive_2367_, lean_object* v_t_2368_, lean_object* v_h_2369_, lean_object* v_response_2370_){
_start:
{
uint8_t v_t_boxed_2371_; lean_object* v_res_2372_; 
v_t_boxed_2371_ = lean_unbox(v_t_2368_);
v_res_2372_ = l_Lean_JsonRpc_MessageKind_response_elim(v_motive_2367_, v_t_boxed_2371_, v_h_2369_, v_response_2370_);
lean_dec(v_response_2370_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object* v_responseError_2373_){
_start:
{
lean_inc(v_responseError_2373_);
return v_responseError_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object* v_responseError_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(v_responseError_2374_);
lean_dec(v_responseError_2374_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object* v_motive_2376_, uint8_t v_t_2377_, lean_object* v_h_2378_, lean_object* v_responseError_2379_){
_start:
{
lean_inc(v_responseError_2379_);
return v_responseError_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object* v_motive_2380_, lean_object* v_t_2381_, lean_object* v_h_2382_, lean_object* v_responseError_2383_){
_start:
{
uint8_t v_t_boxed_2384_; lean_object* v_res_2385_; 
v_t_boxed_2384_ = lean_unbox(v_t_2381_);
v_res_2385_ = l_Lean_JsonRpc_MessageKind_responseError_elim(v_motive_2380_, v_t_boxed_2384_, v_h_2382_, v_responseError_2383_);
lean_dec(v_responseError_2383_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object* v_json_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_Json_getTag_x3f(v_json_2406_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; 
v___x_2408_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0));
return v___x_2408_;
}
else
{
lean_object* v_val_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v_val_2409_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_val_2409_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2410_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1));
v___x_2411_ = lean_string_dec_eq(v_val_2409_, v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2));
v___x_2413_ = lean_string_dec_eq(v_val_2409_, v___x_2412_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2414_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3));
v___x_2415_ = lean_string_dec_eq(v_val_2409_, v___x_2414_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2416_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4));
v___x_2417_ = lean_string_dec_eq(v_val_2409_, v___x_2416_);
lean_dec(v_val_2409_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5));
return v___x_2418_;
}
else
{
lean_object* v___x_2419_; 
v___x_2419_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6));
return v___x_2419_;
}
}
else
{
lean_object* v___x_2420_; 
lean_dec(v_val_2409_);
v___x_2420_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7));
return v___x_2420_;
}
}
else
{
lean_object* v___x_2421_; 
lean_dec(v_val_2409_);
v___x_2421_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8));
return v___x_2421_;
}
}
else
{
lean_object* v___x_2422_; 
lean_dec(v_val_2409_);
v___x_2422_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9));
return v___x_2422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t v_x_2433_){
_start:
{
switch(v_x_2433_)
{
case 0:
{
lean_object* v___x_2434_; 
v___x_2434_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0));
return v___x_2434_;
}
case 1:
{
lean_object* v___x_2435_; 
v___x_2435_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1));
return v___x_2435_;
}
case 2:
{
lean_object* v___x_2436_; 
v___x_2436_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2));
return v___x_2436_;
}
default: 
{
lean_object* v___x_2437_; 
v___x_2437_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3));
return v___x_2437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object* v_x_2438_){
_start:
{
uint8_t v_x_84__boxed_2439_; lean_object* v_res_2440_; 
v_x_84__boxed_2439_ = lean_unbox(v_x_2438_);
v_res_2440_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_x_84__boxed_2439_);
return v_res_2440_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object* v_x_2443_){
_start:
{
switch(lean_obj_tag(v_x_2443_))
{
case 0:
{
uint8_t v___x_2444_; 
v___x_2444_ = 0;
return v___x_2444_;
}
case 1:
{
uint8_t v___x_2445_; 
v___x_2445_ = 1;
return v___x_2445_;
}
case 2:
{
uint8_t v___x_2446_; 
v___x_2446_ = 2;
return v___x_2446_;
}
default: 
{
uint8_t v___x_2447_; 
v___x_2447_ = 3;
return v___x_2447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object* v_x_2448_){
_start:
{
uint8_t v_res_2449_; lean_object* v_r_2450_; 
v_res_2449_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_x_2448_);
lean_dec_ref(v_x_2448_);
v_r_2450_ = lean_box(v_res_2449_);
return v_r_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(lean_object* v_j_2451_, lean_object* v_k_2452_){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = l_Lean_Json_getObjValD(v_j_2451_, v_k_2452_);
v___x_2454_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0___boxed(lean_object* v_j_2455_, lean_object* v_k_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_j_2455_, v_k_2456_);
lean_dec_ref(v_k_2456_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage(lean_object* v_h_2460_, lean_object* v_nBytes_2461_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_IO_FS_Stream_readJson(v_h_2460_, v_nBytes_2461_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2583_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2583_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2583_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
uint8_t v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v_a_2483_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_a_2464_);
v___x_2495_ = l_Lean_Json_getObjVal_x3f(v_a_2464_, v___x_2494_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; 
lean_del_object(v___x_2466_);
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
v_a_2483_ = v_a_2496_;
goto v___jp_2482_;
}
else
{
lean_object* v_a_2497_; 
v_a_2497_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2495_, 1);
if (lean_obj_tag(v_a_2497_) == 3)
{
lean_object* v_s_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v_s_2498_ = lean_ctor_get(v_a_2497_, 0);
lean_inc_ref(v_s_2498_);
lean_dec_ref_known(v_a_2497_, 1);
v___x_2499_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_2500_ = lean_string_dec_eq(v_s_2498_, v___x_2499_);
lean_dec_ref(v_s_2498_);
if (v___x_2500_ == 0)
{
lean_del_object(v___x_2466_);
goto v___jp_2492_;
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_a_2464_);
v___x_2502_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_2464_, v___x_2501_);
if (lean_obj_tag(v___x_2502_) == 0)
{
goto v___jp_2531_;
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v_a_2558_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2558_);
v___x_2559_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2464_);
v___x_2560_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2464_, v___x_2559_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_dec_ref_known(v___x_2560_, 1);
lean_dec(v_a_2558_);
goto v___jp_2531_;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2582_; 
lean_dec_ref_known(v___x_2502_, 1);
lean_del_object(v___x_2466_);
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2563_ = v___x_2560_;
v_isShared_2564_ = v_isSharedCheck_2582_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2582_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___y_2566_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2572_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2464_, v___x_2571_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v___x_2573_; 
lean_dec_ref_known(v___x_2572_, 1);
v___x_2573_ = lean_box(0);
v___y_2566_ = v___x_2573_;
goto v___jp_2565_;
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v_a_2574_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2572_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2572_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
v___y_2566_ = v___x_2579_;
goto v___jp_2565_;
}
}
}
v___jp_2565_:
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
v___x_2567_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2567_, 0, v_a_2558_);
lean_ctor_set(v___x_2567_, 1, v_a_2561_);
lean_ctor_set(v___x_2567_, 2, v___y_2566_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set_tag(v___x_2563_, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2567_);
v___x_2569_ = v___x_2563_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
v___jp_2503_:
{
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2504_; 
lean_del_object(v___x_2466_);
v_a_2504_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2502_, 1);
v_a_2483_ = v_a_2504_;
goto v___jp_2482_;
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_a_2505_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2502_, 1);
v___x_2506_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
lean_inc(v_a_2464_);
v___x_2507_ = l_Lean_Json_getObjVal_x3f(v_a_2464_, v___x_2506_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; 
lean_dec(v_a_2505_);
lean_del_object(v___x_2466_);
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v_a_2483_ = v_a_2508_;
goto v___jp_2482_;
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_a_2509_ = lean_ctor_get(v___x_2507_, 0);
lean_inc_n(v_a_2509_, 2);
lean_dec_ref_known(v___x_2507_, 1);
v___x_2510_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_2511_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_2509_, v___x_2510_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; 
lean_dec(v_a_2509_);
lean_dec(v_a_2505_);
lean_del_object(v___x_2466_);
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v_a_2483_ = v_a_2512_;
goto v___jp_2482_;
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_a_2513_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2511_, 1);
v___x_2514_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_2509_);
v___x_2515_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2509_, v___x_2514_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; 
lean_dec(v_a_2513_);
lean_dec(v_a_2509_);
lean_dec(v_a_2505_);
lean_del_object(v___x_2466_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v_a_2483_ = v_a_2516_;
goto v___jp_2482_;
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec(v_a_2464_);
v_a_2517_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2518_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2519_ = l_Lean_Json_getObjVal_x3f(v_a_2509_, v___x_2518_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v___x_2520_; uint8_t v___x_2521_; 
lean_dec_ref_known(v___x_2519_, 1);
v___x_2520_ = lean_box(0);
v___x_2521_ = lean_unbox(v_a_2513_);
lean_dec(v_a_2513_);
v___y_2469_ = v___x_2521_;
v___y_2470_ = v_a_2517_;
v___y_2471_ = v_a_2505_;
v___y_2472_ = v___x_2520_;
goto v___jp_2468_;
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2530_; 
v_a_2522_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2524_ = v___x_2519_;
v_isShared_2525_ = v_isSharedCheck_2530_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2519_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2530_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
uint8_t v___x_2528_; 
v___x_2528_ = lean_unbox(v_a_2513_);
lean_dec(v_a_2513_);
v___y_2469_ = v___x_2528_;
v___y_2470_ = v_a_2517_;
v___y_2471_ = v_a_2505_;
v___y_2472_ = v___x_2527_;
goto v___jp_2468_;
}
}
}
}
}
}
}
}
v___jp_2531_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2464_);
v___x_2533_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2464_, v___x_2532_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_dec_ref_known(v___x_2533_, 1);
if (lean_obj_tag(v___x_2502_) == 0)
{
goto v___jp_2503_;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_a_2534_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2534_);
v___x_2535_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_2464_);
v___x_2536_ = l_Lean_Json_getObjVal_x3f(v_a_2464_, v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_dec_ref_known(v___x_2536_, 1);
lean_dec(v_a_2534_);
goto v___jp_2503_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2545_; 
lean_dec_ref_known(v___x_2502_, 1);
lean_del_object(v___x_2466_);
lean_dec(v_a_2464_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2545_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2545_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2541_, 0, v_a_2534_);
lean_ctor_set(v___x_2541_, 1, v_a_2537_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set_tag(v___x_2539_, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2541_);
v___x_2543_ = v___x_2539_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_dec_ref(v___x_2502_);
lean_del_object(v___x_2466_);
v_a_2546_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2547_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2548_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2464_, v___x_2547_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v___x_2549_; 
lean_dec_ref_known(v___x_2548_, 1);
v___x_2549_ = lean_box(0);
v___y_2478_ = v_a_2546_;
v___y_2479_ = v___x_2549_;
goto v___jp_2477_;
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
v_a_2550_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2548_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2548_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
v___y_2478_ = v_a_2546_;
v___y_2479_ = v___x_2555_;
goto v___jp_2477_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2497_);
lean_del_object(v___x_2466_);
goto v___jp_2492_;
}
}
v___jp_2468_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2473_, 0, v___y_2471_);
lean_ctor_set(v___x_2473_, 1, v___y_2470_);
lean_ctor_set(v___x_2473_, 2, v___y_2472_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*3, v___y_2469_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2473_);
v___x_2475_ = v___x_2466_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
v___jp_2477_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___y_2478_);
lean_ctor_set(v___x_2480_, 1, v___y_2479_);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
return v___x_2481_;
}
v___jp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2484_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__0));
v___x_2485_ = l_Lean_Json_compress(v_a_2464_);
v___x_2486_ = lean_string_append(v___x_2484_, v___x_2485_);
lean_dec_ref(v___x_2485_);
v___x_2487_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__1));
v___x_2488_ = lean_string_append(v___x_2486_, v___x_2487_);
v___x_2489_ = lean_string_append(v___x_2488_, v_a_2483_);
lean_dec_ref(v_a_2483_);
v___x_2490_ = lean_mk_io_user_error(v___x_2489_);
v___x_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
return v___x_2491_;
}
v___jp_2492_:
{
lean_object* v___x_2493_; 
v___x_2493_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_2483_ = v___x_2493_;
goto v___jp_2482_;
}
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
v_a_2584_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2463_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2463_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage___boxed(lean_object* v_h_2592_, lean_object* v_nBytes_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_IO_FS_Stream_readMessage(v_h_2592_, v_nBytes_2593_);
lean_dec(v_nBytes_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg(lean_object* v_h_2603_, lean_object* v_nBytes_2604_, lean_object* v_expectedMethod_2605_, lean_object* v_inst_2606_){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2609_ = l_Lean_IO_FS_Stream_readMessage(v_h_2603_, v_nBytes_2604_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2795_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2795_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2795_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
if (lean_obj_tag(v_a_2610_) == 0)
{
lean_object* v_id_2614_; lean_object* v_method_2615_; lean_object* v_params_x3f_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2655_; 
v_id_2614_ = lean_ctor_get(v_a_2610_, 0);
v_method_2615_ = lean_ctor_get(v_a_2610_, 1);
v_params_x3f_2616_ = lean_ctor_get(v_a_2610_, 2);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_a_2610_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2618_ = v_a_2610_;
v_isShared_2619_ = v_isSharedCheck_2655_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_params_x3f_2616_);
lean_inc(v_method_2615_);
lean_inc(v_id_2614_);
lean_dec(v_a_2610_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2655_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
uint8_t v___x_2620_; 
v___x_2620_ = lean_string_dec_eq(v_method_2615_, v_expectedMethod_2605_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
lean_del_object(v___x_2618_);
lean_dec(v_params_x3f_2616_);
lean_dec(v_id_2614_);
lean_dec_ref(v_inst_2606_);
v___x_2621_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2622_ = lean_string_append(v___x_2621_, v_expectedMethod_2605_);
lean_dec_ref(v_expectedMethod_2605_);
v___x_2623_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2624_ = lean_string_append(v___x_2622_, v___x_2623_);
v___x_2625_ = lean_string_append(v___x_2624_, v_method_2615_);
lean_dec_ref(v_method_2615_);
v___x_2626_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2627_ = lean_string_append(v___x_2625_, v___x_2626_);
v___x_2628_ = lean_mk_io_user_error(v___x_2627_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set_tag(v___x_2612_, 1);
lean_ctor_set(v___x_2612_, 0, v___x_2628_);
v___x_2630_ = v___x_2612_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_dec_ref(v_method_2615_);
v___x_2632_ = l_Lean_Option_toJson___redArg(v___x_2608_, v_params_x3f_2616_);
lean_inc(v___x_2632_);
v___x_2633_ = lean_apply_1(v_inst_2606_, v___x_2632_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
lean_del_object(v___x_2618_);
lean_dec(v_id_2614_);
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v___x_2635_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2636_ = l_Lean_Json_compress(v___x_2632_);
v___x_2637_ = lean_string_append(v___x_2635_, v___x_2636_);
lean_dec_ref(v___x_2636_);
v___x_2638_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2639_ = lean_string_append(v___x_2637_, v___x_2638_);
v___x_2640_ = lean_string_append(v___x_2639_, v_expectedMethod_2605_);
lean_dec_ref(v_expectedMethod_2605_);
v___x_2641_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2642_ = lean_string_append(v___x_2640_, v___x_2641_);
v___x_2643_ = lean_string_append(v___x_2642_, v_a_2634_);
lean_dec(v_a_2634_);
v___x_2644_ = lean_mk_io_user_error(v___x_2643_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set_tag(v___x_2612_, 1);
lean_ctor_set(v___x_2612_, 0, v___x_2644_);
v___x_2646_ = v___x_2612_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; 
lean_dec(v___x_2632_);
v_a_2648_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2633_, 1);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 2, v_a_2648_);
lean_ctor_set(v___x_2618_, 1, v_expectedMethod_2605_);
v___x_2650_ = v___x_2618_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_id_2614_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_expectedMethod_2605_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_a_2648_);
v___x_2650_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2652_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___x_2650_);
v___x_2652_ = v___x_2612_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___y_2659_; 
lean_dec_ref(v_inst_2606_);
lean_dec_ref(v_expectedMethod_2605_);
v___x_2656_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__6));
v___x_2657_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2610_))
{
case 0:
{
lean_object* v_id_2670_; lean_object* v_method_2671_; lean_object* v_params_x3f_2672_; lean_object* v___x_2673_; lean_object* v___y_2675_; 
v_id_2670_ = lean_ctor_get(v_a_2610_, 0);
lean_inc(v_id_2670_);
v_method_2671_ = lean_ctor_get(v_a_2610_, 1);
lean_inc_ref(v_method_2671_);
v_params_x3f_2672_ = lean_ctor_get(v_a_2610_, 2);
lean_inc(v_params_x3f_2672_);
lean_dec_ref_known(v_a_2610_, 3);
v___x_2673_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2670_) == 0)
{
lean_object* v_s_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_s_2686_ = lean_ctor_get(v_id_2670_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_id_2670_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v_id_2670_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_s_2686_);
lean_dec(v_id_2670_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set_tag(v___x_2688_, 3);
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_s_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
v___y_2675_ = v___x_2691_;
goto v___jp_2674_;
}
}
}
else
{
lean_object* v_n_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
v_n_2694_ = lean_ctor_get(v_id_2670_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_id_2670_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v_id_2670_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_n_2694_);
lean_dec(v_id_2670_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set_tag(v___x_2696_, 2);
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_n_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
v___y_2675_ = v___x_2699_;
goto v___jp_2674_;
}
}
}
v___jp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2673_);
lean_ctor_set(v___x_2676_, 1, v___y_2675_);
v___x_2677_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2678_, 0, v_method_2671_);
v___x_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = lean_box(0);
v___x_2681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
v___x_2682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2676_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2684_ = l_Lean_Json_opt___redArg(v___x_2608_, v___x_2683_, v_params_x3f_2672_);
v___x_2685_ = l_List_appendTR___redArg(v___x_2682_, v___x_2684_);
v___y_2659_ = v___x_2685_;
goto v___jp_2658_;
}
}
case 1:
{
lean_object* v_method_2702_; lean_object* v_params_x3f_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_method_2702_ = lean_ctor_get(v_a_2610_, 0);
lean_inc_ref(v_method_2702_);
v_params_x3f_2703_ = lean_ctor_get(v_a_2610_, 1);
lean_inc(v_params_x3f_2703_);
lean_dec_ref_known(v_a_2610_, 2);
v___x_2704_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2705_, 0, v_method_2702_);
v___x_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2708_ = l_Lean_Json_opt___redArg(v___x_2608_, v___x_2707_, v_params_x3f_2703_);
v___x_2709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2706_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___y_2659_ = v___x_2709_;
goto v___jp_2658_;
}
case 2:
{
lean_object* v_id_2710_; lean_object* v_result_2711_; lean_object* v___x_2712_; lean_object* v___y_2714_; 
v_id_2710_ = lean_ctor_get(v_a_2610_, 0);
lean_inc(v_id_2710_);
v_result_2711_ = lean_ctor_get(v_a_2610_, 1);
lean_inc(v_result_2711_);
lean_dec_ref_known(v_a_2610_, 2);
v___x_2712_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2710_) == 0)
{
lean_object* v_s_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
v_s_2721_ = lean_ctor_get(v_id_2710_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_id_2710_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v_id_2710_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_s_2721_);
lean_dec(v_id_2710_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
lean_ctor_set_tag(v___x_2723_, 3);
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_s_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
v___y_2714_ = v___x_2726_;
goto v___jp_2713_;
}
}
}
else
{
lean_object* v_n_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
v_n_2729_ = lean_ctor_get(v_id_2710_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_id_2710_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v_id_2710_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_n_2729_);
lean_dec(v_id_2710_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
lean_ctor_set_tag(v___x_2731_, 2);
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_n_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
v___y_2714_ = v___x_2734_;
goto v___jp_2713_;
}
}
}
v___jp_2713_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2712_);
lean_ctor_set(v___x_2715_, 1, v___y_2714_);
v___x_2716_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v_result_2711_);
v___x_2718_ = lean_box(0);
v___x_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2715_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___y_2659_ = v___x_2720_;
goto v___jp_2658_;
}
}
default: 
{
lean_object* v_id_2737_; uint8_t v_code_2738_; lean_object* v_message_2739_; lean_object* v_data_x3f_2740_; lean_object* v___x_2741_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___x_2761_; lean_object* v___y_2763_; 
v_id_2737_ = lean_ctor_get(v_a_2610_, 0);
lean_inc(v_id_2737_);
v_code_2738_ = lean_ctor_get_uint8(v_a_2610_, sizeof(void*)*3);
v_message_2739_ = lean_ctor_get(v_a_2610_, 1);
lean_inc_ref(v_message_2739_);
v_data_x3f_2740_ = lean_ctor_get(v_a_2610_, 2);
lean_inc(v_data_x3f_2740_);
lean_dec_ref_known(v_a_2610_, 3);
v___x_2741_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2761_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2737_) == 0)
{
lean_object* v_s_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
v_s_2779_ = lean_ctor_get(v_id_2737_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_id_2737_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v_id_2737_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_s_2779_);
lean_dec(v_id_2737_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set_tag(v___x_2781_, 3);
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_s_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
v___y_2763_ = v___x_2784_;
goto v___jp_2762_;
}
}
}
else
{
lean_object* v_n_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v_n_2787_ = lean_ctor_get(v_id_2737_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_id_2737_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v_id_2737_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_n_2787_);
lean_dec(v_id_2737_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set_tag(v___x_2789_, 2);
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_n_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
v___y_2763_ = v___x_2792_;
goto v___jp_2762_;
}
}
}
v___jp_2742_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_inc(v___y_2746_);
lean_inc_ref(v___y_2743_);
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___y_2743_);
lean_ctor_set(v___x_2747_, 1, v___y_2746_);
v___x_2748_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2749_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_message_2739_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_box(0);
v___x_2752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2747_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2755_ = l_Lean_Json_opt___redArg(v___x_2741_, v___x_2754_, v_data_x3f_2740_);
v___x_2756_ = l_List_appendTR___redArg(v___x_2753_, v___x_2755_);
v___x_2757_ = l_Lean_Json_mkObj(v___x_2756_);
lean_dec(v___x_2756_);
lean_inc_ref(v___y_2745_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___y_2745_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v___x_2751_);
v___x_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___y_2744_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___y_2659_ = v___x_2760_;
goto v___jp_2658_;
}
v___jp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2761_);
lean_ctor_set(v___x_2764_, 1, v___y_2763_);
v___x_2765_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2766_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2738_)
{
case 0:
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2767_;
goto v___jp_2742_;
}
case 1:
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2768_;
goto v___jp_2742_;
}
case 2:
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2769_;
goto v___jp_2742_;
}
case 3:
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2770_;
goto v___jp_2742_;
}
case 4:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2771_;
goto v___jp_2742_;
}
case 5:
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2772_;
goto v___jp_2742_;
}
case 6:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2773_;
goto v___jp_2742_;
}
case 7:
{
lean_object* v___x_2774_; 
v___x_2774_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2774_;
goto v___jp_2742_;
}
case 8:
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2775_;
goto v___jp_2742_;
}
case 9:
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2776_;
goto v___jp_2742_;
}
case 10:
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2777_;
goto v___jp_2742_;
}
default: 
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2743_ = v___x_2766_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2765_;
v___y_2746_ = v___x_2778_;
goto v___jp_2742_;
}
}
}
}
}
v___jp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; 
v___x_2660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2657_);
lean_ctor_set(v___x_2660_, 1, v___y_2659_);
v___x_2661_ = l_Lean_Json_mkObj(v___x_2660_);
lean_dec_ref_known(v___x_2660_, 2);
v___x_2662_ = l_Lean_Json_compress(v___x_2661_);
v___x_2663_ = lean_string_append(v___x_2656_, v___x_2662_);
lean_dec_ref(v___x_2662_);
v___x_2664_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2665_ = lean_string_append(v___x_2663_, v___x_2664_);
v___x_2666_ = lean_mk_io_user_error(v___x_2665_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set_tag(v___x_2612_, 1);
lean_ctor_set(v___x_2612_, 0, v___x_2666_);
v___x_2668_ = v___x_2612_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v_inst_2606_);
lean_dec_ref(v_expectedMethod_2605_);
v_a_2796_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2609_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2609_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* v_h_2804_, lean_object* v_nBytes_2805_, lean_object* v_expectedMethod_2806_, lean_object* v_inst_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2804_, v_nBytes_2805_, v_expectedMethod_2806_, v_inst_2807_);
lean_dec(v_nBytes_2805_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs(lean_object* v_h_2810_, lean_object* v_nBytes_2811_, lean_object* v_expectedMethod_2812_, lean_object* v_00_u03b1_2813_, lean_object* v_inst_2814_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2810_, v_nBytes_2811_, v_expectedMethod_2812_, v_inst_2814_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___boxed(lean_object* v_h_2817_, lean_object* v_nBytes_2818_, lean_object* v_expectedMethod_2819_, lean_object* v_00_u03b1_2820_, lean_object* v_inst_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_IO_FS_Stream_readRequestAs(v_h_2817_, v_nBytes_2818_, v_expectedMethod_2819_, v_00_u03b1_2820_, v_inst_2821_);
lean_dec(v_nBytes_2818_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg(lean_object* v_h_2825_, lean_object* v_nBytes_2826_, lean_object* v_expectedMethod_2827_, lean_object* v_inst_2828_){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2831_ = l_Lean_IO_FS_Stream_readMessage(v_h_2825_, v_nBytes_2826_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_3016_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_3016_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_3016_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
if (lean_obj_tag(v_a_2832_) == 1)
{
lean_object* v_method_2836_; lean_object* v_params_x3f_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2876_; 
v_method_2836_ = lean_ctor_get(v_a_2832_, 0);
v_params_x3f_2837_ = lean_ctor_get(v_a_2832_, 1);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_a_2832_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2839_ = v_a_2832_;
v_isShared_2840_ = v_isSharedCheck_2876_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_params_x3f_2837_);
lean_inc(v_method_2836_);
lean_dec(v_a_2832_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2876_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_string_dec_eq(v_method_2836_, v_expectedMethod_2827_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; 
lean_del_object(v___x_2839_);
lean_dec(v_params_x3f_2837_);
lean_dec_ref(v_inst_2828_);
v___x_2842_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2843_ = lean_string_append(v___x_2842_, v_expectedMethod_2827_);
lean_dec_ref(v_expectedMethod_2827_);
v___x_2844_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2845_ = lean_string_append(v___x_2843_, v___x_2844_);
v___x_2846_ = lean_string_append(v___x_2845_, v_method_2836_);
lean_dec_ref(v_method_2836_);
v___x_2847_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2848_ = lean_string_append(v___x_2846_, v___x_2847_);
v___x_2849_ = lean_mk_io_user_error(v___x_2848_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set_tag(v___x_2834_, 1);
lean_ctor_set(v___x_2834_, 0, v___x_2849_);
v___x_2851_ = v___x_2834_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
else
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_dec_ref(v_method_2836_);
v___x_2853_ = l_Lean_Option_toJson___redArg(v___x_2830_, v_params_x3f_2837_);
lean_inc(v___x_2853_);
v___x_2854_ = lean_apply_1(v_inst_2828_, v___x_2853_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
lean_del_object(v___x_2839_);
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2856_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2857_ = l_Lean_Json_compress(v___x_2853_);
v___x_2858_ = lean_string_append(v___x_2856_, v___x_2857_);
lean_dec_ref(v___x_2857_);
v___x_2859_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2860_ = lean_string_append(v___x_2858_, v___x_2859_);
v___x_2861_ = lean_string_append(v___x_2860_, v_expectedMethod_2827_);
lean_dec_ref(v_expectedMethod_2827_);
v___x_2862_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2863_ = lean_string_append(v___x_2861_, v___x_2862_);
v___x_2864_ = lean_string_append(v___x_2863_, v_a_2855_);
lean_dec(v_a_2855_);
v___x_2865_ = lean_mk_io_user_error(v___x_2864_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set_tag(v___x_2834_, 1);
lean_ctor_set(v___x_2834_, 0, v___x_2865_);
v___x_2867_ = v___x_2834_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; 
lean_dec(v___x_2853_);
v_a_2869_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2854_, 1);
if (v_isShared_2840_ == 0)
{
lean_ctor_set_tag(v___x_2839_, 0);
lean_ctor_set(v___x_2839_, 1, v_a_2869_);
lean_ctor_set(v___x_2839_, 0, v_expectedMethod_2827_);
v___x_2871_ = v___x_2839_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_expectedMethod_2827_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_a_2869_);
v___x_2871_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2873_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2871_);
v___x_2873_ = v___x_2834_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___y_2880_; 
lean_dec_ref(v_inst_2828_);
lean_dec_ref(v_expectedMethod_2827_);
v___x_2877_ = ((lean_object*)(l_Lean_IO_FS_Stream_readNotificationAs___redArg___closed__0));
v___x_2878_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2832_))
{
case 0:
{
lean_object* v_id_2891_; lean_object* v_method_2892_; lean_object* v_params_x3f_2893_; lean_object* v___x_2894_; lean_object* v___y_2896_; 
v_id_2891_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_id_2891_);
v_method_2892_ = lean_ctor_get(v_a_2832_, 1);
lean_inc_ref(v_method_2892_);
v_params_x3f_2893_ = lean_ctor_get(v_a_2832_, 2);
lean_inc(v_params_x3f_2893_);
lean_dec_ref_known(v_a_2832_, 3);
v___x_2894_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2891_) == 0)
{
lean_object* v_s_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
v_s_2907_ = lean_ctor_get(v_id_2891_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_id_2891_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v_id_2891_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_s_2907_);
lean_dec(v_id_2891_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set_tag(v___x_2909_, 3);
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_s_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
v___y_2896_ = v___x_2912_;
goto v___jp_2895_;
}
}
}
else
{
lean_object* v_n_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
v_n_2915_ = lean_ctor_get(v_id_2891_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_id_2891_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v_id_2891_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_n_2915_);
lean_dec(v_id_2891_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set_tag(v___x_2917_, 2);
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_n_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
v___y_2896_ = v___x_2920_;
goto v___jp_2895_;
}
}
}
v___jp_2895_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2894_);
lean_ctor_set(v___x_2897_, 1, v___y_2896_);
v___x_2898_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2899_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2899_, 0, v_method_2892_);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = lean_box(0);
v___x_2902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2900_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2897_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2905_ = l_Lean_Json_opt___redArg(v___x_2830_, v___x_2904_, v_params_x3f_2893_);
v___x_2906_ = l_List_appendTR___redArg(v___x_2903_, v___x_2905_);
v___y_2880_ = v___x_2906_;
goto v___jp_2879_;
}
}
case 1:
{
lean_object* v_method_2923_; lean_object* v_params_x3f_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_method_2923_ = lean_ctor_get(v_a_2832_, 0);
lean_inc_ref(v_method_2923_);
v_params_x3f_2924_ = lean_ctor_get(v_a_2832_, 1);
lean_inc(v_params_x3f_2924_);
lean_dec_ref_known(v_a_2832_, 2);
v___x_2925_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2926_, 0, v_method_2923_);
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2925_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2929_ = l_Lean_Json_opt___redArg(v___x_2830_, v___x_2928_, v_params_x3f_2924_);
v___x_2930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2927_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___y_2880_ = v___x_2930_;
goto v___jp_2879_;
}
case 2:
{
lean_object* v_id_2931_; lean_object* v_result_2932_; lean_object* v___x_2933_; lean_object* v___y_2935_; 
v_id_2931_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_id_2931_);
v_result_2932_ = lean_ctor_get(v_a_2832_, 1);
lean_inc(v_result_2932_);
lean_dec_ref_known(v_a_2832_, 2);
v___x_2933_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2931_) == 0)
{
lean_object* v_s_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
v_s_2942_ = lean_ctor_get(v_id_2931_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_id_2931_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v_id_2931_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_s_2942_);
lean_dec(v_id_2931_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set_tag(v___x_2944_, 3);
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_s_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
v___y_2935_ = v___x_2947_;
goto v___jp_2934_;
}
}
}
else
{
lean_object* v_n_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
v_n_2950_ = lean_ctor_get(v_id_2931_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_id_2931_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v_id_2931_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_n_2950_);
lean_dec(v_id_2931_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set_tag(v___x_2952_, 2);
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_n_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
v___y_2935_ = v___x_2955_;
goto v___jp_2934_;
}
}
}
v___jp_2934_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2933_);
lean_ctor_set(v___x_2936_, 1, v___y_2935_);
v___x_2937_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v_result_2932_);
v___x_2939_ = lean_box(0);
v___x_2940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2938_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2936_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
v___y_2880_ = v___x_2941_;
goto v___jp_2879_;
}
}
default: 
{
lean_object* v_id_2958_; uint8_t v_code_2959_; lean_object* v_message_2960_; lean_object* v_data_x3f_2961_; lean_object* v___x_2962_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___x_2982_; lean_object* v___y_2984_; 
v_id_2958_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_id_2958_);
v_code_2959_ = lean_ctor_get_uint8(v_a_2832_, sizeof(void*)*3);
v_message_2960_ = lean_ctor_get(v_a_2832_, 1);
lean_inc_ref(v_message_2960_);
v_data_x3f_2961_ = lean_ctor_get(v_a_2832_, 2);
lean_inc(v_data_x3f_2961_);
lean_dec_ref_known(v_a_2832_, 3);
v___x_2962_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2982_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2958_) == 0)
{
lean_object* v_s_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
v_s_3000_ = lean_ctor_get(v_id_2958_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_id_2958_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v_id_2958_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_s_3000_);
lean_dec(v_id_2958_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set_tag(v___x_3002_, 3);
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_s_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
v___y_2984_ = v___x_3005_;
goto v___jp_2983_;
}
}
}
else
{
lean_object* v_n_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
v_n_3008_ = lean_ctor_get(v_id_2958_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_id_2958_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v_id_2958_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_n_3008_);
lean_dec(v_id_2958_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
lean_ctor_set_tag(v___x_3010_, 2);
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_n_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
v___y_2984_ = v___x_3013_;
goto v___jp_2983_;
}
}
}
v___jp_2963_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_inc(v___y_2967_);
lean_inc_ref(v___y_2966_);
v___x_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___y_2966_);
lean_ctor_set(v___x_2968_, 1, v___y_2967_);
v___x_2969_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2970_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2970_, 0, v_message_2960_);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2969_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_box(0);
v___x_2973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2968_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2976_ = l_Lean_Json_opt___redArg(v___x_2962_, v___x_2975_, v_data_x3f_2961_);
v___x_2977_ = l_List_appendTR___redArg(v___x_2974_, v___x_2976_);
v___x_2978_ = l_Lean_Json_mkObj(v___x_2977_);
lean_dec(v___x_2977_);
lean_inc_ref(v___y_2964_);
v___x_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___y_2964_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
lean_ctor_set(v___x_2980_, 1, v___x_2972_);
v___x_2981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___y_2965_);
lean_ctor_set(v___x_2981_, 1, v___x_2980_);
v___y_2880_ = v___x_2981_;
goto v___jp_2879_;
}
v___jp_2983_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2982_);
lean_ctor_set(v___x_2985_, 1, v___y_2984_);
v___x_2986_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2987_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2959_)
{
case 0:
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2988_;
goto v___jp_2963_;
}
case 1:
{
lean_object* v___x_2989_; 
v___x_2989_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2989_;
goto v___jp_2963_;
}
case 2:
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2990_;
goto v___jp_2963_;
}
case 3:
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2991_;
goto v___jp_2963_;
}
case 4:
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2992_;
goto v___jp_2963_;
}
case 5:
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2993_;
goto v___jp_2963_;
}
case 6:
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2994_;
goto v___jp_2963_;
}
case 7:
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2995_;
goto v___jp_2963_;
}
case 8:
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2996_;
goto v___jp_2963_;
}
case 9:
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2997_;
goto v___jp_2963_;
}
case 10:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2998_;
goto v___jp_2963_;
}
default: 
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
v___y_2967_ = v___x_2999_;
goto v___jp_2963_;
}
}
}
}
}
v___jp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2878_);
lean_ctor_set(v___x_2881_, 1, v___y_2880_);
v___x_2882_ = l_Lean_Json_mkObj(v___x_2881_);
lean_dec_ref_known(v___x_2881_, 2);
v___x_2883_ = l_Lean_Json_compress(v___x_2882_);
v___x_2884_ = lean_string_append(v___x_2877_, v___x_2883_);
lean_dec_ref(v___x_2883_);
v___x_2885_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2886_ = lean_string_append(v___x_2884_, v___x_2885_);
v___x_2887_ = lean_mk_io_user_error(v___x_2886_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set_tag(v___x_2834_, 1);
lean_ctor_set(v___x_2834_, 0, v___x_2887_);
v___x_2889_ = v___x_2834_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec_ref(v_inst_2828_);
lean_dec_ref(v_expectedMethod_2827_);
v_a_3017_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_2831_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_2831_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* v_h_3025_, lean_object* v_nBytes_3026_, lean_object* v_expectedMethod_3027_, lean_object* v_inst_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3025_, v_nBytes_3026_, v_expectedMethod_3027_, v_inst_3028_);
lean_dec(v_nBytes_3026_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs(lean_object* v_h_3031_, lean_object* v_nBytes_3032_, lean_object* v_expectedMethod_3033_, lean_object* v_00_u03b1_3034_, lean_object* v_inst_3035_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3031_, v_nBytes_3032_, v_expectedMethod_3033_, v_inst_3035_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___boxed(lean_object* v_h_3038_, lean_object* v_nBytes_3039_, lean_object* v_expectedMethod_3040_, lean_object* v_00_u03b1_3041_, lean_object* v_inst_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_IO_FS_Stream_readNotificationAs(v_h_3038_, v_nBytes_3039_, v_expectedMethod_3040_, v_00_u03b1_3041_, v_inst_3042_);
lean_dec(v_nBytes_3039_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg(lean_object* v_h_3049_, lean_object* v_nBytes_3050_, lean_object* v_expectedID_3051_, lean_object* v_inst_3052_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Lean_IO_FS_Stream_readMessage(v_h_3049_, v_nBytes_3050_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3258_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3258_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3258_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___y_3060_; lean_object* v___y_3061_; 
if (lean_obj_tag(v_a_3055_) == 2)
{
lean_object* v_id_3067_; lean_object* v_result_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3119_; 
v_id_3067_ = lean_ctor_get(v_a_3055_, 0);
v_result_3068_ = lean_ctor_get(v_a_3055_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_a_3055_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3070_ = v_a_3055_;
v_isShared_3071_ = v_isSharedCheck_3119_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_result_3068_);
lean_inc(v_id_3067_);
lean_dec(v_a_3055_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3119_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
uint8_t v___x_3072_; 
v___x_3072_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3067_, v_expectedID_3051_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___y_3075_; 
lean_del_object(v___x_3070_);
lean_dec(v_result_3068_);
lean_dec_ref(v_inst_3052_);
v___x_3073_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__0));
switch(lean_obj_tag(v_expectedID_3051_))
{
case 0:
{
lean_object* v_s_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v_s_3085_ = lean_ctor_get(v_expectedID_3051_, 0);
lean_inc_ref(v_s_3085_);
lean_dec_ref_known(v_expectedID_3051_, 1);
v___x_3086_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3087_ = lean_string_append(v___x_3086_, v_s_3085_);
lean_dec_ref(v_s_3085_);
v___x_3088_ = lean_string_append(v___x_3087_, v___x_3086_);
v___y_3075_ = v___x_3088_;
goto v___jp_3074_;
}
case 1:
{
lean_object* v_n_3089_; lean_object* v___x_3090_; 
v_n_3089_ = lean_ctor_get(v_expectedID_3051_, 0);
lean_inc_ref(v_n_3089_);
lean_dec_ref_known(v_expectedID_3051_, 1);
v___x_3090_ = l_Lean_JsonNumber_toString(v_n_3089_);
v___y_3075_ = v___x_3090_;
goto v___jp_3074_;
}
default: 
{
lean_object* v___x_3091_; 
v___x_3091_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___y_3075_ = v___x_3091_;
goto v___jp_3074_;
}
}
v___jp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = lean_string_append(v___x_3073_, v___y_3075_);
lean_dec_ref(v___y_3075_);
v___x_3077_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__1));
v___x_3078_ = lean_string_append(v___x_3076_, v___x_3077_);
if (lean_obj_tag(v_id_3067_) == 0)
{
lean_object* v_s_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v_s_3079_ = lean_ctor_get(v_id_3067_, 0);
lean_inc_ref(v_s_3079_);
lean_dec_ref_known(v_id_3067_, 1);
v___x_3080_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3081_ = lean_string_append(v___x_3080_, v_s_3079_);
lean_dec_ref(v_s_3079_);
v___x_3082_ = lean_string_append(v___x_3081_, v___x_3080_);
v___y_3060_ = v___x_3078_;
v___y_3061_ = v___x_3082_;
goto v___jp_3059_;
}
else
{
lean_object* v_n_3083_; lean_object* v___x_3084_; 
v_n_3083_ = lean_ctor_get(v_id_3067_, 0);
lean_inc_ref(v_n_3083_);
lean_dec_ref_known(v_id_3067_, 1);
v___x_3084_ = l_Lean_JsonNumber_toString(v_n_3083_);
v___y_3060_ = v___x_3078_;
v___y_3061_ = v___x_3084_;
goto v___jp_3059_;
}
}
}
else
{
lean_object* v___x_3092_; 
lean_dec(v_id_3067_);
lean_del_object(v___x_3057_);
lean_inc(v_result_3068_);
v___x_3092_ = lean_apply_1(v_inst_3052_, v_result_3068_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3107_; 
lean_del_object(v___x_3070_);
lean_dec(v_expectedID_3051_);
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3095_ = v___x_3092_;
v_isShared_3096_ = v_isSharedCheck_3107_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3092_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3107_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3097_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__2));
v___x_3098_ = l_Lean_Json_compress(v_result_3068_);
v___x_3099_ = lean_string_append(v___x_3097_, v___x_3098_);
lean_dec_ref(v___x_3098_);
v___x_3100_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_3101_ = lean_string_append(v___x_3099_, v___x_3100_);
v___x_3102_ = lean_string_append(v___x_3101_, v_a_3093_);
lean_dec(v_a_3093_);
v___x_3103_ = lean_mk_io_user_error(v___x_3102_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set_tag(v___x_3095_, 1);
lean_ctor_set(v___x_3095_, 0, v___x_3103_);
v___x_3105_ = v___x_3095_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3118_; 
lean_dec(v_result_3068_);
v_a_3108_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3110_ = v___x_3092_;
v_isShared_3111_ = v_isSharedCheck_3118_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3092_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3118_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3071_ == 0)
{
lean_ctor_set_tag(v___x_3070_, 0);
lean_ctor_set(v___x_3070_, 1, v_a_3108_);
lean_ctor_set(v___x_3070_, 0, v_expectedID_3051_);
v___x_3113_ = v___x_3070_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_expectedID_3051_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3115_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set_tag(v___x_3110_, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3113_);
v___x_3115_ = v___x_3110_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___y_3124_; 
lean_del_object(v___x_3057_);
lean_dec_ref(v_inst_3052_);
lean_dec(v_expectedID_3051_);
v___x_3120_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__3));
v___x_3121_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_3122_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_3055_))
{
case 0:
{
lean_object* v_id_3133_; lean_object* v_method_3134_; lean_object* v_params_x3f_3135_; lean_object* v___x_3136_; lean_object* v___y_3138_; 
v_id_3133_ = lean_ctor_get(v_a_3055_, 0);
lean_inc(v_id_3133_);
v_method_3134_ = lean_ctor_get(v_a_3055_, 1);
lean_inc_ref(v_method_3134_);
v_params_x3f_3135_ = lean_ctor_get(v_a_3055_, 2);
lean_inc(v_params_x3f_3135_);
lean_dec_ref_known(v_a_3055_, 3);
v___x_3136_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3133_) == 0)
{
lean_object* v_s_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
v_s_3149_ = lean_ctor_get(v_id_3133_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_id_3133_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v_id_3133_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_s_3149_);
lean_dec(v_id_3133_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
lean_ctor_set_tag(v___x_3151_, 3);
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_s_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
v___y_3138_ = v___x_3154_;
goto v___jp_3137_;
}
}
}
else
{
lean_object* v_n_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
v_n_3157_ = lean_ctor_get(v_id_3133_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_id_3133_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v_id_3133_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_n_3157_);
lean_dec(v_id_3133_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
lean_ctor_set_tag(v___x_3159_, 2);
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_n_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
v___y_3138_ = v___x_3162_;
goto v___jp_3137_;
}
}
}
v___jp_3137_:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3136_);
lean_ctor_set(v___x_3139_, 1, v___y_3138_);
v___x_3140_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3141_, 0, v_method_3134_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_box(0);
v___x_3144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3139_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3147_ = l_Lean_Json_opt___redArg(v___x_3121_, v___x_3146_, v_params_x3f_3135_);
v___x_3148_ = l_List_appendTR___redArg(v___x_3145_, v___x_3147_);
v___y_3124_ = v___x_3148_;
goto v___jp_3123_;
}
}
case 1:
{
lean_object* v_method_3165_; lean_object* v_params_x3f_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_method_3165_ = lean_ctor_get(v_a_3055_, 0);
lean_inc_ref(v_method_3165_);
v_params_x3f_3166_ = lean_ctor_get(v_a_3055_, 1);
lean_inc(v_params_x3f_3166_);
lean_dec_ref_known(v_a_3055_, 2);
v___x_3167_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3168_, 0, v_method_3165_);
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3167_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3171_ = l_Lean_Json_opt___redArg(v___x_3121_, v___x_3170_, v_params_x3f_3166_);
v___x_3172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3169_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___y_3124_ = v___x_3172_;
goto v___jp_3123_;
}
case 2:
{
lean_object* v_id_3173_; lean_object* v_result_3174_; lean_object* v___x_3175_; lean_object* v___y_3177_; 
v_id_3173_ = lean_ctor_get(v_a_3055_, 0);
lean_inc(v_id_3173_);
v_result_3174_ = lean_ctor_get(v_a_3055_, 1);
lean_inc(v_result_3174_);
lean_dec_ref_known(v_a_3055_, 2);
v___x_3175_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3173_) == 0)
{
lean_object* v_s_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
v_s_3184_ = lean_ctor_get(v_id_3173_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_id_3173_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v_id_3173_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_s_3184_);
lean_dec(v_id_3173_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
lean_ctor_set_tag(v___x_3186_, 3);
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_s_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
v___y_3177_ = v___x_3189_;
goto v___jp_3176_;
}
}
}
else
{
lean_object* v_n_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
v_n_3192_ = lean_ctor_get(v_id_3173_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_id_3173_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v_id_3173_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_n_3192_);
lean_dec(v_id_3173_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
lean_ctor_set_tag(v___x_3194_, 2);
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_n_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
v___y_3177_ = v___x_3197_;
goto v___jp_3176_;
}
}
}
v___jp_3176_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3175_);
lean_ctor_set(v___x_3178_, 1, v___y_3177_);
v___x_3179_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
lean_ctor_set(v___x_3180_, 1, v_result_3174_);
v___x_3181_ = lean_box(0);
v___x_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3180_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3178_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___y_3124_ = v___x_3183_;
goto v___jp_3123_;
}
}
default: 
{
lean_object* v_id_3200_; uint8_t v_code_3201_; lean_object* v_message_3202_; lean_object* v_data_x3f_3203_; lean_object* v___x_3204_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___x_3224_; lean_object* v___y_3226_; 
v_id_3200_ = lean_ctor_get(v_a_3055_, 0);
lean_inc(v_id_3200_);
v_code_3201_ = lean_ctor_get_uint8(v_a_3055_, sizeof(void*)*3);
v_message_3202_ = lean_ctor_get(v_a_3055_, 1);
lean_inc_ref(v_message_3202_);
v_data_x3f_3203_ = lean_ctor_get(v_a_3055_, 2);
lean_inc(v_data_x3f_3203_);
lean_dec_ref_known(v_a_3055_, 3);
v___x_3204_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_3224_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3200_) == 0)
{
lean_object* v_s_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
v_s_3242_ = lean_ctor_get(v_id_3200_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_id_3200_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v_id_3200_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_s_3242_);
lean_dec(v_id_3200_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
lean_ctor_set_tag(v___x_3244_, 3);
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_s_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
v___y_3226_ = v___x_3247_;
goto v___jp_3225_;
}
}
}
else
{
lean_object* v_n_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
v_n_3250_ = lean_ctor_get(v_id_3200_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_id_3200_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v_id_3200_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_n_3250_);
lean_dec(v_id_3200_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set_tag(v___x_3252_, 2);
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_n_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
v___y_3226_ = v___x_3255_;
goto v___jp_3225_;
}
}
}
v___jp_3205_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3206_);
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___y_3206_);
lean_ctor_set(v___x_3210_, 1, v___y_3209_);
v___x_3211_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3212_, 0, v_message_3202_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3211_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = lean_box(0);
v___x_3215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3213_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3210_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3218_ = l_Lean_Json_opt___redArg(v___x_3204_, v___x_3217_, v_data_x3f_3203_);
v___x_3219_ = l_List_appendTR___redArg(v___x_3216_, v___x_3218_);
v___x_3220_ = l_Lean_Json_mkObj(v___x_3219_);
lean_dec(v___x_3219_);
lean_inc_ref(v___y_3208_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___y_3208_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
lean_ctor_set(v___x_3222_, 1, v___x_3214_);
v___x_3223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___y_3207_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___y_3124_ = v___x_3223_;
goto v___jp_3123_;
}
v___jp_3225_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3224_);
lean_ctor_set(v___x_3227_, 1, v___y_3226_);
v___x_3228_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3229_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3201_)
{
case 0:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3230_;
goto v___jp_3205_;
}
case 1:
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3231_;
goto v___jp_3205_;
}
case 2:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3232_;
goto v___jp_3205_;
}
case 3:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3233_;
goto v___jp_3205_;
}
case 4:
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3234_;
goto v___jp_3205_;
}
case 5:
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3235_;
goto v___jp_3205_;
}
case 6:
{
lean_object* v___x_3236_; 
v___x_3236_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3236_;
goto v___jp_3205_;
}
case 7:
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3237_;
goto v___jp_3205_;
}
case 8:
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3238_;
goto v___jp_3205_;
}
case 9:
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3239_;
goto v___jp_3205_;
}
case 10:
{
lean_object* v___x_3240_; 
v___x_3240_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3240_;
goto v___jp_3205_;
}
default: 
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3206_ = v___x_3229_;
v___y_3207_ = v___x_3227_;
v___y_3208_ = v___x_3228_;
v___y_3209_ = v___x_3241_;
goto v___jp_3205_;
}
}
}
}
}
v___jp_3123_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3122_);
lean_ctor_set(v___x_3125_, 1, v___y_3124_);
v___x_3126_ = l_Lean_Json_mkObj(v___x_3125_);
lean_dec_ref_known(v___x_3125_, 2);
v___x_3127_ = l_Lean_Json_compress(v___x_3126_);
v___x_3128_ = lean_string_append(v___x_3120_, v___x_3127_);
lean_dec_ref(v___x_3127_);
v___x_3129_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_3130_ = lean_string_append(v___x_3128_, v___x_3129_);
v___x_3131_ = lean_mk_io_user_error(v___x_3130_);
v___x_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
}
v___jp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3062_ = lean_string_append(v___y_3060_, v___y_3061_);
lean_dec_ref(v___y_3061_);
v___x_3063_ = lean_mk_io_user_error(v___x_3062_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set_tag(v___x_3057_, 1);
lean_ctor_set(v___x_3057_, 0, v___x_3063_);
v___x_3065_ = v___x_3057_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec_ref(v_inst_3052_);
lean_dec(v_expectedID_3051_);
v_a_3259_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3054_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3054_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* v_h_3267_, lean_object* v_nBytes_3268_, lean_object* v_expectedID_3269_, lean_object* v_inst_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3267_, v_nBytes_3268_, v_expectedID_3269_, v_inst_3270_);
lean_dec(v_nBytes_3268_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs(lean_object* v_h_3273_, lean_object* v_nBytes_3274_, lean_object* v_expectedID_3275_, lean_object* v_00_u03b1_3276_, lean_object* v_inst_3277_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3273_, v_nBytes_3274_, v_expectedID_3275_, v_inst_3277_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___boxed(lean_object* v_h_3280_, lean_object* v_nBytes_3281_, lean_object* v_expectedID_3282_, lean_object* v_00_u03b1_3283_, lean_object* v_inst_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_IO_FS_Stream_readResponseAs(v_h_3280_, v_nBytes_3281_, v_expectedID_3282_, v_00_u03b1_3283_, v_inst_3284_);
lean_dec(v_nBytes_3281_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(lean_object* v_k_3287_, lean_object* v_x_3288_){
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
lean_object* v_val_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v_val_3290_ = lean_ctor_get(v_x_3288_, 0);
lean_inc(v_val_3290_);
lean_dec_ref_known(v_x_3288_, 1);
v___x_3291_ = l_Lean_Json_Structured_toJson(v_val_3290_);
v___x_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3292_, 0, v_k_3287_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(lean_object* v_k_3295_, lean_object* v_x_3296_){
_start:
{
if (lean_obj_tag(v_x_3296_) == 0)
{
lean_object* v___x_3297_; 
lean_dec_ref(v_k_3295_);
v___x_3297_ = lean_box(0);
return v___x_3297_;
}
else
{
lean_object* v_val_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v_val_3298_ = lean_ctor_get(v_x_3296_, 0);
lean_inc(v_val_3298_);
v___x_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3299_, 0, v_k_3295_);
lean_ctor_set(v___x_3299_, 1, v_val_3298_);
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3299_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
return v___x_3301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* v_k_3302_, lean_object* v_x_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v_k_3302_, v_x_3303_);
lean_dec(v_x_3303_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage(lean_object* v_h_3305_, lean_object* v_m_3306_){
_start:
{
lean_object* v___x_3308_; lean_object* v___y_3310_; 
v___x_3308_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_3306_))
{
case 0:
{
lean_object* v_id_3314_; lean_object* v_method_3315_; lean_object* v_params_x3f_3316_; lean_object* v___x_3317_; lean_object* v___y_3319_; 
v_id_3314_ = lean_ctor_get(v_m_3306_, 0);
lean_inc(v_id_3314_);
v_method_3315_ = lean_ctor_get(v_m_3306_, 1);
lean_inc_ref(v_method_3315_);
v_params_x3f_3316_ = lean_ctor_get(v_m_3306_, 2);
lean_inc(v_params_x3f_3316_);
lean_dec_ref_known(v_m_3306_, 3);
v___x_3317_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3314_))
{
case 0:
{
lean_object* v_s_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
v_s_3330_ = lean_ctor_get(v_id_3314_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_id_3314_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v_id_3314_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_s_3330_);
lean_dec(v_id_3314_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set_tag(v___x_3332_, 3);
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_s_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
v___y_3319_ = v___x_3335_;
goto v___jp_3318_;
}
}
}
case 1:
{
lean_object* v_n_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
v_n_3338_ = lean_ctor_get(v_id_3314_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_id_3314_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v_id_3314_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_n_3338_);
lean_dec(v_id_3314_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
lean_ctor_set_tag(v___x_3340_, 2);
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_n_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
v___y_3319_ = v___x_3343_;
goto v___jp_3318_;
}
}
}
default: 
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_box(0);
v___y_3319_ = v___x_3346_;
goto v___jp_3318_;
}
}
v___jp_3318_:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3317_);
lean_ctor_set(v___x_3320_, 1, v___y_3319_);
v___x_3321_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3322_, 0, v_method_3315_);
v___x_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3321_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
v___x_3324_ = lean_box(0);
v___x_3325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3320_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3328_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3327_, v_params_x3f_3316_);
v___x_3329_ = l_List_appendTR___redArg(v___x_3326_, v___x_3328_);
v___y_3310_ = v___x_3329_;
goto v___jp_3309_;
}
}
case 1:
{
lean_object* v_method_3347_; lean_object* v_params_x3f_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3360_; 
v_method_3347_ = lean_ctor_get(v_m_3306_, 0);
v_params_x3f_3348_ = lean_ctor_get(v_m_3306_, 1);
v_isSharedCheck_3360_ = !lean_is_exclusive(v_m_3306_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3350_ = v_m_3306_;
v_isShared_3351_ = v_isSharedCheck_3360_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_params_x3f_3348_);
lean_inc(v_method_3347_);
lean_dec(v_m_3306_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3360_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3352_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3353_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3353_, 0, v_method_3347_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 0);
lean_ctor_set(v___x_3350_, 1, v___x_3353_);
lean_ctor_set(v___x_3350_, 0, v___x_3352_);
v___x_3355_ = v___x_3350_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3352_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3357_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3356_, v_params_x3f_3348_);
v___x_3358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3355_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___y_3310_ = v___x_3358_;
goto v___jp_3309_;
}
}
}
case 2:
{
lean_object* v_id_3361_; lean_object* v_result_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3394_; 
v_id_3361_ = lean_ctor_get(v_m_3306_, 0);
v_result_3362_ = lean_ctor_get(v_m_3306_, 1);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_m_3306_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3364_ = v_m_3306_;
v_isShared_3365_ = v_isSharedCheck_3394_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_result_3362_);
lean_inc(v_id_3361_);
lean_dec(v_m_3306_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3394_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; lean_object* v___y_3368_; 
v___x_3366_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3361_))
{
case 0:
{
lean_object* v_s_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
v_s_3377_ = lean_ctor_get(v_id_3361_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_id_3361_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v_id_3361_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_s_3377_);
lean_dec(v_id_3361_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set_tag(v___x_3379_, 3);
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_s_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
v___y_3368_ = v___x_3382_;
goto v___jp_3367_;
}
}
}
case 1:
{
lean_object* v_n_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
v_n_3385_ = lean_ctor_get(v_id_3361_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_id_3361_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v_id_3361_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_n_3385_);
lean_dec(v_id_3361_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
lean_ctor_set_tag(v___x_3387_, 2);
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_n_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
v___y_3368_ = v___x_3390_;
goto v___jp_3367_;
}
}
}
default: 
{
lean_object* v___x_3393_; 
v___x_3393_ = lean_box(0);
v___y_3368_ = v___x_3393_;
goto v___jp_3367_;
}
}
v___jp_3367_:
{
lean_object* v___x_3370_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set_tag(v___x_3364_, 0);
lean_ctor_set(v___x_3364_, 1, v___y_3368_);
lean_ctor_set(v___x_3364_, 0, v___x_3366_);
v___x_3370_ = v___x_3364_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3376_, 1, v___y_3368_);
v___x_3370_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3371_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
lean_ctor_set(v___x_3372_, 1, v_result_3362_);
v___x_3373_ = lean_box(0);
v___x_3374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3370_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___y_3310_ = v___x_3375_;
goto v___jp_3309_;
}
}
}
}
default: 
{
lean_object* v_id_3395_; uint8_t v_code_3396_; lean_object* v_message_3397_; lean_object* v_data_x3f_3398_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___x_3418_; lean_object* v___y_3420_; 
v_id_3395_ = lean_ctor_get(v_m_3306_, 0);
lean_inc(v_id_3395_);
v_code_3396_ = lean_ctor_get_uint8(v_m_3306_, sizeof(void*)*3);
v_message_3397_ = lean_ctor_get(v_m_3306_, 1);
lean_inc_ref(v_message_3397_);
v_data_x3f_3398_ = lean_ctor_get(v_m_3306_, 2);
lean_inc(v_data_x3f_3398_);
lean_dec_ref_known(v_m_3306_, 3);
v___x_3418_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3395_))
{
case 0:
{
lean_object* v_s_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
v_s_3436_ = lean_ctor_get(v_id_3395_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_id_3395_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v_id_3395_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_s_3436_);
lean_dec(v_id_3395_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set_tag(v___x_3438_, 3);
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_s_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
v___y_3420_ = v___x_3441_;
goto v___jp_3419_;
}
}
}
case 1:
{
lean_object* v_n_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
v_n_3444_ = lean_ctor_get(v_id_3395_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_id_3395_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v_id_3395_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_n_3444_);
lean_dec(v_id_3395_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set_tag(v___x_3446_, 2);
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_n_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
v___y_3420_ = v___x_3449_;
goto v___jp_3419_;
}
}
}
default: 
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_box(0);
v___y_3420_ = v___x_3452_;
goto v___jp_3419_;
}
}
v___jp_3399_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_inc(v___y_3403_);
lean_inc_ref(v___y_3400_);
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___y_3400_);
lean_ctor_set(v___x_3404_, 1, v___y_3403_);
v___x_3405_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3406_, 0, v_message_3397_);
v___x_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3405_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = lean_box(0);
v___x_3409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3407_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3404_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3412_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v___x_3411_, v_data_x3f_3398_);
lean_dec(v_data_x3f_3398_);
v___x_3413_ = l_List_appendTR___redArg(v___x_3410_, v___x_3412_);
v___x_3414_ = l_Lean_Json_mkObj(v___x_3413_);
lean_dec(v___x_3413_);
lean_inc_ref(v___y_3402_);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___y_3402_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v___x_3408_);
v___x_3417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___y_3401_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___y_3310_ = v___x_3417_;
goto v___jp_3309_;
}
v___jp_3419_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3418_);
lean_ctor_set(v___x_3421_, 1, v___y_3420_);
v___x_3422_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3423_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3396_)
{
case 0:
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3424_;
goto v___jp_3399_;
}
case 1:
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3425_;
goto v___jp_3399_;
}
case 2:
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3426_;
goto v___jp_3399_;
}
case 3:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3427_;
goto v___jp_3399_;
}
case 4:
{
lean_object* v___x_3428_; 
v___x_3428_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3428_;
goto v___jp_3399_;
}
case 5:
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3429_;
goto v___jp_3399_;
}
case 6:
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3430_;
goto v___jp_3399_;
}
case 7:
{
lean_object* v___x_3431_; 
v___x_3431_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3431_;
goto v___jp_3399_;
}
case 8:
{
lean_object* v___x_3432_; 
v___x_3432_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3432_;
goto v___jp_3399_;
}
case 9:
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3433_;
goto v___jp_3399_;
}
case 10:
{
lean_object* v___x_3434_; 
v___x_3434_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3434_;
goto v___jp_3399_;
}
default: 
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3400_ = v___x_3423_;
v___y_3401_ = v___x_3421_;
v___y_3402_ = v___x_3422_;
v___y_3403_ = v___x_3435_;
goto v___jp_3399_;
}
}
}
}
}
v___jp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3308_);
lean_ctor_set(v___x_3311_, 1, v___y_3310_);
v___x_3312_ = l_Lean_Json_mkObj(v___x_3311_);
lean_dec_ref_known(v___x_3311_, 2);
v___x_3313_ = l_Lean_IO_FS_Stream_writeJson(v_h_3305_, v___x_3312_);
return v___x_3313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage___boxed(lean_object* v_h_3453_, lean_object* v_m_3454_, lean_object* v_a_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3453_, v_m_3454_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg(lean_object* v_inst_3457_, lean_object* v_h_3458_, lean_object* v_r_3459_){
_start:
{
lean_object* v_id_3461_; lean_object* v_method_3462_; lean_object* v_param_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3483_; 
v_id_3461_ = lean_ctor_get(v_r_3459_, 0);
v_method_3462_ = lean_ctor_get(v_r_3459_, 1);
v_param_3463_ = lean_ctor_get(v_r_3459_, 2);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_r_3459_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3465_ = v_r_3459_;
v_isShared_3466_ = v_isSharedCheck_3483_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_param_3463_);
lean_inc(v_method_3462_);
lean_inc(v_id_3461_);
lean_dec(v_r_3459_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3483_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___y_3468_; lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3457_, v_param_3463_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v___x_3474_; 
lean_dec_ref_known(v___x_3473_, 1);
v___x_3474_ = lean_box(0);
v___y_3468_ = v___x_3474_;
goto v___jp_3467_;
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
v_a_3475_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3473_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3473_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
v___y_3468_ = v___x_3480_;
goto v___jp_3467_;
}
}
}
v___jp_3467_:
{
lean_object* v___x_3470_; 
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 2, v___y_3468_);
v___x_3470_ = v___x_3465_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_id_3461_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_method_3462_);
lean_ctor_set(v_reuseFailAlloc_3472_, 2, v___y_3468_);
v___x_3470_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3458_, v___x_3470_);
return v___x_3471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg___boxed(lean_object* v_inst_3484_, lean_object* v_h_3485_, lean_object* v_r_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3484_, v_h_3485_, v_r_3486_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest(lean_object* v_00_u03b1_3489_, lean_object* v_inst_3490_, lean_object* v_h_3491_, lean_object* v_r_3492_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3490_, v_h_3491_, v_r_3492_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___boxed(lean_object* v_00_u03b1_3495_, lean_object* v_inst_3496_, lean_object* v_h_3497_, lean_object* v_r_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_IO_FS_Stream_writeRequest(v_00_u03b1_3495_, v_inst_3496_, v_h_3497_, v_r_3498_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg(lean_object* v_inst_3501_, lean_object* v_h_3502_, lean_object* v_n_3503_){
_start:
{
lean_object* v_method_3505_; lean_object* v_param_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3526_; 
v_method_3505_ = lean_ctor_get(v_n_3503_, 0);
v_param_3506_ = lean_ctor_get(v_n_3503_, 1);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_n_3503_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3508_ = v_n_3503_;
v_isShared_3509_ = v_isSharedCheck_3526_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_param_3506_);
lean_inc(v_method_3505_);
lean_dec(v_n_3503_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3526_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___y_3511_; lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3501_, v_param_3506_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v___x_3517_; 
lean_dec_ref_known(v___x_3516_, 1);
v___x_3517_ = lean_box(0);
v___y_3511_ = v___x_3517_;
goto v___jp_3510_;
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
v_a_3518_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3516_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3516_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
v___y_3511_ = v___x_3523_;
goto v___jp_3510_;
}
}
}
v___jp_3510_:
{
lean_object* v___x_3513_; 
if (v_isShared_3509_ == 0)
{
lean_ctor_set_tag(v___x_3508_, 1);
lean_ctor_set(v___x_3508_, 1, v___y_3511_);
v___x_3513_ = v___x_3508_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_method_3505_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v___y_3511_);
v___x_3513_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3502_, v___x_3513_);
return v___x_3514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg___boxed(lean_object* v_inst_3527_, lean_object* v_h_3528_, lean_object* v_n_3529_, lean_object* v_a_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3527_, v_h_3528_, v_n_3529_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification(lean_object* v_00_u03b1_3532_, lean_object* v_inst_3533_, lean_object* v_h_3534_, lean_object* v_n_3535_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3533_, v_h_3534_, v_n_3535_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___boxed(lean_object* v_00_u03b1_3538_, lean_object* v_inst_3539_, lean_object* v_h_3540_, lean_object* v_n_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_IO_FS_Stream_writeNotification(v_00_u03b1_3538_, v_inst_3539_, v_h_3540_, v_n_3541_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg(lean_object* v_inst_3544_, lean_object* v_h_3545_, lean_object* v_r_3546_){
_start:
{
lean_object* v_id_3548_; lean_object* v_result_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3558_; 
v_id_3548_ = lean_ctor_get(v_r_3546_, 0);
v_result_3549_ = lean_ctor_get(v_r_3546_, 1);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_r_3546_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3551_ = v_r_3546_;
v_isShared_3552_ = v_isSharedCheck_3558_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_result_3549_);
lean_inc(v_id_3548_);
lean_dec(v_r_3546_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3558_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3555_; 
v___x_3553_ = lean_apply_1(v_inst_3544_, v_result_3549_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set_tag(v___x_3551_, 2);
lean_ctor_set(v___x_3551_, 1, v___x_3553_);
v___x_3555_ = v___x_3551_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_id_3548_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v___x_3556_; 
v___x_3556_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3545_, v___x_3555_);
return v___x_3556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg___boxed(lean_object* v_inst_3559_, lean_object* v_h_3560_, lean_object* v_r_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3559_, v_h_3560_, v_r_3561_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse(lean_object* v_00_u03b1_3564_, lean_object* v_inst_3565_, lean_object* v_h_3566_, lean_object* v_r_3567_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3565_, v_h_3566_, v_r_3567_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___boxed(lean_object* v_00_u03b1_3570_, lean_object* v_inst_3571_, lean_object* v_h_3572_, lean_object* v_r_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_IO_FS_Stream_writeResponse(v_00_u03b1_3570_, v_inst_3571_, v_h_3572_, v_r_3573_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError(lean_object* v_h_3576_, lean_object* v_e_3577_){
_start:
{
lean_object* v_id_3579_; uint8_t v_code_3580_; lean_object* v_message_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3590_; 
v_id_3579_ = lean_ctor_get(v_e_3577_, 0);
v_code_3580_ = lean_ctor_get_uint8(v_e_3577_, sizeof(void*)*3);
v_message_3581_ = lean_ctor_get(v_e_3577_, 1);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_e_3577_);
if (v_isSharedCheck_3590_ == 0)
{
lean_object* v_unused_3591_; 
v_unused_3591_ = lean_ctor_get(v_e_3577_, 2);
lean_dec(v_unused_3591_);
v___x_3583_ = v_e_3577_;
v_isShared_3584_ = v_isSharedCheck_3590_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_message_3581_);
lean_inc(v_id_3579_);
lean_dec(v_e_3577_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3590_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v___x_3587_; 
v___x_3585_ = lean_box(0);
if (v_isShared_3584_ == 0)
{
lean_ctor_set_tag(v___x_3583_, 3);
lean_ctor_set(v___x_3583_, 2, v___x_3585_);
v___x_3587_ = v___x_3583_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_id_3579_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_message_3581_);
lean_ctor_set(v_reuseFailAlloc_3589_, 2, v___x_3585_);
lean_ctor_set_uint8(v_reuseFailAlloc_3589_, sizeof(void*)*3, v_code_3580_);
v___x_3587_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3576_, v___x_3587_);
return v___x_3588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError___boxed(lean_object* v_h_3592_, lean_object* v_e_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_IO_FS_Stream_writeResponseError(v_h_3592_, v_e_3593_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* v_inst_3596_, lean_object* v_h_3597_, lean_object* v_e_3598_){
_start:
{
lean_object* v_id_3600_; uint8_t v_code_3601_; lean_object* v_message_3602_; lean_object* v_data_x3f_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3623_; 
v_id_3600_ = lean_ctor_get(v_e_3598_, 0);
v_code_3601_ = lean_ctor_get_uint8(v_e_3598_, sizeof(void*)*3);
v_message_3602_ = lean_ctor_get(v_e_3598_, 1);
v_data_x3f_3603_ = lean_ctor_get(v_e_3598_, 2);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_e_3598_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3605_ = v_e_3598_;
v_isShared_3606_ = v_isSharedCheck_3623_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_data_x3f_3603_);
lean_inc(v_message_3602_);
lean_inc(v_id_3600_);
lean_dec(v_e_3598_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3623_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___y_3608_; 
if (lean_obj_tag(v_data_x3f_3603_) == 0)
{
lean_object* v___x_3613_; 
lean_dec_ref(v_inst_3596_);
v___x_3613_ = lean_box(0);
v___y_3608_ = v___x_3613_;
goto v___jp_3607_;
}
else
{
lean_object* v_val_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3622_; 
v_val_3614_ = lean_ctor_get(v_data_x3f_3603_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_data_x3f_3603_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3616_ = v_data_x3f_3603_;
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_val_3614_);
lean_dec(v_data_x3f_3603_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3618_; lean_object* v___x_3620_; 
v___x_3618_ = lean_apply_1(v_inst_3596_, v_val_3614_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3618_);
v___x_3620_ = v___x_3616_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3618_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
v___y_3608_ = v___x_3620_;
goto v___jp_3607_;
}
}
}
v___jp_3607_:
{
lean_object* v___x_3610_; 
if (v_isShared_3606_ == 0)
{
lean_ctor_set_tag(v___x_3605_, 3);
lean_ctor_set(v___x_3605_, 2, v___y_3608_);
v___x_3610_ = v___x_3605_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_id_3600_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_message_3602_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v___y_3608_);
lean_ctor_set_uint8(v_reuseFailAlloc_3612_, sizeof(void*)*3, v_code_3601_);
v___x_3610_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3597_, v___x_3610_);
return v___x_3611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object* v_inst_3624_, lean_object* v_h_3625_, lean_object* v_e_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3624_, v_h_3625_, v_e_3626_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData(lean_object* v_00_u03b1_3629_, lean_object* v_inst_3630_, lean_object* v_h_3631_, lean_object* v_e_3632_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3630_, v_h_3631_, v_e_3632_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object* v_00_u03b1_3635_, lean_object* v_inst_3636_, lean_object* v_h_3637_, lean_object* v_e_3638_, lean_object* v_a_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData(v_00_u03b1_3635_, v_inst_3636_, v_h_3637_, v_e_3638_);
return v_res_3640_;
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
