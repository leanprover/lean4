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
uint8_t v_x_17__boxed_320_; uint8_t v_y_18__boxed_321_; uint8_t v_res_322_; lean_object* v_r_323_; 
v_x_17__boxed_320_ = lean_unbox(v_x_318_);
v_y_18__boxed_321_ = lean_unbox(v_y_319_);
v_res_322_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_x_17__boxed_320_, v_y_18__boxed_321_);
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
lean_inc_ref(v___y_1177_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___y_1177_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1185_);
v___x_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___y_1179_);
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
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
v___y_1180_ = v___x_1201_;
goto v___jp_1176_;
}
case 1:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
v___y_1180_ = v___x_1202_;
goto v___jp_1176_;
}
case 2:
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
v___y_1180_ = v___x_1203_;
goto v___jp_1176_;
}
case 3:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
v___y_1180_ = v___x_1204_;
goto v___jp_1176_;
}
case 4:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
v___y_1180_ = v___x_1205_;
goto v___jp_1176_;
}
case 5:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
v___y_1180_ = v___x_1206_;
goto v___jp_1176_;
}
case 6:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
v___y_1180_ = v___x_1207_;
goto v___jp_1176_;
}
case 7:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
v___y_1180_ = v___x_1208_;
goto v___jp_1176_;
}
case 8:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
v___y_1180_ = v___x_1209_;
goto v___jp_1176_;
}
case 9:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
v___y_1180_ = v___x_1210_;
goto v___jp_1176_;
}
case 10:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
v___y_1180_ = v___x_1211_;
goto v___jp_1176_;
}
default: 
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_1177_ = v___x_1199_;
v___y_1178_ = v___x_1200_;
v___y_1179_ = v___x_1198_;
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
lean_object* v___y_1247_; uint8_t v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
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
v___y_1248_ = v___x_1320_;
v___y_1249_ = v_a_1316_;
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
v___y_1248_ = v___x_1327_;
v___y_1249_ = v_a_1316_;
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
lean_ctor_set(v___x_1251_, 1, v___y_1249_);
lean_ctor_set(v___x_1251_, 2, v___y_1250_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*3, v___y_1248_);
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
lean_object* v_fst_1625_; lean_object* v_snd_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v_fst_1625_ = lean_ctor_get(v_a_1624_, 0);
v_snd_1626_ = lean_ctor_get(v_a_1624_, 1);
v___x_1627_ = lean_string_utf8_byte_size(v_fst_1625_);
v___x_1628_ = lean_nat_dec_eq(v_snd_1626_, v___x_1627_);
if (v___x_1628_ == 0)
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
if (v___x_1628_ == 0)
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
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1649_, 0, v_a_1624_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(lean_object* v_a_1650_){
_start:
{
lean_object* v___x_1651_; 
lean_inc_ref(v_a_1650_);
v___x_1651_ = l_Lean_Json_Parser_num(v_a_1650_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_pos_1652_; lean_object* v_res_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1661_; 
lean_dec_ref(v_a_1650_);
v_pos_1652_ = lean_ctor_get(v___x_1651_, 0);
v_res_1653_ = lean_ctor_get(v___x_1651_, 1);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1655_ = v___x_1651_;
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_res_1653_);
lean_inc(v_pos_1652_);
lean_dec(v___x_1651_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1657_, 0, v_res_1653_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v___x_1657_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_pos_1652_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
lean_object* v_pos_1662_; lean_object* v_err_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1716_; 
v_pos_1662_ = lean_ctor_get(v___x_1651_, 0);
v_err_1663_ = lean_ctor_get(v___x_1651_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1665_ = v___x_1651_;
v_isShared_1666_ = v_isSharedCheck_1716_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_err_1663_);
lean_inc(v_pos_1662_);
lean_dec(v___x_1651_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1716_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v_snd_1667_; lean_object* v_snd_1668_; uint8_t v___x_1669_; 
v_snd_1667_ = lean_ctor_get(v_a_1650_, 1);
lean_inc(v_snd_1667_);
lean_dec_ref(v_a_1650_);
v_snd_1668_ = lean_ctor_get(v_pos_1662_, 1);
v___x_1669_ = lean_nat_dec_eq(v_snd_1667_, v_snd_1668_);
lean_dec(v_snd_1667_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1671_; 
if (v_isShared_1666_ == 0)
{
v___x_1671_ = v___x_1665_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_pos_1662_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_err_1663_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
else
{
lean_object* v___x_1673_; 
lean_inc(v_snd_1668_);
lean_del_object(v___x_1665_);
lean_dec(v_err_1663_);
v___x_1673_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v_pos_1662_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_pos_1674_; lean_object* v_res_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_snd_1668_);
v_pos_1674_ = lean_ctor_get(v___x_1673_, 0);
v_res_1675_ = lean_ctor_get(v___x_1673_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1677_ = v___x_1673_;
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_res_1675_);
lean_inc(v_pos_1674_);
lean_dec(v___x_1673_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_res_1675_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v___x_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_pos_1674_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
else
{
lean_object* v_pos_1684_; lean_object* v_err_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1715_; 
v_pos_1684_ = lean_ctor_get(v___x_1673_, 0);
v_err_1685_ = lean_ctor_get(v___x_1673_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1687_ = v___x_1673_;
v_isShared_1688_ = v_isSharedCheck_1715_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_err_1685_);
lean_inc(v_pos_1684_);
lean_dec(v___x_1673_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1715_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v_snd_1689_; uint8_t v___x_1690_; 
v_snd_1689_ = lean_ctor_get(v_pos_1684_, 1);
v___x_1690_ = lean_nat_dec_eq(v_snd_1668_, v_snd_1689_);
lean_dec(v_snd_1668_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1692_; 
if (v_isShared_1688_ == 0)
{
v___x_1692_ = v___x_1687_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_pos_1684_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_err_1685_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_del_object(v___x_1687_);
lean_dec(v_err_1685_);
v___x_1694_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___x_1695_ = l_Std_Internal_Parsec_String_pstring(v___x_1694_, v_pos_1684_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_pos_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1704_; 
v_pos_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; 
v_unused_1705_ = lean_ctor_get(v___x_1695_, 1);
lean_dec(v_unused_1705_);
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_pos_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = lean_box(2);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v___x_1700_);
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_pos_1696_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
else
{
lean_object* v_pos_1706_; lean_object* v_err_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_pos_1706_ = lean_ctor_get(v___x_1695_, 0);
v_err_1707_ = lean_ctor_get(v___x_1695_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1695_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_err_1707_);
lean_inc(v_pos_1706_);
lean_dec(v___x_1695_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_pos_1706_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_err_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object* v_j_1717_, lean_object* v_k_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_Json_getObjValD(v_j_1717_, v_k_1718_);
switch(lean_obj_tag(v___x_1719_))
{
case 3:
{
lean_object* v_s_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1728_; 
v_s_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_s_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1728_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 0);
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_s_1720_);
v___x_1725_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
}
}
case 2:
{
lean_object* v_n_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
v_n_1729_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1731_ = v___x_1719_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_n_1729_);
lean_dec(v___x_1719_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set_tag(v___x_1731_, 1);
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_n_1729_);
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
default: 
{
lean_object* v___x_1738_; 
lean_dec(v___x_1719_);
v___x_1738_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object* v_j_1739_, lean_object* v_k_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_j_1739_, v_k_1740_);
lean_dec_ref(v_k_1740_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object* v_j_1742_, lean_object* v_k_1743_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Json_getObjValD(v_j_1742_, v_k_1743_);
if (lean_obj_tag(v___x_1746_) == 2)
{
lean_object* v_n_1747_; lean_object* v_mantissa_1748_; lean_object* v_exponent_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_n_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc_ref(v_n_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v_mantissa_1748_ = lean_ctor_get(v_n_1747_, 0);
lean_inc(v_mantissa_1748_);
v_exponent_1749_ = lean_ctor_get(v_n_1747_, 1);
lean_inc(v_exponent_1749_);
lean_dec_ref(v_n_1747_);
v___x_1750_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_1751_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1752_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_1753_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1752_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_1755_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_1757_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_1759_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_1761_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_1763_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_1765_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_1767_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_1769_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_1771_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_1773_ = lean_int_dec_eq(v_mantissa_1748_, v___x_1772_);
lean_dec(v_mantissa_1748_);
if (v___x_1773_ == 0)
{
lean_dec(v_exponent_1749_);
goto v___jp_1744_;
}
else
{
lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = lean_unsigned_to_nat(0u);
v___x_1775_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1774_);
lean_dec(v_exponent_1749_);
if (v___x_1775_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1776_; 
v___x_1776_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_1776_;
}
}
}
else
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
lean_dec(v_mantissa_1748_);
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1777_);
lean_dec(v_exponent_1749_);
if (v___x_1778_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_1779_;
}
}
}
else
{
lean_object* v___x_1780_; uint8_t v___x_1781_; 
lean_dec(v_mantissa_1748_);
v___x_1780_ = lean_unsigned_to_nat(0u);
v___x_1781_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1780_);
lean_dec(v_exponent_1749_);
if (v___x_1781_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1782_; 
v___x_1782_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_1782_;
}
}
}
else
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
lean_dec(v_mantissa_1748_);
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1783_);
lean_dec(v_exponent_1749_);
if (v___x_1784_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1785_; 
v___x_1785_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_1785_;
}
}
}
else
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
lean_dec(v_mantissa_1748_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1786_);
lean_dec(v_exponent_1749_);
if (v___x_1787_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1788_; 
v___x_1788_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_1788_;
}
}
}
else
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
lean_dec(v_mantissa_1748_);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1789_);
lean_dec(v_exponent_1749_);
if (v___x_1790_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1791_; 
v___x_1791_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_1791_;
}
}
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
lean_dec(v_mantissa_1748_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1792_);
lean_dec(v_exponent_1749_);
if (v___x_1793_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1794_; 
v___x_1794_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_1794_;
}
}
}
else
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
lean_dec(v_mantissa_1748_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1795_);
lean_dec(v_exponent_1749_);
if (v___x_1796_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1797_; 
v___x_1797_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_1797_;
}
}
}
else
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
lean_dec(v_mantissa_1748_);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1798_);
lean_dec(v_exponent_1749_);
if (v___x_1799_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_1800_;
}
}
}
else
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
lean_dec(v_mantissa_1748_);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1801_);
lean_dec(v_exponent_1749_);
if (v___x_1802_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1803_; 
v___x_1803_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_1803_;
}
}
}
else
{
lean_object* v___x_1804_; uint8_t v___x_1805_; 
lean_dec(v_mantissa_1748_);
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1804_);
lean_dec(v_exponent_1749_);
if (v___x_1805_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1806_; 
v___x_1806_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_1806_;
}
}
}
else
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
lean_dec(v_mantissa_1748_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_nat_dec_eq(v_exponent_1749_, v___x_1807_);
lean_dec(v_exponent_1749_);
if (v___x_1808_ == 0)
{
goto v___jp_1744_;
}
else
{
lean_object* v___x_1809_; 
v___x_1809_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_1809_;
}
}
}
else
{
lean_dec(v___x_1746_);
goto v___jp_1744_;
}
v___jp_1744_:
{
lean_object* v___x_1745_; 
v___x_1745_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object* v_j_1810_, lean_object* v_k_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_j_1810_, v_k_1811_);
lean_dec_ref(v_k_1811_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object* v_j_1813_, lean_object* v_k_1814_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = l_Lean_Json_getObjValD(v_j_1813_, v_k_1814_);
v___x_1816_ = l_Lean_Json_getStr_x3f(v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object* v_j_1817_, lean_object* v_k_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_j_1817_, v_k_1818_);
lean_dec_ref(v_k_1818_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object* v_input_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v_fst_1856_; lean_object* v_snd_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v_fst_1856_ = lean_ctor_get(v_a_1830_, 0);
v_snd_1857_ = lean_ctor_get(v_a_1830_, 1);
v___x_1858_ = lean_string_utf8_byte_size(v_fst_1856_);
v___x_1859_ = lean_nat_dec_eq(v_snd_1857_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_2209_; 
lean_inc(v_snd_1857_);
lean_inc(v_fst_1856_);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_a_1830_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; lean_object* v_unused_2211_; 
v_unused_2210_ = lean_ctor_get(v_a_1830_, 1);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v_a_1830_, 0);
lean_dec(v_unused_2211_);
v___x_1861_ = v_a_1830_;
v_isShared_1862_ = v_isSharedCheck_2209_;
goto v_resetjp_1860_;
}
else
{
lean_dec(v_a_1830_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_2209_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = lean_string_utf8_next_fast(v_fst_1856_, v_snd_1857_);
lean_dec(v_snd_1857_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v___x_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_fst_1856_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_2208_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1866_; 
v___x_1866_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1865_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_pos_1867_; lean_object* v_res_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_2198_; 
v_pos_1867_ = lean_ctor_get(v___x_1866_, 0);
v_res_1868_ = lean_ctor_get(v___x_1866_, 1);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_1870_ = v___x_1866_;
v_isShared_1871_ = v_isSharedCheck_2198_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_res_1868_);
lean_inc(v_pos_1867_);
lean_dec(v___x_1866_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_2198_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v_fst_1872_; lean_object* v_snd_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v_fst_1872_ = lean_ctor_get(v_pos_1867_, 0);
v_snd_1873_ = lean_ctor_get(v_pos_1867_, 1);
v___x_1874_ = lean_string_utf8_byte_size(v_fst_1872_);
v___x_1875_ = lean_nat_dec_eq(v_snd_1873_, v___x_1874_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_2191_; 
lean_inc(v_snd_1873_);
lean_inc(v_fst_1872_);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_pos_1867_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; lean_object* v_unused_2193_; 
v_unused_2192_ = lean_ctor_get(v_pos_1867_, 1);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_pos_1867_, 0);
lean_dec(v_unused_2193_);
v___x_1877_ = v_pos_1867_;
v_isShared_1878_ = v_isSharedCheck_2191_;
goto v_resetjp_1876_;
}
else
{
lean_dec(v_pos_1867_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_2191_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1879_ = lean_string_utf8_next_fast(v_fst_1872_, v_snd_1873_);
lean_dec(v_snd_1873_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v___x_1879_);
v___x_1881_ = v___x_1877_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_fst_1872_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_2190_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v_id_1883_; uint8_t v_code_1884_; lean_object* v_message_1885_; lean_object* v_data_x3f_1886_; lean_object* v_a_1895_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
v___x_1901_ = lean_string_dec_eq(v_res_1868_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1902_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
v___x_1903_ = lean_string_dec_eq(v_res_1868_, v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1905_ = lean_string_dec_eq(v_res_1868_, v___x_1904_);
lean_dec(v_res_1868_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_del_object(v___x_1870_);
lean_dec_ref(v_input_1829_);
v___x_1906_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3));
v___x_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1881_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_Json_parse(v_input_1829_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1917_; 
lean_del_object(v___x_1870_);
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1917_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1917_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 1);
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1881_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
return v___x_1915_;
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1908_, 0);
lean_inc_n(v_a_1918_, 2);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1919_ = l_Lean_Json_getObjVal_x3f(v_a_1918_, v___x_1902_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; 
lean_dec(v_a_1918_);
lean_del_object(v___x_1870_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v_a_1895_ = v_a_1920_;
goto v___jp_1894_;
}
else
{
lean_object* v_a_1921_; 
v_a_1921_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1919_, 1);
if (lean_obj_tag(v_a_1921_) == 3)
{
lean_object* v_s_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v_s_1922_ = lean_ctor_get(v_a_1921_, 0);
lean_inc_ref(v_s_1922_);
lean_dec_ref_known(v_a_1921_, 1);
v___x_1923_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1924_ = lean_string_dec_eq(v_s_1922_, v___x_1923_);
lean_dec_ref(v_s_1922_);
if (v___x_1924_ == 0)
{
lean_dec(v_a_1918_);
lean_del_object(v___x_1870_);
goto v___jp_1898_;
}
else
{
lean_object* v___x_1925_; 
lean_inc(v_a_1918_);
v___x_1925_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_1918_, v___x_1900_);
if (lean_obj_tag(v___x_1925_) == 0)
{
goto v___jp_1953_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1918_);
v___x_1959_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1918_, v___x_1958_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_dec_ref_known(v___x_1959_, 1);
goto v___jp_1953_;
}
else
{
lean_dec_ref_known(v___x_1959_, 1);
lean_dec_ref_known(v___x_1925_, 1);
lean_dec(v_a_1918_);
lean_del_object(v___x_1870_);
goto v___jp_1891_;
}
}
v___jp_1926_:
{
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1927_; 
lean_dec(v_a_1918_);
lean_del_object(v___x_1870_);
v_a_1927_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1925_, 1);
v_a_1895_ = v_a_1927_;
goto v___jp_1894_;
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1929_; 
v_a_1928_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1929_ = l_Lean_Json_getObjVal_x3f(v_a_1918_, v___x_1904_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; 
lean_dec(v_a_1928_);
lean_del_object(v___x_1870_);
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v_a_1895_ = v_a_1930_;
goto v___jp_1894_;
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_a_1931_ = lean_ctor_get(v___x_1929_, 0);
lean_inc_n(v_a_1931_, 2);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1932_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1933_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_1931_, v___x_1932_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; 
lean_dec(v_a_1931_);
lean_dec(v_a_1928_);
lean_del_object(v___x_1870_);
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v_a_1895_ = v_a_1934_;
goto v___jp_1894_;
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_a_1935_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1936_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1931_);
v___x_1937_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1931_, v___x_1936_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; 
lean_dec(v_a_1935_);
lean_dec(v_a_1931_);
lean_dec(v_a_1928_);
lean_del_object(v___x_1870_);
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v_a_1895_ = v_a_1938_;
goto v___jp_1894_;
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_a_1939_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1940_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1941_ = l_Lean_Json_getObjVal_x3f(v_a_1931_, v___x_1940_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v___x_1942_; uint8_t v___x_1943_; 
lean_dec_ref_known(v___x_1941_, 1);
v___x_1942_ = lean_box(0);
v___x_1943_ = lean_unbox(v_a_1935_);
lean_dec(v_a_1935_);
v_id_1883_ = v_a_1928_;
v_code_1884_ = v___x_1943_;
v_message_1885_ = v_a_1939_;
v_data_x3f_1886_ = v___x_1942_;
goto v___jp_1882_;
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1952_; 
v_a_1944_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1946_ = v___x_1941_;
v_isShared_1947_ = v_isSharedCheck_1952_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1941_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1952_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_unbox(v_a_1935_);
lean_dec(v_a_1935_);
v_id_1883_ = v_a_1928_;
v_code_1884_ = v___x_1950_;
v_message_1885_ = v_a_1939_;
v_data_x3f_1886_ = v___x_1949_;
goto v___jp_1882_;
}
}
}
}
}
}
}
}
v___jp_1953_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1918_);
v___x_1955_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1918_, v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_dec_ref_known(v___x_1955_, 1);
if (lean_obj_tag(v___x_1925_) == 0)
{
goto v___jp_1926_;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_1918_);
v___x_1957_ = l_Lean_Json_getObjVal_x3f(v_a_1918_, v___x_1956_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_dec_ref_known(v___x_1957_, 1);
goto v___jp_1926_;
}
else
{
lean_dec_ref_known(v___x_1957_, 1);
lean_dec_ref_known(v___x_1925_, 1);
lean_dec(v_a_1918_);
lean_del_object(v___x_1870_);
goto v___jp_1891_;
}
}
}
else
{
lean_dec_ref_known(v___x_1955_, 1);
lean_dec_ref(v___x_1925_);
lean_dec(v_a_1918_);
lean_del_object(v___x_1870_);
goto v___jp_1891_;
}
}
}
}
else
{
lean_dec(v_a_1921_);
lean_dec(v_a_1918_);
lean_del_object(v___x_1870_);
goto v___jp_1898_;
}
}
}
}
}
else
{
lean_object* v___x_1960_; 
lean_del_object(v___x_1870_);
lean_dec(v_res_1868_);
lean_dec_ref(v_input_1829_);
v___x_1960_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1881_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_pos_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2009_; 
v_pos_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v___x_1960_, 1);
lean_dec(v_unused_2010_);
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_2009_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_pos_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2009_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_fst_1965_; lean_object* v_snd_1966_; uint8_t v___y_1968_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_fst_1965_ = lean_ctor_get(v_pos_1961_, 0);
v_snd_1966_ = lean_ctor_get(v_pos_1961_, 1);
v___x_2007_ = lean_string_utf8_byte_size(v_fst_1965_);
v___x_2008_ = lean_nat_dec_eq(v_snd_1966_, v___x_2007_);
if (v___x_2008_ == 0)
{
v___y_1968_ = v___x_1903_;
goto v___jp_1967_;
}
else
{
v___y_1968_ = v___x_1901_;
goto v___jp_1967_;
}
v___jp_1967_:
{
if (v___y_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_box(0);
if (v_isShared_1964_ == 0)
{
lean_ctor_set_tag(v___x_1963_, 1);
lean_ctor_set(v___x_1963_, 1, v___x_1969_);
v___x_1971_ = v___x_1963_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_pos_1961_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
else
{
lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2004_; 
lean_inc(v_snd_1966_);
lean_inc(v_fst_1965_);
lean_del_object(v___x_1963_);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_pos_1961_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; lean_object* v_unused_2006_; 
v_unused_2005_ = lean_ctor_get(v_pos_1961_, 1);
lean_dec(v_unused_2005_);
v_unused_2006_ = lean_ctor_get(v_pos_1961_, 0);
lean_dec(v_unused_2006_);
v___x_1974_ = v_pos_1961_;
v_isShared_1975_ = v_isSharedCheck_2004_;
goto v_resetjp_1973_;
}
else
{
lean_dec(v_pos_1961_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2004_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1976_ = lean_string_utf8_next_fast(v_fst_1965_, v_snd_1966_);
lean_dec(v_snd_1966_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 1, v___x_1976_);
v___x_1978_ = v___x_1974_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_fst_1965_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1979_; 
v___x_1979_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1978_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_pos_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1992_; 
v_pos_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v___x_1979_, 1);
lean_dec(v_unused_1993_);
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1992_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_pos_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1992_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_fst_1984_; lean_object* v_snd_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_fst_1984_ = lean_ctor_get(v_pos_1980_, 0);
v_snd_1985_ = lean_ctor_get(v_pos_1980_, 1);
v___x_1986_ = lean_string_utf8_byte_size(v_fst_1984_);
v___x_1987_ = lean_nat_dec_eq(v_snd_1985_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_inc(v_snd_1985_);
lean_inc(v_fst_1984_);
lean_del_object(v___x_1982_);
lean_dec(v_pos_1980_);
v___y_1832_ = v_snd_1985_;
v___y_1833_ = v_fst_1984_;
goto v___jp_1831_;
}
else
{
if (v___x_1901_ == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1988_ = lean_box(0);
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 1);
lean_ctor_set(v___x_1982_, 1, v___x_1988_);
v___x_1990_ = v___x_1982_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_pos_1980_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
else
{
lean_inc(v_snd_1985_);
lean_inc(v_fst_1984_);
lean_del_object(v___x_1982_);
lean_dec(v_pos_1980_);
v___y_1832_ = v_snd_1985_;
v___y_1833_ = v_fst_1984_;
goto v___jp_1831_;
}
}
}
}
else
{
lean_object* v_pos_1994_; lean_object* v_err_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
v_pos_1994_ = lean_ctor_get(v___x_1979_, 0);
v_err_1995_ = lean_ctor_get(v___x_1979_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1979_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_err_1995_);
lean_inc(v_pos_1994_);
lean_dec(v___x_1979_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_pos_1994_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_err_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
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
lean_object* v_pos_2011_; lean_object* v_err_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v_pos_2011_ = lean_ctor_get(v___x_1960_, 0);
v_err_2012_ = lean_ctor_get(v___x_1960_, 1);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1960_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_err_2012_);
lean_inc(v_pos_2011_);
lean_dec(v___x_1960_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_pos_2011_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_err_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
else
{
lean_object* v___x_2020_; 
lean_del_object(v___x_1870_);
lean_dec(v_res_1868_);
lean_dec_ref(v_input_1829_);
v___x_2020_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(v___x_1881_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_pos_2021_; lean_object* v_res_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2180_; 
v_pos_2021_ = lean_ctor_get(v___x_2020_, 0);
v_res_2022_ = lean_ctor_get(v___x_2020_, 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2024_ = v___x_2020_;
v_isShared_2025_ = v_isSharedCheck_2180_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_res_2022_);
lean_inc(v_pos_2021_);
lean_dec(v___x_2020_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2180_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v_fst_2031_; lean_object* v_snd_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_fst_2031_ = lean_ctor_get(v_pos_2021_, 0);
v_snd_2032_ = lean_ctor_get(v_pos_2021_, 1);
v___x_2033_ = lean_string_utf8_byte_size(v_fst_2031_);
v___x_2034_ = lean_nat_dec_eq(v_snd_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
if (v___x_1901_ == 0)
{
lean_dec(v_res_2022_);
goto v___jp_2026_;
}
else
{
lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2177_; 
lean_inc(v_snd_2032_);
lean_inc(v_fst_2031_);
lean_del_object(v___x_2024_);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_pos_2021_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; lean_object* v_unused_2179_; 
v_unused_2178_ = lean_ctor_get(v_pos_2021_, 1);
lean_dec(v_unused_2178_);
v_unused_2179_ = lean_ctor_get(v_pos_2021_, 0);
lean_dec(v_unused_2179_);
v___x_2036_ = v_pos_2021_;
v_isShared_2037_ = v_isSharedCheck_2177_;
goto v_resetjp_2035_;
}
else
{
lean_dec(v_pos_2021_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2177_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_string_utf8_next_fast(v_fst_2031_, v_snd_2032_);
lean_dec(v_snd_2032_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 1, v___x_2038_);
v___x_2040_ = v___x_2036_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_fst_2031_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; 
v___x_2041_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2040_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_pos_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2165_; 
v_pos_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v___x_2041_, 1);
lean_dec(v_unused_2166_);
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2165_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_pos_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2165_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_fst_2046_; lean_object* v_snd_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v_fst_2046_ = lean_ctor_get(v_pos_2042_, 0);
v_snd_2047_ = lean_ctor_get(v_pos_2042_, 1);
v___x_2048_ = lean_string_utf8_byte_size(v_fst_2046_);
v___x_2049_ = lean_nat_dec_eq(v_snd_2047_, v___x_2048_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2158_; 
lean_inc(v_snd_2047_);
lean_inc(v_fst_2046_);
lean_del_object(v___x_2044_);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_pos_2042_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; lean_object* v_unused_2160_; 
v_unused_2159_ = lean_ctor_get(v_pos_2042_, 1);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_pos_2042_, 0);
lean_dec(v_unused_2160_);
v___x_2051_ = v_pos_2042_;
v_isShared_2052_ = v_isSharedCheck_2158_;
goto v_resetjp_2050_;
}
else
{
lean_dec(v_pos_2042_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2158_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2053_ = lean_string_utf8_next_fast(v_fst_2046_, v_snd_2047_);
lean_dec(v_snd_2047_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v___x_2053_);
v___x_2055_ = v___x_2051_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_fst_2046_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; 
v___x_2056_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_pos_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2146_; 
v_pos_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; 
v_unused_2147_ = lean_ctor_get(v___x_2056_, 1);
lean_dec(v_unused_2147_);
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2146_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_pos_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2146_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_fst_2061_; lean_object* v_snd_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_fst_2061_ = lean_ctor_get(v_pos_2057_, 0);
v_snd_2062_ = lean_ctor_get(v_pos_2057_, 1);
v___x_2063_ = lean_string_utf8_byte_size(v_fst_2061_);
v___x_2064_ = lean_nat_dec_eq(v_snd_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2139_; 
lean_inc(v_snd_2062_);
lean_inc(v_fst_2061_);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_pos_2057_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; lean_object* v_unused_2141_; 
v_unused_2140_ = lean_ctor_get(v_pos_2057_, 1);
lean_dec(v_unused_2140_);
v_unused_2141_ = lean_ctor_get(v_pos_2057_, 0);
lean_dec(v_unused_2141_);
v___x_2066_ = v_pos_2057_;
v_isShared_2067_ = v_isSharedCheck_2139_;
goto v_resetjp_2065_;
}
else
{
lean_dec(v_pos_2057_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2139_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = lean_string_utf8_next_fast(v_fst_2061_, v_snd_2062_);
lean_dec(v_snd_2062_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 1, v___x_2068_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_fst_2061_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2071_; 
v___x_2071_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2070_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_pos_2072_; lean_object* v_res_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2128_; 
v_pos_2072_ = lean_ctor_get(v___x_2071_, 0);
v_res_2073_ = lean_ctor_get(v___x_2071_, 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2075_ = v___x_2071_;
v_isShared_2076_ = v_isSharedCheck_2128_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_res_2073_);
lean_inc(v_pos_2072_);
lean_dec(v___x_2071_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2128_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2083_ = lean_string_dec_eq(v_res_2073_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
lean_del_object(v___x_2075_);
v___x_2084_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2085_ = lean_string_dec_eq(v_res_2073_, v___x_2084_);
lean_dec(v_res_2073_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_dec(v_res_2022_);
v___x_2086_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5));
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 1);
lean_ctor_set(v___x_2059_, 1, v___x_2086_);
lean_ctor_set(v___x_2059_, 0, v_pos_2072_);
v___x_2088_ = v___x_2059_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_pos_2072_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_res_2022_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___x_2090_);
lean_ctor_set(v___x_2059_, 0, v_pos_2072_);
v___x_2092_ = v___x_2059_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_pos_2072_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_object* v_fst_2094_; lean_object* v_snd_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
lean_dec(v_res_2073_);
lean_del_object(v___x_2059_);
v_fst_2094_ = lean_ctor_get(v_pos_2072_, 0);
v_snd_2095_ = lean_ctor_get(v_pos_2072_, 1);
v___x_2096_ = lean_string_utf8_byte_size(v_fst_2094_);
v___x_2097_ = lean_nat_dec_eq(v_snd_2095_, v___x_2096_);
if (v___x_2097_ == 0)
{
if (v___x_2083_ == 0)
{
lean_dec(v_res_2022_);
goto v___jp_2077_;
}
else
{
lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2125_; 
lean_inc(v_snd_2095_);
lean_inc(v_fst_2094_);
lean_del_object(v___x_2075_);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_pos_2072_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; lean_object* v_unused_2127_; 
v_unused_2126_ = lean_ctor_get(v_pos_2072_, 1);
lean_dec(v_unused_2126_);
v_unused_2127_ = lean_ctor_get(v_pos_2072_, 0);
lean_dec(v_unused_2127_);
v___x_2099_ = v_pos_2072_;
v_isShared_2100_ = v_isSharedCheck_2125_;
goto v_resetjp_2098_;
}
else
{
lean_dec(v_pos_2072_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2125_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2103_; 
v___x_2101_ = lean_string_utf8_next_fast(v_fst_2094_, v_snd_2095_);
lean_dec(v_snd_2095_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v___x_2101_);
v___x_2103_ = v___x_2099_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_fst_2094_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; 
v___x_2104_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2103_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_pos_2105_; lean_object* v_res_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2114_; 
v_pos_2105_ = lean_ctor_get(v___x_2104_, 0);
v_res_2106_ = lean_ctor_get(v___x_2104_, 1);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2108_ = v___x_2104_;
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_res_2106_);
lean_inc(v_pos_2105_);
lean_dec(v___x_2104_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2114_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v_res_2022_);
lean_ctor_set(v___x_2110_, 1, v_res_2106_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 1, v___x_2110_);
v___x_2112_ = v___x_2108_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_pos_2105_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
else
{
lean_object* v_pos_2115_; lean_object* v_err_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec(v_res_2022_);
v_pos_2115_ = lean_ctor_get(v___x_2104_, 0);
v_err_2116_ = lean_ctor_get(v___x_2104_, 1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2104_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_err_2116_);
lean_inc(v_pos_2115_);
lean_dec(v___x_2104_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_pos_2115_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_err_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2022_);
goto v___jp_2077_;
}
}
v___jp_2077_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_box(0);
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 1);
lean_ctor_set(v___x_2075_, 1, v___x_2078_);
v___x_2080_ = v___x_2075_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_pos_2072_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v_pos_2129_; lean_object* v_err_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_del_object(v___x_2059_);
lean_dec(v_res_2022_);
v_pos_2129_ = lean_ctor_get(v___x_2071_, 0);
v_err_2130_ = lean_ctor_get(v___x_2071_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2071_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_err_2130_);
lean_inc(v_pos_2129_);
lean_dec(v___x_2071_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_pos_2129_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_err_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
lean_dec(v_res_2022_);
v___x_2142_ = lean_box(0);
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 1);
lean_ctor_set(v___x_2059_, 1, v___x_2142_);
v___x_2144_ = v___x_2059_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_pos_2057_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v___x_2142_);
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
else
{
lean_object* v_pos_2148_; lean_object* v_err_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_res_2022_);
v_pos_2148_ = lean_ctor_get(v___x_2056_, 0);
v_err_2149_ = lean_ctor_get(v___x_2056_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2056_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_err_2149_);
lean_inc(v_pos_2148_);
lean_dec(v___x_2056_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_pos_2148_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_err_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
lean_dec(v_res_2022_);
v___x_2161_ = lean_box(0);
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 1);
lean_ctor_set(v___x_2044_, 1, v___x_2161_);
v___x_2163_ = v___x_2044_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_pos_2042_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2161_);
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
else
{
lean_object* v_pos_2167_; lean_object* v_err_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v_res_2022_);
v_pos_2167_ = lean_ctor_get(v___x_2041_, 0);
v_err_2168_ = lean_ctor_get(v___x_2041_, 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2041_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_err_2168_);
lean_inc(v_pos_2167_);
lean_dec(v___x_2041_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_pos_2167_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_err_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2022_);
goto v___jp_2026_;
}
v___jp_2026_:
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = lean_box(0);
if (v_isShared_2025_ == 0)
{
lean_ctor_set_tag(v___x_2024_, 1);
lean_ctor_set(v___x_2024_, 1, v___x_2027_);
v___x_2029_ = v___x_2024_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_pos_2021_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v_pos_2181_; lean_object* v_err_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
v_pos_2181_ = lean_ctor_get(v___x_2020_, 0);
v_err_2182_ = lean_ctor_get(v___x_2020_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2020_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_err_2182_);
lean_inc(v_pos_2181_);
lean_dec(v___x_2020_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_pos_2181_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_err_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
v___jp_1882_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1887_, 0, v_id_1883_);
lean_ctor_set(v___x_1887_, 1, v_message_1885_);
lean_ctor_set(v___x_1887_, 2, v_data_x3f_1886_);
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*3, v_code_1884_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 1, v___x_1887_);
lean_ctor_set(v___x_1870_, 0, v___x_1881_);
v___x_1889_ = v___x_1870_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
v___jp_1891_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1));
v___x_1893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1881_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
return v___x_1893_;
}
v___jp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_a_1895_);
v___x_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1881_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
return v___x_1897_;
}
v___jp_1898_:
{
lean_object* v___x_1899_; 
v___x_1899_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_1895_ = v___x_1899_;
goto v___jp_1894_;
}
}
}
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
lean_dec(v_res_1868_);
lean_dec_ref(v_input_1829_);
v___x_2194_ = lean_box(0);
if (v_isShared_1871_ == 0)
{
lean_ctor_set_tag(v___x_1870_, 1);
lean_ctor_set(v___x_1870_, 1, v___x_2194_);
v___x_2196_ = v___x_1870_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_pos_1867_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_2194_);
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
else
{
lean_object* v_pos_2199_; lean_object* v_err_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec_ref(v_input_1829_);
v_pos_2199_ = lean_ctor_get(v___x_1866_, 0);
v_err_2200_ = lean_ctor_get(v___x_1866_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_1866_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_err_2200_);
lean_inc(v_pos_2199_);
lean_dec(v___x_1866_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_pos_2199_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_err_2200_);
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
}
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec_ref(v_input_1829_);
v___x_2212_ = lean_box(0);
v___x_2213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2213_, 0, v_a_1830_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
return v___x_2213_;
}
v___jp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = lean_string_utf8_next_fast(v___y_1833_, v___y_1832_);
lean_dec(v___y_1832_);
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___y_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1835_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_pos_1837_; lean_object* v_res_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1846_; 
v_pos_1837_ = lean_ctor_get(v___x_1836_, 0);
v_res_1838_ = lean_ctor_get(v___x_1836_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1840_ = v___x_1836_;
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_res_1838_);
lean_inc(v_pos_1837_);
lean_dec(v___x_1836_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_res_1838_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 1, v___x_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_pos_1837_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_object* v_pos_1847_; lean_object* v_err_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
v_pos_1847_ = lean_ctor_get(v___x_1836_, 0);
v_err_1848_ = lean_ctor_get(v___x_1836_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1836_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_err_1848_);
lean_inc(v_pos_1847_);
lean_dec(v___x_1836_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_pos_1847_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_err_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object* v_input_2214_){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_inc_ref(v_input_2214_);
v___x_2215_ = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser), 2, 1);
lean_closure_set(v___x_2215_, 0, v_input_2214_);
v___x_2216_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2215_, v_input_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx(uint8_t v_x_2217_){
_start:
{
if (v_x_2217_ == 0)
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_unsigned_to_nat(0u);
return v___x_2218_;
}
else
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_unsigned_to_nat(1u);
return v___x_2219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___boxed(lean_object* v_x_2220_){
_start:
{
uint8_t v_x_boxed_2221_; lean_object* v_res_2222_; 
v_x_boxed_2221_ = lean_unbox(v_x_2220_);
v_res_2222_ = l_Lean_JsonRpc_MessageDirection_ctorIdx(v_x_boxed_2221_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object* v_k_2223_){
_start:
{
lean_inc(v_k_2223_);
return v_k_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object* v_k_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(v_k_2224_);
lean_dec(v_k_2224_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object* v_motive_2226_, lean_object* v_ctorIdx_2227_, uint8_t v_t_2228_, lean_object* v_h_2229_, lean_object* v_k_2230_){
_start:
{
lean_inc(v_k_2230_);
return v_k_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object* v_motive_2231_, lean_object* v_ctorIdx_2232_, lean_object* v_t_2233_, lean_object* v_h_2234_, lean_object* v_k_2235_){
_start:
{
uint8_t v_t_boxed_2236_; lean_object* v_res_2237_; 
v_t_boxed_2236_ = lean_unbox(v_t_2233_);
v_res_2237_ = l_Lean_JsonRpc_MessageDirection_ctorElim(v_motive_2231_, v_ctorIdx_2232_, v_t_boxed_2236_, v_h_2234_, v_k_2235_);
lean_dec(v_k_2235_);
lean_dec(v_ctorIdx_2232_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object* v_clientToServer_2238_){
_start:
{
lean_inc(v_clientToServer_2238_);
return v_clientToServer_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object* v_clientToServer_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(v_clientToServer_2239_);
lean_dec(v_clientToServer_2239_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object* v_motive_2241_, uint8_t v_t_2242_, lean_object* v_h_2243_, lean_object* v_clientToServer_2244_){
_start:
{
lean_inc(v_clientToServer_2244_);
return v_clientToServer_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object* v_motive_2245_, lean_object* v_t_2246_, lean_object* v_h_2247_, lean_object* v_clientToServer_2248_){
_start:
{
uint8_t v_t_boxed_2249_; lean_object* v_res_2250_; 
v_t_boxed_2249_ = lean_unbox(v_t_2246_);
v_res_2250_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(v_motive_2245_, v_t_boxed_2249_, v_h_2247_, v_clientToServer_2248_);
lean_dec(v_clientToServer_2248_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object* v_serverToClient_2251_){
_start:
{
lean_inc(v_serverToClient_2251_);
return v_serverToClient_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object* v_serverToClient_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(v_serverToClient_2252_);
lean_dec(v_serverToClient_2252_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object* v_motive_2254_, uint8_t v_t_2255_, lean_object* v_h_2256_, lean_object* v_serverToClient_2257_){
_start:
{
lean_inc(v_serverToClient_2257_);
return v_serverToClient_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object* v_motive_2258_, lean_object* v_t_2259_, lean_object* v_h_2260_, lean_object* v_serverToClient_2261_){
_start:
{
uint8_t v_t_boxed_2262_; lean_object* v_res_2263_; 
v_t_boxed_2262_ = lean_unbox(v_t_2259_);
v_res_2263_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(v_motive_2258_, v_t_boxed_2262_, v_h_2260_, v_serverToClient_2261_);
lean_dec(v_serverToClient_2261_);
return v_res_2263_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default(void){
_start:
{
uint8_t v___x_2264_; 
v___x_2264_ = 0;
return v___x_2264_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection(void){
_start:
{
uint8_t v___x_2265_; 
v___x_2265_ = 0;
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object* v_json_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Json_getTag_x3f(v_json_2280_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1));
return v___x_2282_;
}
else
{
lean_object* v_val_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v_val_2283_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_val_2283_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2284_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2));
v___x_2285_ = lean_string_dec_eq(v_val_2283_, v___x_2284_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3));
v___x_2287_ = lean_string_dec_eq(v_val_2283_, v___x_2286_);
lean_dec(v_val_2283_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; 
v___x_2288_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5));
return v___x_2288_;
}
else
{
lean_object* v___x_2289_; 
v___x_2289_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6));
return v___x_2289_;
}
}
else
{
lean_object* v___x_2290_; 
lean_dec(v_val_2283_);
v___x_2290_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7));
return v___x_2290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t v_x_2297_){
_start:
{
if (v_x_2297_ == 0)
{
lean_object* v___x_2298_; 
v___x_2298_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0));
return v___x_2298_;
}
else
{
lean_object* v___x_2299_; 
v___x_2299_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1));
return v___x_2299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object* v_x_2300_){
_start:
{
uint8_t v_x_44__boxed_2301_; lean_object* v_res_2302_; 
v_x_44__boxed_2301_ = lean_unbox(v_x_2300_);
v_res_2302_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_x_44__boxed_2301_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx(uint8_t v_x_2305_){
_start:
{
switch(v_x_2305_)
{
case 0:
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_unsigned_to_nat(0u);
return v___x_2306_;
}
case 1:
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_unsigned_to_nat(1u);
return v___x_2307_;
}
case 2:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_unsigned_to_nat(2u);
return v___x_2308_;
}
default: 
{
lean_object* v___x_2309_; 
v___x_2309_ = lean_unsigned_to_nat(3u);
return v___x_2309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___boxed(lean_object* v_x_2310_){
_start:
{
uint8_t v_x_boxed_2311_; lean_object* v_res_2312_; 
v_x_boxed_2311_ = lean_unbox(v_x_2310_);
v_res_2312_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_boxed_2311_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object* v_k_2313_){
_start:
{
lean_inc(v_k_2313_);
return v_k_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object* v_k_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_JsonRpc_MessageKind_ctorElim___redArg(v_k_2314_);
lean_dec(v_k_2314_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object* v_motive_2316_, lean_object* v_ctorIdx_2317_, uint8_t v_t_2318_, lean_object* v_h_2319_, lean_object* v_k_2320_){
_start:
{
lean_inc(v_k_2320_);
return v_k_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object* v_motive_2321_, lean_object* v_ctorIdx_2322_, lean_object* v_t_2323_, lean_object* v_h_2324_, lean_object* v_k_2325_){
_start:
{
uint8_t v_t_boxed_2326_; lean_object* v_res_2327_; 
v_t_boxed_2326_ = lean_unbox(v_t_2323_);
v_res_2327_ = l_Lean_JsonRpc_MessageKind_ctorElim(v_motive_2321_, v_ctorIdx_2322_, v_t_boxed_2326_, v_h_2324_, v_k_2325_);
lean_dec(v_k_2325_);
lean_dec(v_ctorIdx_2322_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object* v_request_2328_){
_start:
{
lean_inc(v_request_2328_);
return v_request_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object* v_request_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_JsonRpc_MessageKind_request_elim___redArg(v_request_2329_);
lean_dec(v_request_2329_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object* v_motive_2331_, uint8_t v_t_2332_, lean_object* v_h_2333_, lean_object* v_request_2334_){
_start:
{
lean_inc(v_request_2334_);
return v_request_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object* v_motive_2335_, lean_object* v_t_2336_, lean_object* v_h_2337_, lean_object* v_request_2338_){
_start:
{
uint8_t v_t_boxed_2339_; lean_object* v_res_2340_; 
v_t_boxed_2339_ = lean_unbox(v_t_2336_);
v_res_2340_ = l_Lean_JsonRpc_MessageKind_request_elim(v_motive_2335_, v_t_boxed_2339_, v_h_2337_, v_request_2338_);
lean_dec(v_request_2338_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object* v_notification_2341_){
_start:
{
lean_inc(v_notification_2341_);
return v_notification_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object* v_notification_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_JsonRpc_MessageKind_notification_elim___redArg(v_notification_2342_);
lean_dec(v_notification_2342_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object* v_motive_2344_, uint8_t v_t_2345_, lean_object* v_h_2346_, lean_object* v_notification_2347_){
_start:
{
lean_inc(v_notification_2347_);
return v_notification_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object* v_motive_2348_, lean_object* v_t_2349_, lean_object* v_h_2350_, lean_object* v_notification_2351_){
_start:
{
uint8_t v_t_boxed_2352_; lean_object* v_res_2353_; 
v_t_boxed_2352_ = lean_unbox(v_t_2349_);
v_res_2353_ = l_Lean_JsonRpc_MessageKind_notification_elim(v_motive_2348_, v_t_boxed_2352_, v_h_2350_, v_notification_2351_);
lean_dec(v_notification_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object* v_response_2354_){
_start:
{
lean_inc(v_response_2354_);
return v_response_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object* v_response_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_JsonRpc_MessageKind_response_elim___redArg(v_response_2355_);
lean_dec(v_response_2355_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object* v_motive_2357_, uint8_t v_t_2358_, lean_object* v_h_2359_, lean_object* v_response_2360_){
_start:
{
lean_inc(v_response_2360_);
return v_response_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object* v_motive_2361_, lean_object* v_t_2362_, lean_object* v_h_2363_, lean_object* v_response_2364_){
_start:
{
uint8_t v_t_boxed_2365_; lean_object* v_res_2366_; 
v_t_boxed_2365_ = lean_unbox(v_t_2362_);
v_res_2366_ = l_Lean_JsonRpc_MessageKind_response_elim(v_motive_2361_, v_t_boxed_2365_, v_h_2363_, v_response_2364_);
lean_dec(v_response_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object* v_responseError_2367_){
_start:
{
lean_inc(v_responseError_2367_);
return v_responseError_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object* v_responseError_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(v_responseError_2368_);
lean_dec(v_responseError_2368_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object* v_motive_2370_, uint8_t v_t_2371_, lean_object* v_h_2372_, lean_object* v_responseError_2373_){
_start:
{
lean_inc(v_responseError_2373_);
return v_responseError_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object* v_motive_2374_, lean_object* v_t_2375_, lean_object* v_h_2376_, lean_object* v_responseError_2377_){
_start:
{
uint8_t v_t_boxed_2378_; lean_object* v_res_2379_; 
v_t_boxed_2378_ = lean_unbox(v_t_2375_);
v_res_2379_ = l_Lean_JsonRpc_MessageKind_responseError_elim(v_motive_2374_, v_t_boxed_2378_, v_h_2376_, v_responseError_2377_);
lean_dec(v_responseError_2377_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object* v_json_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_Json_getTag_x3f(v_json_2400_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2402_; 
v___x_2402_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0));
return v___x_2402_;
}
else
{
lean_object* v_val_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v_val_2403_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_val_2403_);
lean_dec_ref_known(v___x_2401_, 1);
v___x_2404_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1));
v___x_2405_ = lean_string_dec_eq(v_val_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2));
v___x_2407_ = lean_string_dec_eq(v_val_2403_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3));
v___x_2409_ = lean_string_dec_eq(v_val_2403_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; uint8_t v___x_2411_; 
v___x_2410_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4));
v___x_2411_ = lean_string_dec_eq(v_val_2403_, v___x_2410_);
lean_dec(v_val_2403_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
v___x_2412_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5));
return v___x_2412_;
}
else
{
lean_object* v___x_2413_; 
v___x_2413_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6));
return v___x_2413_;
}
}
else
{
lean_object* v___x_2414_; 
lean_dec(v_val_2403_);
v___x_2414_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7));
return v___x_2414_;
}
}
else
{
lean_object* v___x_2415_; 
lean_dec(v_val_2403_);
v___x_2415_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8));
return v___x_2415_;
}
}
else
{
lean_object* v___x_2416_; 
lean_dec(v_val_2403_);
v___x_2416_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9));
return v___x_2416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t v_x_2427_){
_start:
{
switch(v_x_2427_)
{
case 0:
{
lean_object* v___x_2428_; 
v___x_2428_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0));
return v___x_2428_;
}
case 1:
{
lean_object* v___x_2429_; 
v___x_2429_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1));
return v___x_2429_;
}
case 2:
{
lean_object* v___x_2430_; 
v___x_2430_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2));
return v___x_2430_;
}
default: 
{
lean_object* v___x_2431_; 
v___x_2431_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3));
return v___x_2431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object* v_x_2432_){
_start:
{
uint8_t v_x_84__boxed_2433_; lean_object* v_res_2434_; 
v_x_84__boxed_2433_ = lean_unbox(v_x_2432_);
v_res_2434_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_x_84__boxed_2433_);
return v_res_2434_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object* v_x_2437_){
_start:
{
switch(lean_obj_tag(v_x_2437_))
{
case 0:
{
uint8_t v___x_2438_; 
v___x_2438_ = 0;
return v___x_2438_;
}
case 1:
{
uint8_t v___x_2439_; 
v___x_2439_ = 1;
return v___x_2439_;
}
case 2:
{
uint8_t v___x_2440_; 
v___x_2440_ = 2;
return v___x_2440_;
}
default: 
{
uint8_t v___x_2441_; 
v___x_2441_ = 3;
return v___x_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object* v_x_2442_){
_start:
{
uint8_t v_res_2443_; lean_object* v_r_2444_; 
v_res_2443_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_x_2442_);
lean_dec_ref(v_x_2442_);
v_r_2444_ = lean_box(v_res_2443_);
return v_r_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(lean_object* v_j_2445_, lean_object* v_k_2446_){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = l_Lean_Json_getObjValD(v_j_2445_, v_k_2446_);
v___x_2448_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0___boxed(lean_object* v_j_2449_, lean_object* v_k_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_j_2449_, v_k_2450_);
lean_dec_ref(v_k_2450_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage(lean_object* v_h_2454_, lean_object* v_nBytes_2455_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_IO_FS_Stream_readJson(v_h_2454_, v_nBytes_2455_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2577_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2577_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2577_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___y_2463_; uint8_t v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v_a_2477_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_a_2458_);
v___x_2489_ = l_Lean_Json_getObjVal_x3f(v_a_2458_, v___x_2488_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; 
lean_del_object(v___x_2460_);
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v_a_2477_ = v_a_2490_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2491_; 
v_a_2491_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v___x_2489_, 1);
if (lean_obj_tag(v_a_2491_) == 3)
{
lean_object* v_s_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
v_s_2492_ = lean_ctor_get(v_a_2491_, 0);
lean_inc_ref(v_s_2492_);
lean_dec_ref_known(v_a_2491_, 1);
v___x_2493_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_2494_ = lean_string_dec_eq(v_s_2492_, v___x_2493_);
lean_dec_ref(v_s_2492_);
if (v___x_2494_ == 0)
{
lean_del_object(v___x_2460_);
goto v___jp_2486_;
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_a_2458_);
v___x_2496_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_2458_, v___x_2495_);
if (lean_obj_tag(v___x_2496_) == 0)
{
goto v___jp_2525_;
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_a_2552_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2552_);
v___x_2553_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2458_);
v___x_2554_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2458_, v___x_2553_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_dec_ref_known(v___x_2554_, 1);
lean_dec(v_a_2552_);
goto v___jp_2525_;
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref_known(v___x_2496_, 1);
lean_del_object(v___x_2460_);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2576_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2576_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___y_2560_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2566_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2458_, v___x_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; 
lean_dec_ref_known(v___x_2566_, 1);
v___x_2567_ = lean_box(0);
v___y_2560_ = v___x_2567_;
goto v___jp_2559_;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
v_a_2568_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2566_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2566_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
v___y_2560_ = v___x_2573_;
goto v___jp_2559_;
}
}
}
v___jp_2559_:
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2561_, 0, v_a_2552_);
lean_ctor_set(v___x_2561_, 1, v_a_2555_);
lean_ctor_set(v___x_2561_, 2, v___y_2560_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set_tag(v___x_2557_, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2561_);
v___x_2563_ = v___x_2557_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
}
v___jp_2497_:
{
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2498_; 
lean_del_object(v___x_2460_);
v_a_2498_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2496_, 1);
v_a_2477_ = v_a_2498_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_a_2499_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2496_, 1);
v___x_2500_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
lean_inc(v_a_2458_);
v___x_2501_ = l_Lean_Json_getObjVal_x3f(v_a_2458_, v___x_2500_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; 
lean_dec(v_a_2499_);
lean_del_object(v___x_2460_);
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v_a_2477_ = v_a_2502_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_a_2503_ = lean_ctor_get(v___x_2501_, 0);
lean_inc_n(v_a_2503_, 2);
lean_dec_ref_known(v___x_2501_, 1);
v___x_2504_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_2505_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_2503_, v___x_2504_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; 
lean_dec(v_a_2503_);
lean_dec(v_a_2499_);
lean_del_object(v___x_2460_);
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v_a_2477_ = v_a_2506_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v_a_2507_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2508_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_2503_);
v___x_2509_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2503_, v___x_2508_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; 
lean_dec(v_a_2507_);
lean_dec(v_a_2503_);
lean_dec(v_a_2499_);
lean_del_object(v___x_2460_);
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref_known(v___x_2509_, 1);
v_a_2477_ = v_a_2510_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
lean_dec(v_a_2458_);
v_a_2511_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v___x_2509_, 1);
v___x_2512_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2513_ = l_Lean_Json_getObjVal_x3f(v_a_2503_, v___x_2512_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v___x_2514_; uint8_t v___x_2515_; 
lean_dec_ref_known(v___x_2513_, 1);
v___x_2514_ = lean_box(0);
v___x_2515_ = lean_unbox(v_a_2507_);
lean_dec(v_a_2507_);
v___y_2463_ = v_a_2511_;
v___y_2464_ = v___x_2515_;
v___y_2465_ = v_a_2499_;
v___y_2466_ = v___x_2514_;
goto v___jp_2462_;
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2524_; 
v_a_2516_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2518_ = v___x_2513_;
v_isShared_2519_ = v_isSharedCheck_2524_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2513_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2524_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
uint8_t v___x_2522_; 
v___x_2522_ = lean_unbox(v_a_2507_);
lean_dec(v_a_2507_);
v___y_2463_ = v_a_2511_;
v___y_2464_ = v___x_2522_;
v___y_2465_ = v_a_2499_;
v___y_2466_ = v___x_2521_;
goto v___jp_2462_;
}
}
}
}
}
}
}
}
v___jp_2525_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2458_);
v___x_2527_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2458_, v___x_2526_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_dec_ref_known(v___x_2527_, 1);
if (lean_obj_tag(v___x_2496_) == 0)
{
goto v___jp_2497_;
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v_a_2528_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2528_);
v___x_2529_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_2458_);
v___x_2530_ = l_Lean_Json_getObjVal_x3f(v_a_2458_, v___x_2529_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_dec_ref_known(v___x_2530_, 1);
lean_dec(v_a_2528_);
goto v___jp_2497_;
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2539_; 
lean_dec_ref_known(v___x_2496_, 1);
lean_del_object(v___x_2460_);
lean_dec(v_a_2458_);
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2535_, 0, v_a_2528_);
lean_ctor_set(v___x_2535_, 1, v_a_2531_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set_tag(v___x_2533_, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2535_);
v___x_2537_ = v___x_2533_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec_ref(v___x_2496_);
lean_del_object(v___x_2460_);
v_a_2540_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2541_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2542_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2458_, v___x_2541_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v___x_2543_; 
lean_dec_ref_known(v___x_2542_, 1);
v___x_2543_ = lean_box(0);
v___y_2472_ = v_a_2540_;
v___y_2473_ = v___x_2543_;
goto v___jp_2471_;
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
v_a_2544_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2542_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2542_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
v___y_2472_ = v_a_2540_;
v___y_2473_ = v___x_2549_;
goto v___jp_2471_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2491_);
lean_del_object(v___x_2460_);
goto v___jp_2486_;
}
}
v___jp_2462_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2467_, 0, v___y_2465_);
lean_ctor_set(v___x_2467_, 1, v___y_2463_);
lean_ctor_set(v___x_2467_, 2, v___y_2466_);
lean_ctor_set_uint8(v___x_2467_, sizeof(void*)*3, v___y_2464_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2467_);
v___x_2469_ = v___x_2460_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
v___jp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___y_2472_);
lean_ctor_set(v___x_2474_, 1, v___y_2473_);
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
return v___x_2475_;
}
v___jp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2478_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__0));
v___x_2479_ = l_Lean_Json_compress(v_a_2458_);
v___x_2480_ = lean_string_append(v___x_2478_, v___x_2479_);
lean_dec_ref(v___x_2479_);
v___x_2481_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__1));
v___x_2482_ = lean_string_append(v___x_2480_, v___x_2481_);
v___x_2483_ = lean_string_append(v___x_2482_, v_a_2477_);
lean_dec_ref(v_a_2477_);
v___x_2484_ = lean_mk_io_user_error(v___x_2483_);
v___x_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
return v___x_2485_;
}
v___jp_2486_:
{
lean_object* v___x_2487_; 
v___x_2487_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_2477_ = v___x_2487_;
goto v___jp_2476_;
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
v_a_2578_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2457_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2457_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage___boxed(lean_object* v_h_2586_, lean_object* v_nBytes_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_IO_FS_Stream_readMessage(v_h_2586_, v_nBytes_2587_);
lean_dec(v_nBytes_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg(lean_object* v_h_2597_, lean_object* v_nBytes_2598_, lean_object* v_expectedMethod_2599_, lean_object* v_inst_2600_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_IO_FS_Stream_readMessage(v_h_2597_, v_nBytes_2598_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2790_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2790_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2790_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
if (lean_obj_tag(v_a_2603_) == 0)
{
lean_object* v_id_2607_; lean_object* v_method_2608_; lean_object* v_params_x3f_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2649_; 
v_id_2607_ = lean_ctor_get(v_a_2603_, 0);
v_method_2608_ = lean_ctor_get(v_a_2603_, 1);
v_params_x3f_2609_ = lean_ctor_get(v_a_2603_, 2);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_a_2603_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2611_ = v_a_2603_;
v_isShared_2612_ = v_isSharedCheck_2649_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_params_x3f_2609_);
lean_inc(v_method_2608_);
lean_inc(v_id_2607_);
lean_dec(v_a_2603_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2649_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
uint8_t v___x_2613_; 
v___x_2613_ = lean_string_dec_eq(v_method_2608_, v_expectedMethod_2599_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
lean_del_object(v___x_2611_);
lean_dec(v_params_x3f_2609_);
lean_dec(v_id_2607_);
lean_dec_ref(v_inst_2600_);
v___x_2614_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2615_ = lean_string_append(v___x_2614_, v_expectedMethod_2599_);
lean_dec_ref(v_expectedMethod_2599_);
v___x_2616_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2617_ = lean_string_append(v___x_2615_, v___x_2616_);
v___x_2618_ = lean_string_append(v___x_2617_, v_method_2608_);
lean_dec_ref(v_method_2608_);
v___x_2619_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2620_ = lean_string_append(v___x_2618_, v___x_2619_);
v___x_2621_ = lean_mk_io_user_error(v___x_2620_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set_tag(v___x_2605_, 1);
lean_ctor_set(v___x_2605_, 0, v___x_2621_);
v___x_2623_ = v___x_2605_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec_ref(v_method_2608_);
v___x_2625_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2626_ = l_Lean_Option_toJson___redArg(v___x_2625_, v_params_x3f_2609_);
lean_inc(v___x_2626_);
v___x_2627_ = lean_apply_1(v_inst_2600_, v___x_2626_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
lean_del_object(v___x_2611_);
lean_dec(v_id_2607_);
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2629_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2630_ = l_Lean_Json_compress(v___x_2626_);
v___x_2631_ = lean_string_append(v___x_2629_, v___x_2630_);
lean_dec_ref(v___x_2630_);
v___x_2632_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2633_ = lean_string_append(v___x_2631_, v___x_2632_);
v___x_2634_ = lean_string_append(v___x_2633_, v_expectedMethod_2599_);
lean_dec_ref(v_expectedMethod_2599_);
v___x_2635_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2636_ = lean_string_append(v___x_2634_, v___x_2635_);
v___x_2637_ = lean_string_append(v___x_2636_, v_a_2628_);
lean_dec(v_a_2628_);
v___x_2638_ = lean_mk_io_user_error(v___x_2637_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set_tag(v___x_2605_, 1);
lean_ctor_set(v___x_2605_, 0, v___x_2638_);
v___x_2640_ = v___x_2605_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; 
lean_dec(v___x_2626_);
v_a_2642_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2627_, 1);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 2, v_a_2642_);
lean_ctor_set(v___x_2611_, 1, v_expectedMethod_2599_);
v___x_2644_ = v___x_2611_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_id_2607_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_expectedMethod_2599_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_a_2642_);
v___x_2644_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2646_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2644_);
v___x_2646_ = v___x_2605_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___y_2654_; 
lean_dec_ref(v_inst_2600_);
lean_dec_ref(v_expectedMethod_2599_);
v___x_2650_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__6));
v___x_2651_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2652_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2603_))
{
case 0:
{
lean_object* v_id_2665_; lean_object* v_method_2666_; lean_object* v_params_x3f_2667_; lean_object* v___x_2668_; lean_object* v___y_2670_; 
v_id_2665_ = lean_ctor_get(v_a_2603_, 0);
lean_inc(v_id_2665_);
v_method_2666_ = lean_ctor_get(v_a_2603_, 1);
lean_inc_ref(v_method_2666_);
v_params_x3f_2667_ = lean_ctor_get(v_a_2603_, 2);
lean_inc(v_params_x3f_2667_);
lean_dec_ref_known(v_a_2603_, 3);
v___x_2668_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2665_) == 0)
{
lean_object* v_s_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
v_s_2681_ = lean_ctor_get(v_id_2665_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_id_2665_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v_id_2665_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_s_2681_);
lean_dec(v_id_2665_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set_tag(v___x_2683_, 3);
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_s_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
v___y_2670_ = v___x_2686_;
goto v___jp_2669_;
}
}
}
else
{
lean_object* v_n_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
v_n_2689_ = lean_ctor_get(v_id_2665_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_id_2665_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v_id_2665_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_n_2689_);
lean_dec(v_id_2665_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set_tag(v___x_2691_, 2);
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_n_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
v___y_2670_ = v___x_2694_;
goto v___jp_2669_;
}
}
}
v___jp_2669_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2668_);
lean_ctor_set(v___x_2671_, 1, v___y_2670_);
v___x_2672_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2673_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_method_2666_);
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2671_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
v___x_2678_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2679_ = l_Lean_Json_opt___redArg(v___x_2651_, v___x_2678_, v_params_x3f_2667_);
v___x_2680_ = l_List_appendTR___redArg(v___x_2677_, v___x_2679_);
v___y_2654_ = v___x_2680_;
goto v___jp_2653_;
}
}
case 1:
{
lean_object* v_method_2697_; lean_object* v_params_x3f_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_method_2697_ = lean_ctor_get(v_a_2603_, 0);
lean_inc_ref(v_method_2697_);
v_params_x3f_2698_ = lean_ctor_get(v_a_2603_, 1);
lean_inc(v_params_x3f_2698_);
lean_dec_ref_known(v_a_2603_, 2);
v___x_2699_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2700_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2700_, 0, v_method_2697_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2703_ = l_Lean_Json_opt___redArg(v___x_2651_, v___x_2702_, v_params_x3f_2698_);
v___x_2704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2701_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___y_2654_ = v___x_2704_;
goto v___jp_2653_;
}
case 2:
{
lean_object* v_id_2705_; lean_object* v_result_2706_; lean_object* v___x_2707_; lean_object* v___y_2709_; 
v_id_2705_ = lean_ctor_get(v_a_2603_, 0);
lean_inc(v_id_2705_);
v_result_2706_ = lean_ctor_get(v_a_2603_, 1);
lean_inc(v_result_2706_);
lean_dec_ref_known(v_a_2603_, 2);
v___x_2707_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2705_) == 0)
{
lean_object* v_s_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
v_s_2716_ = lean_ctor_get(v_id_2705_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_id_2705_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v_id_2705_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_s_2716_);
lean_dec(v_id_2705_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set_tag(v___x_2718_, 3);
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_s_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
v___y_2709_ = v___x_2721_;
goto v___jp_2708_;
}
}
}
else
{
lean_object* v_n_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
v_n_2724_ = lean_ctor_get(v_id_2705_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v_id_2705_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v_id_2705_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_n_2724_);
lean_dec(v_id_2705_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set_tag(v___x_2726_, 2);
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_n_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
v___y_2709_ = v___x_2729_;
goto v___jp_2708_;
}
}
}
v___jp_2708_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2707_);
lean_ctor_set(v___x_2710_, 1, v___y_2709_);
v___x_2711_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
lean_ctor_set(v___x_2712_, 1, v_result_2706_);
v___x_2713_ = lean_box(0);
v___x_2714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2712_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
v___x_2715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2710_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___y_2654_ = v___x_2715_;
goto v___jp_2653_;
}
}
default: 
{
lean_object* v_id_2732_; uint8_t v_code_2733_; lean_object* v_message_2734_; lean_object* v_data_x3f_2735_; lean_object* v___x_2736_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___x_2756_; lean_object* v___y_2758_; 
v_id_2732_ = lean_ctor_get(v_a_2603_, 0);
lean_inc(v_id_2732_);
v_code_2733_ = lean_ctor_get_uint8(v_a_2603_, sizeof(void*)*3);
v_message_2734_ = lean_ctor_get(v_a_2603_, 1);
lean_inc_ref(v_message_2734_);
v_data_x3f_2735_ = lean_ctor_get(v_a_2603_, 2);
lean_inc(v_data_x3f_2735_);
lean_dec_ref_known(v_a_2603_, 3);
v___x_2736_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2756_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2732_) == 0)
{
lean_object* v_s_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
v_s_2774_ = lean_ctor_get(v_id_2732_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_id_2732_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v_id_2732_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_s_2774_);
lean_dec(v_id_2732_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 3);
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_s_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
v___y_2758_ = v___x_2779_;
goto v___jp_2757_;
}
}
}
else
{
lean_object* v_n_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_n_2782_ = lean_ctor_get(v_id_2732_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_id_2732_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v_id_2732_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_n_2782_);
lean_dec(v_id_2732_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set_tag(v___x_2784_, 2);
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_n_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
v___y_2758_ = v___x_2787_;
goto v___jp_2757_;
}
}
}
v___jp_2737_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_inc(v___y_2741_);
lean_inc_ref(v___y_2738_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___y_2738_);
lean_ctor_set(v___x_2742_, 1, v___y_2741_);
v___x_2743_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2744_, 0, v_message_2734_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = lean_box(0);
v___x_2747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2742_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2750_ = l_Lean_Json_opt___redArg(v___x_2736_, v___x_2749_, v_data_x3f_2735_);
v___x_2751_ = l_List_appendTR___redArg(v___x_2748_, v___x_2750_);
v___x_2752_ = l_Lean_Json_mkObj(v___x_2751_);
lean_dec(v___x_2751_);
lean_inc_ref(v___y_2739_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___y_2739_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
lean_ctor_set(v___x_2754_, 1, v___x_2746_);
v___x_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___y_2740_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___y_2654_ = v___x_2755_;
goto v___jp_2653_;
}
v___jp_2757_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2756_);
lean_ctor_set(v___x_2759_, 1, v___y_2758_);
v___x_2760_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2761_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2733_)
{
case 0:
{
lean_object* v___x_2762_; 
v___x_2762_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2762_;
goto v___jp_2737_;
}
case 1:
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2763_;
goto v___jp_2737_;
}
case 2:
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2764_;
goto v___jp_2737_;
}
case 3:
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2765_;
goto v___jp_2737_;
}
case 4:
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2766_;
goto v___jp_2737_;
}
case 5:
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2767_;
goto v___jp_2737_;
}
case 6:
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2768_;
goto v___jp_2737_;
}
case 7:
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2769_;
goto v___jp_2737_;
}
case 8:
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2770_;
goto v___jp_2737_;
}
case 9:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2771_;
goto v___jp_2737_;
}
case 10:
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2772_;
goto v___jp_2737_;
}
default: 
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2738_ = v___x_2761_;
v___y_2739_ = v___x_2760_;
v___y_2740_ = v___x_2759_;
v___y_2741_ = v___x_2773_;
goto v___jp_2737_;
}
}
}
}
}
v___jp_2653_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2652_);
lean_ctor_set(v___x_2655_, 1, v___y_2654_);
v___x_2656_ = l_Lean_Json_mkObj(v___x_2655_);
lean_dec_ref_known(v___x_2655_, 2);
v___x_2657_ = l_Lean_Json_compress(v___x_2656_);
v___x_2658_ = lean_string_append(v___x_2650_, v___x_2657_);
lean_dec_ref(v___x_2657_);
v___x_2659_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2660_ = lean_string_append(v___x_2658_, v___x_2659_);
v___x_2661_ = lean_mk_io_user_error(v___x_2660_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set_tag(v___x_2605_, 1);
lean_ctor_set(v___x_2605_, 0, v___x_2661_);
v___x_2663_ = v___x_2605_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec_ref(v_inst_2600_);
lean_dec_ref(v_expectedMethod_2599_);
v_a_2791_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2602_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2602_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* v_h_2799_, lean_object* v_nBytes_2800_, lean_object* v_expectedMethod_2801_, lean_object* v_inst_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2799_, v_nBytes_2800_, v_expectedMethod_2801_, v_inst_2802_);
lean_dec(v_nBytes_2800_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs(lean_object* v_h_2805_, lean_object* v_nBytes_2806_, lean_object* v_expectedMethod_2807_, lean_object* v_00_u03b1_2808_, lean_object* v_inst_2809_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2805_, v_nBytes_2806_, v_expectedMethod_2807_, v_inst_2809_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___boxed(lean_object* v_h_2812_, lean_object* v_nBytes_2813_, lean_object* v_expectedMethod_2814_, lean_object* v_00_u03b1_2815_, lean_object* v_inst_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_IO_FS_Stream_readRequestAs(v_h_2812_, v_nBytes_2813_, v_expectedMethod_2814_, v_00_u03b1_2815_, v_inst_2816_);
lean_dec(v_nBytes_2813_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg(lean_object* v_h_2820_, lean_object* v_nBytes_2821_, lean_object* v_expectedMethod_2822_, lean_object* v_inst_2823_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_IO_FS_Stream_readMessage(v_h_2820_, v_nBytes_2821_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_3012_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_3012_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_3012_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
if (lean_obj_tag(v_a_2826_) == 1)
{
lean_object* v_method_2830_; lean_object* v_params_x3f_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2871_; 
v_method_2830_ = lean_ctor_get(v_a_2826_, 0);
v_params_x3f_2831_ = lean_ctor_get(v_a_2826_, 1);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_a_2826_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2833_ = v_a_2826_;
v_isShared_2834_ = v_isSharedCheck_2871_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_params_x3f_2831_);
lean_inc(v_method_2830_);
lean_dec(v_a_2826_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2871_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
uint8_t v___x_2835_; 
v___x_2835_ = lean_string_dec_eq(v_method_2830_, v_expectedMethod_2822_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
lean_del_object(v___x_2833_);
lean_dec(v_params_x3f_2831_);
lean_dec_ref(v_inst_2823_);
v___x_2836_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2837_ = lean_string_append(v___x_2836_, v_expectedMethod_2822_);
lean_dec_ref(v_expectedMethod_2822_);
v___x_2838_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2839_ = lean_string_append(v___x_2837_, v___x_2838_);
v___x_2840_ = lean_string_append(v___x_2839_, v_method_2830_);
lean_dec_ref(v_method_2830_);
v___x_2841_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2842_ = lean_string_append(v___x_2840_, v___x_2841_);
v___x_2843_ = lean_mk_io_user_error(v___x_2842_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set_tag(v___x_2828_, 1);
lean_ctor_set(v___x_2828_, 0, v___x_2843_);
v___x_2845_ = v___x_2828_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
lean_dec_ref(v_method_2830_);
v___x_2847_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2848_ = l_Lean_Option_toJson___redArg(v___x_2847_, v_params_x3f_2831_);
lean_inc(v___x_2848_);
v___x_2849_ = lean_apply_1(v_inst_2823_, v___x_2848_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
lean_del_object(v___x_2833_);
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
v___x_2851_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2852_ = l_Lean_Json_compress(v___x_2848_);
v___x_2853_ = lean_string_append(v___x_2851_, v___x_2852_);
lean_dec_ref(v___x_2852_);
v___x_2854_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2855_ = lean_string_append(v___x_2853_, v___x_2854_);
v___x_2856_ = lean_string_append(v___x_2855_, v_expectedMethod_2822_);
lean_dec_ref(v_expectedMethod_2822_);
v___x_2857_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2858_ = lean_string_append(v___x_2856_, v___x_2857_);
v___x_2859_ = lean_string_append(v___x_2858_, v_a_2850_);
lean_dec(v_a_2850_);
v___x_2860_ = lean_mk_io_user_error(v___x_2859_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set_tag(v___x_2828_, 1);
lean_ctor_set(v___x_2828_, 0, v___x_2860_);
v___x_2862_ = v___x_2828_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; 
lean_dec(v___x_2848_);
v_a_2864_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2849_, 1);
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 0);
lean_ctor_set(v___x_2833_, 1, v_a_2864_);
lean_ctor_set(v___x_2833_, 0, v_expectedMethod_2822_);
v___x_2866_ = v___x_2833_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_expectedMethod_2822_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_a_2864_);
v___x_2866_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2868_; 
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2866_);
v___x_2868_ = v___x_2828_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___y_2876_; 
lean_dec_ref(v_inst_2823_);
lean_dec_ref(v_expectedMethod_2822_);
v___x_2872_ = ((lean_object*)(l_Lean_IO_FS_Stream_readNotificationAs___redArg___closed__0));
v___x_2873_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2874_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2826_))
{
case 0:
{
lean_object* v_id_2887_; lean_object* v_method_2888_; lean_object* v_params_x3f_2889_; lean_object* v___x_2890_; lean_object* v___y_2892_; 
v_id_2887_ = lean_ctor_get(v_a_2826_, 0);
lean_inc(v_id_2887_);
v_method_2888_ = lean_ctor_get(v_a_2826_, 1);
lean_inc_ref(v_method_2888_);
v_params_x3f_2889_ = lean_ctor_get(v_a_2826_, 2);
lean_inc(v_params_x3f_2889_);
lean_dec_ref_known(v_a_2826_, 3);
v___x_2890_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2887_) == 0)
{
lean_object* v_s_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
v_s_2903_ = lean_ctor_get(v_id_2887_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_id_2887_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v_id_2887_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_s_2903_);
lean_dec(v_id_2887_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set_tag(v___x_2905_, 3);
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_s_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
v___y_2892_ = v___x_2908_;
goto v___jp_2891_;
}
}
}
else
{
lean_object* v_n_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
v_n_2911_ = lean_ctor_get(v_id_2887_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_id_2887_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v_id_2887_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_n_2911_);
lean_dec(v_id_2887_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set_tag(v___x_2913_, 2);
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_n_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
v___y_2892_ = v___x_2916_;
goto v___jp_2891_;
}
}
}
v___jp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2890_);
lean_ctor_set(v___x_2893_, 1, v___y_2892_);
v___x_2894_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2895_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_method_2888_);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = lean_box(0);
v___x_2898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2893_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2901_ = l_Lean_Json_opt___redArg(v___x_2873_, v___x_2900_, v_params_x3f_2889_);
v___x_2902_ = l_List_appendTR___redArg(v___x_2899_, v___x_2901_);
v___y_2876_ = v___x_2902_;
goto v___jp_2875_;
}
}
case 1:
{
lean_object* v_method_2919_; lean_object* v_params_x3f_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_method_2919_ = lean_ctor_get(v_a_2826_, 0);
lean_inc_ref(v_method_2919_);
v_params_x3f_2920_ = lean_ctor_get(v_a_2826_, 1);
lean_inc(v_params_x3f_2920_);
lean_dec_ref_known(v_a_2826_, 2);
v___x_2921_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2922_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2922_, 0, v_method_2919_);
v___x_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2925_ = l_Lean_Json_opt___redArg(v___x_2873_, v___x_2924_, v_params_x3f_2920_);
v___x_2926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2923_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___y_2876_ = v___x_2926_;
goto v___jp_2875_;
}
case 2:
{
lean_object* v_id_2927_; lean_object* v_result_2928_; lean_object* v___x_2929_; lean_object* v___y_2931_; 
v_id_2927_ = lean_ctor_get(v_a_2826_, 0);
lean_inc(v_id_2927_);
v_result_2928_ = lean_ctor_get(v_a_2826_, 1);
lean_inc(v_result_2928_);
lean_dec_ref_known(v_a_2826_, 2);
v___x_2929_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2927_) == 0)
{
lean_object* v_s_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
v_s_2938_ = lean_ctor_get(v_id_2927_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_id_2927_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v_id_2927_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_s_2938_);
lean_dec(v_id_2927_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set_tag(v___x_2940_, 3);
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_s_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
v___y_2931_ = v___x_2943_;
goto v___jp_2930_;
}
}
}
else
{
lean_object* v_n_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
v_n_2946_ = lean_ctor_get(v_id_2927_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_id_2927_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v_id_2927_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_n_2946_);
lean_dec(v_id_2927_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set_tag(v___x_2948_, 2);
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_n_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
v___y_2931_ = v___x_2951_;
goto v___jp_2930_;
}
}
}
v___jp_2930_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2929_);
lean_ctor_set(v___x_2932_, 1, v___y_2931_);
v___x_2933_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
lean_ctor_set(v___x_2934_, 1, v_result_2928_);
v___x_2935_ = lean_box(0);
v___x_2936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2934_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
v___x_2937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2932_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___y_2876_ = v___x_2937_;
goto v___jp_2875_;
}
}
default: 
{
lean_object* v_id_2954_; uint8_t v_code_2955_; lean_object* v_message_2956_; lean_object* v_data_x3f_2957_; lean_object* v___x_2958_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___x_2978_; lean_object* v___y_2980_; 
v_id_2954_ = lean_ctor_get(v_a_2826_, 0);
lean_inc(v_id_2954_);
v_code_2955_ = lean_ctor_get_uint8(v_a_2826_, sizeof(void*)*3);
v_message_2956_ = lean_ctor_get(v_a_2826_, 1);
lean_inc_ref(v_message_2956_);
v_data_x3f_2957_ = lean_ctor_get(v_a_2826_, 2);
lean_inc(v_data_x3f_2957_);
lean_dec_ref_known(v_a_2826_, 3);
v___x_2958_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2978_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2954_) == 0)
{
lean_object* v_s_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
v_s_2996_ = lean_ctor_get(v_id_2954_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_id_2954_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v_id_2954_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_s_2996_);
lean_dec(v_id_2954_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
lean_ctor_set_tag(v___x_2998_, 3);
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_s_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
v___y_2980_ = v___x_3001_;
goto v___jp_2979_;
}
}
}
else
{
lean_object* v_n_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
v_n_3004_ = lean_ctor_get(v_id_2954_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_id_2954_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v_id_2954_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_n_3004_);
lean_dec(v_id_2954_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
lean_ctor_set_tag(v___x_3006_, 2);
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_n_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
v___y_2980_ = v___x_3009_;
goto v___jp_2979_;
}
}
}
v___jp_2959_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_inc(v___y_2963_);
lean_inc_ref(v___y_2961_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___y_2961_);
lean_ctor_set(v___x_2964_, 1, v___y_2963_);
v___x_2965_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2966_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2966_, 0, v_message_2956_);
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2965_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2967_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___x_2970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2964_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___x_2971_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2972_ = l_Lean_Json_opt___redArg(v___x_2958_, v___x_2971_, v_data_x3f_2957_);
v___x_2973_ = l_List_appendTR___redArg(v___x_2970_, v___x_2972_);
v___x_2974_ = l_Lean_Json_mkObj(v___x_2973_);
lean_dec(v___x_2973_);
lean_inc_ref(v___y_2962_);
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___y_2962_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v___x_2968_);
v___x_2977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___y_2960_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___y_2876_ = v___x_2977_;
goto v___jp_2875_;
}
v___jp_2979_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2978_);
lean_ctor_set(v___x_2981_, 1, v___y_2980_);
v___x_2982_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2983_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2955_)
{
case 0:
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2984_;
goto v___jp_2959_;
}
case 1:
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2985_;
goto v___jp_2959_;
}
case 2:
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2986_;
goto v___jp_2959_;
}
case 3:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2987_;
goto v___jp_2959_;
}
case 4:
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2988_;
goto v___jp_2959_;
}
case 5:
{
lean_object* v___x_2989_; 
v___x_2989_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2989_;
goto v___jp_2959_;
}
case 6:
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2990_;
goto v___jp_2959_;
}
case 7:
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2991_;
goto v___jp_2959_;
}
case 8:
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2992_;
goto v___jp_2959_;
}
case 9:
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2993_;
goto v___jp_2959_;
}
case 10:
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2994_;
goto v___jp_2959_;
}
default: 
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2960_ = v___x_2981_;
v___y_2961_ = v___x_2983_;
v___y_2962_ = v___x_2982_;
v___y_2963_ = v___x_2995_;
goto v___jp_2959_;
}
}
}
}
}
v___jp_2875_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2874_);
lean_ctor_set(v___x_2877_, 1, v___y_2876_);
v___x_2878_ = l_Lean_Json_mkObj(v___x_2877_);
lean_dec_ref_known(v___x_2877_, 2);
v___x_2879_ = l_Lean_Json_compress(v___x_2878_);
v___x_2880_ = lean_string_append(v___x_2872_, v___x_2879_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2882_ = lean_string_append(v___x_2880_, v___x_2881_);
v___x_2883_ = lean_mk_io_user_error(v___x_2882_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set_tag(v___x_2828_, 1);
lean_ctor_set(v___x_2828_, 0, v___x_2883_);
v___x_2885_ = v___x_2828_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref(v_inst_2823_);
lean_dec_ref(v_expectedMethod_2822_);
v_a_3013_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2825_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2825_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* v_h_3021_, lean_object* v_nBytes_3022_, lean_object* v_expectedMethod_3023_, lean_object* v_inst_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3021_, v_nBytes_3022_, v_expectedMethod_3023_, v_inst_3024_);
lean_dec(v_nBytes_3022_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs(lean_object* v_h_3027_, lean_object* v_nBytes_3028_, lean_object* v_expectedMethod_3029_, lean_object* v_00_u03b1_3030_, lean_object* v_inst_3031_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3027_, v_nBytes_3028_, v_expectedMethod_3029_, v_inst_3031_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___boxed(lean_object* v_h_3034_, lean_object* v_nBytes_3035_, lean_object* v_expectedMethod_3036_, lean_object* v_00_u03b1_3037_, lean_object* v_inst_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_IO_FS_Stream_readNotificationAs(v_h_3034_, v_nBytes_3035_, v_expectedMethod_3036_, v_00_u03b1_3037_, v_inst_3038_);
lean_dec(v_nBytes_3035_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg(lean_object* v_h_3045_, lean_object* v_nBytes_3046_, lean_object* v_expectedID_3047_, lean_object* v_inst_3048_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_IO_FS_Stream_readMessage(v_h_3045_, v_nBytes_3046_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3254_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3053_ = v___x_3050_;
v_isShared_3054_ = v_isSharedCheck_3254_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3254_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___y_3056_; lean_object* v___y_3057_; 
if (lean_obj_tag(v_a_3051_) == 2)
{
lean_object* v_id_3063_; lean_object* v_result_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3115_; 
v_id_3063_ = lean_ctor_get(v_a_3051_, 0);
v_result_3064_ = lean_ctor_get(v_a_3051_, 1);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_a_3051_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3066_ = v_a_3051_;
v_isShared_3067_ = v_isSharedCheck_3115_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_result_3064_);
lean_inc(v_id_3063_);
lean_dec(v_a_3051_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3115_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
uint8_t v___x_3068_; 
v___x_3068_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3063_, v_expectedID_3047_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v___y_3071_; 
lean_del_object(v___x_3066_);
lean_dec(v_result_3064_);
lean_dec_ref(v_inst_3048_);
v___x_3069_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__0));
switch(lean_obj_tag(v_expectedID_3047_))
{
case 0:
{
lean_object* v_s_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_s_3081_ = lean_ctor_get(v_expectedID_3047_, 0);
lean_inc_ref(v_s_3081_);
lean_dec_ref_known(v_expectedID_3047_, 1);
v___x_3082_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3083_ = lean_string_append(v___x_3082_, v_s_3081_);
lean_dec_ref(v_s_3081_);
v___x_3084_ = lean_string_append(v___x_3083_, v___x_3082_);
v___y_3071_ = v___x_3084_;
goto v___jp_3070_;
}
case 1:
{
lean_object* v_n_3085_; lean_object* v___x_3086_; 
v_n_3085_ = lean_ctor_get(v_expectedID_3047_, 0);
lean_inc_ref(v_n_3085_);
lean_dec_ref_known(v_expectedID_3047_, 1);
v___x_3086_ = l_Lean_JsonNumber_toString(v_n_3085_);
v___y_3071_ = v___x_3086_;
goto v___jp_3070_;
}
default: 
{
lean_object* v___x_3087_; 
v___x_3087_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___y_3071_ = v___x_3087_;
goto v___jp_3070_;
}
}
v___jp_3070_:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = lean_string_append(v___x_3069_, v___y_3071_);
lean_dec_ref(v___y_3071_);
v___x_3073_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__1));
v___x_3074_ = lean_string_append(v___x_3072_, v___x_3073_);
if (lean_obj_tag(v_id_3063_) == 0)
{
lean_object* v_s_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_s_3075_ = lean_ctor_get(v_id_3063_, 0);
lean_inc_ref(v_s_3075_);
lean_dec_ref_known(v_id_3063_, 1);
v___x_3076_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3077_ = lean_string_append(v___x_3076_, v_s_3075_);
lean_dec_ref(v_s_3075_);
v___x_3078_ = lean_string_append(v___x_3077_, v___x_3076_);
v___y_3056_ = v___x_3074_;
v___y_3057_ = v___x_3078_;
goto v___jp_3055_;
}
else
{
lean_object* v_n_3079_; lean_object* v___x_3080_; 
v_n_3079_ = lean_ctor_get(v_id_3063_, 0);
lean_inc_ref(v_n_3079_);
lean_dec_ref_known(v_id_3063_, 1);
v___x_3080_ = l_Lean_JsonNumber_toString(v_n_3079_);
v___y_3056_ = v___x_3074_;
v___y_3057_ = v___x_3080_;
goto v___jp_3055_;
}
}
}
else
{
lean_object* v___x_3088_; 
lean_dec(v_id_3063_);
lean_del_object(v___x_3053_);
lean_inc(v_result_3064_);
v___x_3088_ = lean_apply_1(v_inst_3048_, v_result_3064_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3103_; 
lean_del_object(v___x_3066_);
lean_dec(v_expectedID_3047_);
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3103_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3103_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3093_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__2));
v___x_3094_ = l_Lean_Json_compress(v_result_3064_);
v___x_3095_ = lean_string_append(v___x_3093_, v___x_3094_);
lean_dec_ref(v___x_3094_);
v___x_3096_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_3097_ = lean_string_append(v___x_3095_, v___x_3096_);
v___x_3098_ = lean_string_append(v___x_3097_, v_a_3089_);
lean_dec(v_a_3089_);
v___x_3099_ = lean_mk_io_user_error(v___x_3098_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set_tag(v___x_3091_, 1);
lean_ctor_set(v___x_3091_, 0, v___x_3099_);
v___x_3101_ = v___x_3091_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3114_; 
lean_dec(v_result_3064_);
v_a_3104_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3106_ = v___x_3088_;
v_isShared_3107_ = v_isSharedCheck_3114_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3088_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3114_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3067_ == 0)
{
lean_ctor_set_tag(v___x_3066_, 0);
lean_ctor_set(v___x_3066_, 1, v_a_3104_);
lean_ctor_set(v___x_3066_, 0, v_expectedID_3047_);
v___x_3109_ = v___x_3066_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_expectedID_3047_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3111_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3109_);
v___x_3111_ = v___x_3106_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___y_3120_; 
lean_del_object(v___x_3053_);
lean_dec_ref(v_inst_3048_);
lean_dec(v_expectedID_3047_);
v___x_3116_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__3));
v___x_3117_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_3118_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_3051_))
{
case 0:
{
lean_object* v_id_3129_; lean_object* v_method_3130_; lean_object* v_params_x3f_3131_; lean_object* v___x_3132_; lean_object* v___y_3134_; 
v_id_3129_ = lean_ctor_get(v_a_3051_, 0);
lean_inc(v_id_3129_);
v_method_3130_ = lean_ctor_get(v_a_3051_, 1);
lean_inc_ref(v_method_3130_);
v_params_x3f_3131_ = lean_ctor_get(v_a_3051_, 2);
lean_inc(v_params_x3f_3131_);
lean_dec_ref_known(v_a_3051_, 3);
v___x_3132_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3129_) == 0)
{
lean_object* v_s_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
v_s_3145_ = lean_ctor_get(v_id_3129_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_id_3129_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v_id_3129_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_s_3145_);
lean_dec(v_id_3129_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 3);
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_s_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
v___y_3134_ = v___x_3150_;
goto v___jp_3133_;
}
}
}
else
{
lean_object* v_n_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
v_n_3153_ = lean_ctor_get(v_id_3129_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_id_3129_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v_id_3129_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_n_3153_);
lean_dec(v_id_3129_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 2);
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_n_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
v___y_3134_ = v___x_3158_;
goto v___jp_3133_;
}
}
}
v___jp_3133_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3132_);
lean_ctor_set(v___x_3135_, 1, v___y_3134_);
v___x_3136_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3137_, 0, v_method_3130_);
v___x_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = lean_box(0);
v___x_3140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3135_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3143_ = l_Lean_Json_opt___redArg(v___x_3117_, v___x_3142_, v_params_x3f_3131_);
v___x_3144_ = l_List_appendTR___redArg(v___x_3141_, v___x_3143_);
v___y_3120_ = v___x_3144_;
goto v___jp_3119_;
}
}
case 1:
{
lean_object* v_method_3161_; lean_object* v_params_x3f_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v_method_3161_ = lean_ctor_get(v_a_3051_, 0);
lean_inc_ref(v_method_3161_);
v_params_x3f_3162_ = lean_ctor_get(v_a_3051_, 1);
lean_inc(v_params_x3f_3162_);
lean_dec_ref_known(v_a_3051_, 2);
v___x_3163_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3164_, 0, v_method_3161_);
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3163_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3167_ = l_Lean_Json_opt___redArg(v___x_3117_, v___x_3166_, v_params_x3f_3162_);
v___x_3168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3165_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___y_3120_ = v___x_3168_;
goto v___jp_3119_;
}
case 2:
{
lean_object* v_id_3169_; lean_object* v_result_3170_; lean_object* v___x_3171_; lean_object* v___y_3173_; 
v_id_3169_ = lean_ctor_get(v_a_3051_, 0);
lean_inc(v_id_3169_);
v_result_3170_ = lean_ctor_get(v_a_3051_, 1);
lean_inc(v_result_3170_);
lean_dec_ref_known(v_a_3051_, 2);
v___x_3171_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3169_) == 0)
{
lean_object* v_s_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
v_s_3180_ = lean_ctor_get(v_id_3169_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v_id_3169_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v_id_3169_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_s_3180_);
lean_dec(v_id_3169_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
lean_ctor_set_tag(v___x_3182_, 3);
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_s_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
v___y_3173_ = v___x_3185_;
goto v___jp_3172_;
}
}
}
else
{
lean_object* v_n_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
v_n_3188_ = lean_ctor_get(v_id_3169_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_id_3169_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v_id_3169_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_n_3188_);
lean_dec(v_id_3169_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
lean_ctor_set_tag(v___x_3190_, 2);
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_n_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
v___y_3173_ = v___x_3193_;
goto v___jp_3172_;
}
}
}
v___jp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3171_);
lean_ctor_set(v___x_3174_, 1, v___y_3173_);
v___x_3175_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v_result_3170_);
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3176_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3174_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___y_3120_ = v___x_3179_;
goto v___jp_3119_;
}
}
default: 
{
lean_object* v_id_3196_; uint8_t v_code_3197_; lean_object* v_message_3198_; lean_object* v_data_x3f_3199_; lean_object* v___x_3200_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___x_3220_; lean_object* v___y_3222_; 
v_id_3196_ = lean_ctor_get(v_a_3051_, 0);
lean_inc(v_id_3196_);
v_code_3197_ = lean_ctor_get_uint8(v_a_3051_, sizeof(void*)*3);
v_message_3198_ = lean_ctor_get(v_a_3051_, 1);
lean_inc_ref(v_message_3198_);
v_data_x3f_3199_ = lean_ctor_get(v_a_3051_, 2);
lean_inc(v_data_x3f_3199_);
lean_dec_ref_known(v_a_3051_, 3);
v___x_3200_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_3220_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3196_) == 0)
{
lean_object* v_s_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
v_s_3238_ = lean_ctor_get(v_id_3196_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_id_3196_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v_id_3196_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_s_3238_);
lean_dec(v_id_3196_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
lean_ctor_set_tag(v___x_3240_, 3);
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_s_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
v___y_3222_ = v___x_3243_;
goto v___jp_3221_;
}
}
}
else
{
lean_object* v_n_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
v_n_3246_ = lean_ctor_get(v_id_3196_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_id_3196_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v_id_3196_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_n_3246_);
lean_dec(v_id_3196_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
lean_ctor_set_tag(v___x_3248_, 2);
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_n_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
v___y_3222_ = v___x_3251_;
goto v___jp_3221_;
}
}
}
v___jp_3201_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_inc(v___y_3205_);
lean_inc_ref(v___y_3203_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___y_3203_);
lean_ctor_set(v___x_3206_, 1, v___y_3205_);
v___x_3207_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3208_, 0, v_message_3198_);
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3207_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = lean_box(0);
v___x_3211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3206_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3214_ = l_Lean_Json_opt___redArg(v___x_3200_, v___x_3213_, v_data_x3f_3199_);
v___x_3215_ = l_List_appendTR___redArg(v___x_3212_, v___x_3214_);
v___x_3216_ = l_Lean_Json_mkObj(v___x_3215_);
lean_dec(v___x_3215_);
lean_inc_ref(v___y_3202_);
v___x_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___y_3202_);
lean_ctor_set(v___x_3217_, 1, v___x_3216_);
v___x_3218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v___x_3210_);
v___x_3219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___y_3204_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___y_3120_ = v___x_3219_;
goto v___jp_3119_;
}
v___jp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3220_);
lean_ctor_set(v___x_3223_, 1, v___y_3222_);
v___x_3224_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3225_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3197_)
{
case 0:
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3226_;
goto v___jp_3201_;
}
case 1:
{
lean_object* v___x_3227_; 
v___x_3227_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3227_;
goto v___jp_3201_;
}
case 2:
{
lean_object* v___x_3228_; 
v___x_3228_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3228_;
goto v___jp_3201_;
}
case 3:
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3229_;
goto v___jp_3201_;
}
case 4:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3230_;
goto v___jp_3201_;
}
case 5:
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3231_;
goto v___jp_3201_;
}
case 6:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3232_;
goto v___jp_3201_;
}
case 7:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3233_;
goto v___jp_3201_;
}
case 8:
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3234_;
goto v___jp_3201_;
}
case 9:
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3235_;
goto v___jp_3201_;
}
case 10:
{
lean_object* v___x_3236_; 
v___x_3236_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3236_;
goto v___jp_3201_;
}
default: 
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3202_ = v___x_3224_;
v___y_3203_ = v___x_3225_;
v___y_3204_ = v___x_3223_;
v___y_3205_ = v___x_3237_;
goto v___jp_3201_;
}
}
}
}
}
v___jp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3118_);
lean_ctor_set(v___x_3121_, 1, v___y_3120_);
v___x_3122_ = l_Lean_Json_mkObj(v___x_3121_);
lean_dec_ref_known(v___x_3121_, 2);
v___x_3123_ = l_Lean_Json_compress(v___x_3122_);
v___x_3124_ = lean_string_append(v___x_3116_, v___x_3123_);
lean_dec_ref(v___x_3123_);
v___x_3125_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_3126_ = lean_string_append(v___x_3124_, v___x_3125_);
v___x_3127_ = lean_mk_io_user_error(v___x_3126_);
v___x_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
return v___x_3128_;
}
}
v___jp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3058_ = lean_string_append(v___y_3056_, v___y_3057_);
lean_dec_ref(v___y_3057_);
v___x_3059_ = lean_mk_io_user_error(v___x_3058_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set_tag(v___x_3053_, 1);
lean_ctor_set(v___x_3053_, 0, v___x_3059_);
v___x_3061_ = v___x_3053_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v_inst_3048_);
lean_dec(v_expectedID_3047_);
v_a_3255_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3050_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3050_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* v_h_3263_, lean_object* v_nBytes_3264_, lean_object* v_expectedID_3265_, lean_object* v_inst_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3263_, v_nBytes_3264_, v_expectedID_3265_, v_inst_3266_);
lean_dec(v_nBytes_3264_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs(lean_object* v_h_3269_, lean_object* v_nBytes_3270_, lean_object* v_expectedID_3271_, lean_object* v_00_u03b1_3272_, lean_object* v_inst_3273_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3269_, v_nBytes_3270_, v_expectedID_3271_, v_inst_3273_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___boxed(lean_object* v_h_3276_, lean_object* v_nBytes_3277_, lean_object* v_expectedID_3278_, lean_object* v_00_u03b1_3279_, lean_object* v_inst_3280_, lean_object* v_a_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_IO_FS_Stream_readResponseAs(v_h_3276_, v_nBytes_3277_, v_expectedID_3278_, v_00_u03b1_3279_, v_inst_3280_);
lean_dec(v_nBytes_3277_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(lean_object* v_k_3283_, lean_object* v_x_3284_){
_start:
{
if (lean_obj_tag(v_x_3284_) == 0)
{
lean_object* v___x_3285_; 
lean_dec_ref(v_k_3283_);
v___x_3285_ = lean_box(0);
return v___x_3285_;
}
else
{
lean_object* v_val_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_val_3286_ = lean_ctor_get(v_x_3284_, 0);
lean_inc(v_val_3286_);
lean_dec_ref_known(v_x_3284_, 1);
v___x_3287_ = l_Lean_Json_Structured_toJson(v_val_3286_);
v___x_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3288_, 0, v_k_3283_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
return v___x_3290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(lean_object* v_k_3291_, lean_object* v_x_3292_){
_start:
{
if (lean_obj_tag(v_x_3292_) == 0)
{
lean_object* v___x_3293_; 
lean_dec_ref(v_k_3291_);
v___x_3293_ = lean_box(0);
return v___x_3293_;
}
else
{
lean_object* v_val_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_val_3294_ = lean_ctor_get(v_x_3292_, 0);
lean_inc(v_val_3294_);
v___x_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3295_, 0, v_k_3291_);
lean_ctor_set(v___x_3295_, 1, v_val_3294_);
v___x_3296_ = lean_box(0);
v___x_3297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* v_k_3298_, lean_object* v_x_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v_k_3298_, v_x_3299_);
lean_dec(v_x_3299_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage(lean_object* v_h_3301_, lean_object* v_m_3302_){
_start:
{
lean_object* v___x_3304_; lean_object* v___y_3306_; 
v___x_3304_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_3302_))
{
case 0:
{
lean_object* v_id_3310_; lean_object* v_method_3311_; lean_object* v_params_x3f_3312_; lean_object* v___x_3313_; lean_object* v___y_3315_; 
v_id_3310_ = lean_ctor_get(v_m_3302_, 0);
lean_inc(v_id_3310_);
v_method_3311_ = lean_ctor_get(v_m_3302_, 1);
lean_inc_ref(v_method_3311_);
v_params_x3f_3312_ = lean_ctor_get(v_m_3302_, 2);
lean_inc(v_params_x3f_3312_);
lean_dec_ref_known(v_m_3302_, 3);
v___x_3313_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3310_))
{
case 0:
{
lean_object* v_s_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
v_s_3326_ = lean_ctor_get(v_id_3310_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v_id_3310_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v_id_3310_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_s_3326_);
lean_dec(v_id_3310_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
lean_ctor_set_tag(v___x_3328_, 3);
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_s_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
v___y_3315_ = v___x_3331_;
goto v___jp_3314_;
}
}
}
case 1:
{
lean_object* v_n_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
v_n_3334_ = lean_ctor_get(v_id_3310_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_id_3310_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v_id_3310_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_n_3334_);
lean_dec(v_id_3310_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set_tag(v___x_3336_, 2);
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_n_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
v___y_3315_ = v___x_3339_;
goto v___jp_3314_;
}
}
}
default: 
{
lean_object* v___x_3342_; 
v___x_3342_ = lean_box(0);
v___y_3315_ = v___x_3342_;
goto v___jp_3314_;
}
}
v___jp_3314_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3313_);
lean_ctor_set(v___x_3316_, 1, v___y_3315_);
v___x_3317_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3318_, 0, v_method_3311_);
v___x_3319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3317_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___x_3320_ = lean_box(0);
v___x_3321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3319_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___x_3322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3316_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3324_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3323_, v_params_x3f_3312_);
v___x_3325_ = l_List_appendTR___redArg(v___x_3322_, v___x_3324_);
v___y_3306_ = v___x_3325_;
goto v___jp_3305_;
}
}
case 1:
{
lean_object* v_method_3343_; lean_object* v_params_x3f_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3356_; 
v_method_3343_ = lean_ctor_get(v_m_3302_, 0);
v_params_x3f_3344_ = lean_ctor_get(v_m_3302_, 1);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_m_3302_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3346_ = v_m_3302_;
v_isShared_3347_ = v_isSharedCheck_3356_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_params_x3f_3344_);
lean_inc(v_method_3343_);
lean_dec(v_m_3302_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3356_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3351_; 
v___x_3348_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3349_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_method_3343_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set_tag(v___x_3346_, 0);
lean_ctor_set(v___x_3346_, 1, v___x_3349_);
lean_ctor_set(v___x_3346_, 0, v___x_3348_);
v___x_3351_ = v___x_3346_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3352_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3353_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3352_, v_params_x3f_3344_);
v___x_3354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3351_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___y_3306_ = v___x_3354_;
goto v___jp_3305_;
}
}
}
case 2:
{
lean_object* v_id_3357_; lean_object* v_result_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3390_; 
v_id_3357_ = lean_ctor_get(v_m_3302_, 0);
v_result_3358_ = lean_ctor_get(v_m_3302_, 1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_m_3302_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3360_ = v_m_3302_;
v_isShared_3361_ = v_isSharedCheck_3390_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_result_3358_);
lean_inc(v_id_3357_);
lean_dec(v_m_3302_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3390_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___y_3364_; 
v___x_3362_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3357_))
{
case 0:
{
lean_object* v_s_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
v_s_3373_ = lean_ctor_get(v_id_3357_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_id_3357_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v_id_3357_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_s_3373_);
lean_dec(v_id_3357_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 3);
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_s_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
v___y_3364_ = v___x_3378_;
goto v___jp_3363_;
}
}
}
case 1:
{
lean_object* v_n_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
v_n_3381_ = lean_ctor_get(v_id_3357_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_id_3357_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v_id_3357_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_n_3381_);
lean_dec(v_id_3357_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set_tag(v___x_3383_, 2);
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_n_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
v___y_3364_ = v___x_3386_;
goto v___jp_3363_;
}
}
}
default: 
{
lean_object* v___x_3389_; 
v___x_3389_ = lean_box(0);
v___y_3364_ = v___x_3389_;
goto v___jp_3363_;
}
}
v___jp_3363_:
{
lean_object* v___x_3366_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 0);
lean_ctor_set(v___x_3360_, 1, v___y_3364_);
lean_ctor_set(v___x_3360_, 0, v___x_3362_);
v___x_3366_ = v___x_3360_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v___y_3364_);
v___x_3366_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3367_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
lean_ctor_set(v___x_3368_, 1, v_result_3358_);
v___x_3369_ = lean_box(0);
v___x_3370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3368_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3366_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___y_3306_ = v___x_3371_;
goto v___jp_3305_;
}
}
}
}
default: 
{
lean_object* v_id_3391_; uint8_t v_code_3392_; lean_object* v_message_3393_; lean_object* v_data_x3f_3394_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___x_3414_; lean_object* v___y_3416_; 
v_id_3391_ = lean_ctor_get(v_m_3302_, 0);
lean_inc(v_id_3391_);
v_code_3392_ = lean_ctor_get_uint8(v_m_3302_, sizeof(void*)*3);
v_message_3393_ = lean_ctor_get(v_m_3302_, 1);
lean_inc_ref(v_message_3393_);
v_data_x3f_3394_ = lean_ctor_get(v_m_3302_, 2);
lean_inc(v_data_x3f_3394_);
lean_dec_ref_known(v_m_3302_, 3);
v___x_3414_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3391_))
{
case 0:
{
lean_object* v_s_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
v_s_3432_ = lean_ctor_get(v_id_3391_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_id_3391_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v_id_3391_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_s_3432_);
lean_dec(v_id_3391_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 3);
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_s_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
v___y_3416_ = v___x_3437_;
goto v___jp_3415_;
}
}
}
case 1:
{
lean_object* v_n_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
v_n_3440_ = lean_ctor_get(v_id_3391_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_id_3391_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v_id_3391_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_n_3440_);
lean_dec(v_id_3391_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
lean_ctor_set_tag(v___x_3442_, 2);
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_n_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
v___y_3416_ = v___x_3445_;
goto v___jp_3415_;
}
}
}
default: 
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_box(0);
v___y_3416_ = v___x_3448_;
goto v___jp_3415_;
}
}
v___jp_3395_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___y_3398_);
lean_ctor_set(v___x_3400_, 1, v___y_3399_);
v___x_3401_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3402_, 0, v_message_3393_);
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3401_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v___x_3404_ = lean_box(0);
v___x_3405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3403_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3400_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3408_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v___x_3407_, v_data_x3f_3394_);
lean_dec(v_data_x3f_3394_);
v___x_3409_ = l_List_appendTR___redArg(v___x_3406_, v___x_3408_);
v___x_3410_ = l_Lean_Json_mkObj(v___x_3409_);
lean_dec(v___x_3409_);
lean_inc_ref(v___y_3397_);
v___x_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___y_3397_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
lean_ctor_set(v___x_3412_, 1, v___x_3404_);
v___x_3413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___y_3396_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
v___y_3306_ = v___x_3413_;
goto v___jp_3305_;
}
v___jp_3415_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3414_);
lean_ctor_set(v___x_3417_, 1, v___y_3416_);
v___x_3418_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3419_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3392_)
{
case 0:
{
lean_object* v___x_3420_; 
v___x_3420_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3420_;
goto v___jp_3395_;
}
case 1:
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3421_;
goto v___jp_3395_;
}
case 2:
{
lean_object* v___x_3422_; 
v___x_3422_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3422_;
goto v___jp_3395_;
}
case 3:
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3423_;
goto v___jp_3395_;
}
case 4:
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3424_;
goto v___jp_3395_;
}
case 5:
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3425_;
goto v___jp_3395_;
}
case 6:
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3426_;
goto v___jp_3395_;
}
case 7:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3427_;
goto v___jp_3395_;
}
case 8:
{
lean_object* v___x_3428_; 
v___x_3428_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3428_;
goto v___jp_3395_;
}
case 9:
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3429_;
goto v___jp_3395_;
}
case 10:
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3430_;
goto v___jp_3395_;
}
default: 
{
lean_object* v___x_3431_; 
v___x_3431_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3396_ = v___x_3417_;
v___y_3397_ = v___x_3418_;
v___y_3398_ = v___x_3419_;
v___y_3399_ = v___x_3431_;
goto v___jp_3395_;
}
}
}
}
}
v___jp_3305_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3304_);
lean_ctor_set(v___x_3307_, 1, v___y_3306_);
v___x_3308_ = l_Lean_Json_mkObj(v___x_3307_);
lean_dec_ref_known(v___x_3307_, 2);
v___x_3309_ = l_Lean_IO_FS_Stream_writeJson(v_h_3301_, v___x_3308_);
return v___x_3309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage___boxed(lean_object* v_h_3449_, lean_object* v_m_3450_, lean_object* v_a_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3449_, v_m_3450_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg(lean_object* v_inst_3453_, lean_object* v_h_3454_, lean_object* v_r_3455_){
_start:
{
lean_object* v_id_3457_; lean_object* v_method_3458_; lean_object* v_param_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3479_; 
v_id_3457_ = lean_ctor_get(v_r_3455_, 0);
v_method_3458_ = lean_ctor_get(v_r_3455_, 1);
v_param_3459_ = lean_ctor_get(v_r_3455_, 2);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_r_3455_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3461_ = v_r_3455_;
v_isShared_3462_ = v_isSharedCheck_3479_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_param_3459_);
lean_inc(v_method_3458_);
lean_inc(v_id_3457_);
lean_dec(v_r_3455_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3479_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___y_3464_; lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3453_, v_param_3459_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v___x_3470_; 
lean_dec_ref_known(v___x_3469_, 1);
v___x_3470_ = lean_box(0);
v___y_3464_ = v___x_3470_;
goto v___jp_3463_;
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
v_a_3471_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3469_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3469_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
v___y_3464_ = v___x_3476_;
goto v___jp_3463_;
}
}
}
v___jp_3463_:
{
lean_object* v___x_3466_; 
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 2, v___y_3464_);
v___x_3466_ = v___x_3461_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_id_3457_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_method_3458_);
lean_ctor_set(v_reuseFailAlloc_3468_, 2, v___y_3464_);
v___x_3466_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3454_, v___x_3466_);
return v___x_3467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg___boxed(lean_object* v_inst_3480_, lean_object* v_h_3481_, lean_object* v_r_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3480_, v_h_3481_, v_r_3482_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest(lean_object* v_00_u03b1_3485_, lean_object* v_inst_3486_, lean_object* v_h_3487_, lean_object* v_r_3488_){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3486_, v_h_3487_, v_r_3488_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___boxed(lean_object* v_00_u03b1_3491_, lean_object* v_inst_3492_, lean_object* v_h_3493_, lean_object* v_r_3494_, lean_object* v_a_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_IO_FS_Stream_writeRequest(v_00_u03b1_3491_, v_inst_3492_, v_h_3493_, v_r_3494_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg(lean_object* v_inst_3497_, lean_object* v_h_3498_, lean_object* v_n_3499_){
_start:
{
lean_object* v_method_3501_; lean_object* v_param_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3522_; 
v_method_3501_ = lean_ctor_get(v_n_3499_, 0);
v_param_3502_ = lean_ctor_get(v_n_3499_, 1);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_n_3499_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3504_ = v_n_3499_;
v_isShared_3505_ = v_isSharedCheck_3522_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_param_3502_);
lean_inc(v_method_3501_);
lean_dec(v_n_3499_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3522_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___y_3507_; lean_object* v___x_3512_; 
v___x_3512_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3497_, v_param_3502_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v___x_3513_; 
lean_dec_ref_known(v___x_3512_, 1);
v___x_3513_ = lean_box(0);
v___y_3507_ = v___x_3513_;
goto v___jp_3506_;
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
v_a_3514_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3512_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3512_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
v___y_3507_ = v___x_3519_;
goto v___jp_3506_;
}
}
}
v___jp_3506_:
{
lean_object* v___x_3509_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set_tag(v___x_3504_, 1);
lean_ctor_set(v___x_3504_, 1, v___y_3507_);
v___x_3509_ = v___x_3504_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_method_3501_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v___y_3507_);
v___x_3509_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3498_, v___x_3509_);
return v___x_3510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg___boxed(lean_object* v_inst_3523_, lean_object* v_h_3524_, lean_object* v_n_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3523_, v_h_3524_, v_n_3525_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification(lean_object* v_00_u03b1_3528_, lean_object* v_inst_3529_, lean_object* v_h_3530_, lean_object* v_n_3531_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3529_, v_h_3530_, v_n_3531_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___boxed(lean_object* v_00_u03b1_3534_, lean_object* v_inst_3535_, lean_object* v_h_3536_, lean_object* v_n_3537_, lean_object* v_a_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Lean_IO_FS_Stream_writeNotification(v_00_u03b1_3534_, v_inst_3535_, v_h_3536_, v_n_3537_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg(lean_object* v_inst_3540_, lean_object* v_h_3541_, lean_object* v_r_3542_){
_start:
{
lean_object* v_id_3544_; lean_object* v_result_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3554_; 
v_id_3544_ = lean_ctor_get(v_r_3542_, 0);
v_result_3545_ = lean_ctor_get(v_r_3542_, 1);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_r_3542_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3547_ = v_r_3542_;
v_isShared_3548_ = v_isSharedCheck_3554_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_result_3545_);
lean_inc(v_id_3544_);
lean_dec(v_r_3542_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3554_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3549_ = lean_apply_1(v_inst_3540_, v_result_3545_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set_tag(v___x_3547_, 2);
lean_ctor_set(v___x_3547_, 1, v___x_3549_);
v___x_3551_ = v___x_3547_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_id_3544_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3541_, v___x_3551_);
return v___x_3552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg___boxed(lean_object* v_inst_3555_, lean_object* v_h_3556_, lean_object* v_r_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3555_, v_h_3556_, v_r_3557_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse(lean_object* v_00_u03b1_3560_, lean_object* v_inst_3561_, lean_object* v_h_3562_, lean_object* v_r_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3561_, v_h_3562_, v_r_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___boxed(lean_object* v_00_u03b1_3566_, lean_object* v_inst_3567_, lean_object* v_h_3568_, lean_object* v_r_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_IO_FS_Stream_writeResponse(v_00_u03b1_3566_, v_inst_3567_, v_h_3568_, v_r_3569_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError(lean_object* v_h_3572_, lean_object* v_e_3573_){
_start:
{
lean_object* v_id_3575_; uint8_t v_code_3576_; lean_object* v_message_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3586_; 
v_id_3575_ = lean_ctor_get(v_e_3573_, 0);
v_code_3576_ = lean_ctor_get_uint8(v_e_3573_, sizeof(void*)*3);
v_message_3577_ = lean_ctor_get(v_e_3573_, 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_e_3573_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; 
v_unused_3587_ = lean_ctor_get(v_e_3573_, 2);
lean_dec(v_unused_3587_);
v___x_3579_ = v_e_3573_;
v_isShared_3580_ = v_isSharedCheck_3586_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_message_3577_);
lean_inc(v_id_3575_);
lean_dec(v_e_3573_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3586_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3581_ = lean_box(0);
if (v_isShared_3580_ == 0)
{
lean_ctor_set_tag(v___x_3579_, 3);
lean_ctor_set(v___x_3579_, 2, v___x_3581_);
v___x_3583_ = v___x_3579_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_id_3575_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_message_3577_);
lean_ctor_set(v_reuseFailAlloc_3585_, 2, v___x_3581_);
lean_ctor_set_uint8(v_reuseFailAlloc_3585_, sizeof(void*)*3, v_code_3576_);
v___x_3583_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3572_, v___x_3583_);
return v___x_3584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError___boxed(lean_object* v_h_3588_, lean_object* v_e_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lean_IO_FS_Stream_writeResponseError(v_h_3588_, v_e_3589_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* v_inst_3592_, lean_object* v_h_3593_, lean_object* v_e_3594_){
_start:
{
lean_object* v_id_3596_; uint8_t v_code_3597_; lean_object* v_message_3598_; lean_object* v_data_x3f_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3619_; 
v_id_3596_ = lean_ctor_get(v_e_3594_, 0);
v_code_3597_ = lean_ctor_get_uint8(v_e_3594_, sizeof(void*)*3);
v_message_3598_ = lean_ctor_get(v_e_3594_, 1);
v_data_x3f_3599_ = lean_ctor_get(v_e_3594_, 2);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_e_3594_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3601_ = v_e_3594_;
v_isShared_3602_ = v_isSharedCheck_3619_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_data_x3f_3599_);
lean_inc(v_message_3598_);
lean_inc(v_id_3596_);
lean_dec(v_e_3594_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3619_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___y_3604_; 
if (lean_obj_tag(v_data_x3f_3599_) == 0)
{
lean_object* v___x_3609_; 
lean_dec_ref(v_inst_3592_);
v___x_3609_ = lean_box(0);
v___y_3604_ = v___x_3609_;
goto v___jp_3603_;
}
else
{
lean_object* v_val_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3618_; 
v_val_3610_ = lean_ctor_get(v_data_x3f_3599_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_data_x3f_3599_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3612_ = v_data_x3f_3599_;
v_isShared_3613_ = v_isSharedCheck_3618_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_val_3610_);
lean_dec(v_data_x3f_3599_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3618_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3614_; lean_object* v___x_3616_; 
v___x_3614_ = lean_apply_1(v_inst_3592_, v_val_3610_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 0, v___x_3614_);
v___x_3616_ = v___x_3612_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
v___y_3604_ = v___x_3616_;
goto v___jp_3603_;
}
}
}
v___jp_3603_:
{
lean_object* v___x_3606_; 
if (v_isShared_3602_ == 0)
{
lean_ctor_set_tag(v___x_3601_, 3);
lean_ctor_set(v___x_3601_, 2, v___y_3604_);
v___x_3606_ = v___x_3601_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_id_3596_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_message_3598_);
lean_ctor_set(v_reuseFailAlloc_3608_, 2, v___y_3604_);
lean_ctor_set_uint8(v_reuseFailAlloc_3608_, sizeof(void*)*3, v_code_3597_);
v___x_3606_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3593_, v___x_3606_);
return v___x_3607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object* v_inst_3620_, lean_object* v_h_3621_, lean_object* v_e_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3620_, v_h_3621_, v_e_3622_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData(lean_object* v_00_u03b1_3625_, lean_object* v_inst_3626_, lean_object* v_h_3627_, lean_object* v_e_3628_){
_start:
{
lean_object* v___x_3630_; 
v___x_3630_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3626_, v_h_3627_, v_e_3628_);
return v___x_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object* v_00_u03b1_3631_, lean_object* v_inst_3632_, lean_object* v_h_3633_, lean_object* v_e_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData(v_00_u03b1_3631_, v_inst_3632_, v_h_3633_, v_e_3634_);
return v_res_3636_;
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
