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
if (lean_obj_tag(v_x_86_) == 0)
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
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
lean_dec_ref_known(v_x_85_, 1);
lean_dec(v_x_86_);
v___x_90_ = 0;
return v___x_90_;
}
}
case 1:
{
switch(lean_obj_tag(v_x_86_))
{
case 0:
{
uint8_t v___x_91_; 
lean_dec_ref_known(v_x_86_, 1);
lean_dec_ref_known(v_x_85_, 1);
v___x_91_ = 2;
return v___x_91_;
}
case 1:
{
lean_object* v_n_92_; lean_object* v_n_93_; uint8_t v___x_94_; 
v_n_92_ = lean_ctor_get(v_x_85_, 0);
lean_inc_ref_n(v_n_92_, 2);
lean_dec_ref_known(v_x_85_, 1);
v_n_93_ = lean_ctor_get(v_x_86_, 0);
lean_inc_ref_n(v_n_93_, 2);
lean_dec_ref_known(v_x_86_, 1);
v___x_94_ = l_Lean_JsonNumber_lt(v_n_92_, v_n_93_);
if (v___x_94_ == 0)
{
uint8_t v___x_95_; 
v___x_95_ = l_Lean_JsonNumber_lt(v_n_93_, v_n_92_);
if (v___x_95_ == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 1;
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 2;
return v___x_97_;
}
}
else
{
uint8_t v___x_98_; 
lean_dec_ref(v_n_93_);
lean_dec_ref(v_n_92_);
v___x_98_ = 0;
return v___x_98_;
}
}
default: 
{
uint8_t v___x_99_; 
lean_dec_ref_known(v_x_85_, 1);
lean_dec(v_x_86_);
v___x_99_ = 0;
return v___x_99_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_86_) == 2)
{
uint8_t v___x_100_; 
v___x_100_ = 1;
return v___x_100_;
}
else
{
uint8_t v___x_101_; 
lean_dec(v_x_86_);
v___x_101_ = 2;
return v___x_101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOrdRequestID_ord___boxed(lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Lean_JsonRpc_instOrdRequestID_ord(v_x_102_, v_x_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instOfNatRequestID(lean_object* v_n_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = l_Lean_JsonNumber_fromNat(v_n_108_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToStringRequestID___lam__0(lean_object* v_x_113_){
_start:
{
switch(lean_obj_tag(v_x_113_))
{
case 0:
{
lean_object* v_s_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_s_114_ = lean_ctor_get(v_x_113_, 0);
lean_inc_ref(v_s_114_);
lean_dec_ref_known(v_x_113_, 1);
v___x_115_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_116_ = lean_string_append(v___x_115_, v_s_114_);
lean_dec_ref(v_s_114_);
v___x_117_ = lean_string_append(v___x_116_, v___x_115_);
return v___x_117_;
}
case 1:
{
lean_object* v_n_118_; lean_object* v___x_119_; 
v_n_118_ = lean_ctor_get(v_x_113_, 0);
lean_inc_ref(v_n_118_);
lean_dec_ref_known(v_x_113_, 1);
v___x_119_ = l_Lean_JsonNumber_toString(v_n_118_);
return v___x_119_;
}
default: 
{
lean_object* v___x_120_; 
v___x_120_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx(uint8_t v_x_123_){
_start:
{
switch(v_x_123_)
{
case 0:
{
lean_object* v___x_124_; 
v___x_124_ = lean_unsigned_to_nat(0u);
return v___x_124_;
}
case 1:
{
lean_object* v___x_125_; 
v___x_125_ = lean_unsigned_to_nat(1u);
return v___x_125_;
}
case 2:
{
lean_object* v___x_126_; 
v___x_126_ = lean_unsigned_to_nat(2u);
return v___x_126_;
}
case 3:
{
lean_object* v___x_127_; 
v___x_127_ = lean_unsigned_to_nat(3u);
return v___x_127_;
}
case 4:
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(4u);
return v___x_128_;
}
case 5:
{
lean_object* v___x_129_; 
v___x_129_ = lean_unsigned_to_nat(5u);
return v___x_129_;
}
case 6:
{
lean_object* v___x_130_; 
v___x_130_ = lean_unsigned_to_nat(6u);
return v___x_130_;
}
case 7:
{
lean_object* v___x_131_; 
v___x_131_ = lean_unsigned_to_nat(7u);
return v___x_131_;
}
case 8:
{
lean_object* v___x_132_; 
v___x_132_ = lean_unsigned_to_nat(8u);
return v___x_132_;
}
case 9:
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(9u);
return v___x_133_;
}
case 10:
{
lean_object* v___x_134_; 
v___x_134_ = lean_unsigned_to_nat(10u);
return v___x_134_;
}
default: 
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(11u);
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___boxed(lean_object* v_x_136_){
_start:
{
uint8_t v_x_boxed_137_; lean_object* v_res_138_; 
v_x_boxed_137_ = lean_unbox(v_x_136_);
v_res_138_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_boxed_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(lean_object* v_k_139_){
_start:
{
lean_inc(v_k_139_);
return v_k_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg___boxed(lean_object* v_k_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(v_k_140_);
lean_dec(v_k_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim(lean_object* v_motive_142_, lean_object* v_ctorIdx_143_, uint8_t v_t_144_, lean_object* v_h_145_, lean_object* v_k_146_){
_start:
{
lean_inc(v_k_146_);
return v_k_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___boxed(lean_object* v_motive_147_, lean_object* v_ctorIdx_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_k_151_){
_start:
{
uint8_t v_t_boxed_152_; lean_object* v_res_153_; 
v_t_boxed_152_ = lean_unbox(v_t_149_);
v_res_153_ = l_Lean_JsonRpc_ErrorCode_ctorElim(v_motive_147_, v_ctorIdx_148_, v_t_boxed_152_, v_h_150_, v_k_151_);
lean_dec(v_k_151_);
lean_dec(v_ctorIdx_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(lean_object* v_parseError_154_){
_start:
{
lean_inc(v_parseError_154_);
return v_parseError_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg___boxed(lean_object* v_parseError_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(v_parseError_155_);
lean_dec(v_parseError_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_object* v_motive_157_, uint8_t v_t_158_, lean_object* v_h_159_, lean_object* v_parseError_160_){
_start:
{
lean_inc(v_parseError_160_);
return v_parseError_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___boxed(lean_object* v_motive_161_, lean_object* v_t_162_, lean_object* v_h_163_, lean_object* v_parseError_164_){
_start:
{
uint8_t v_t_boxed_165_; lean_object* v_res_166_; 
v_t_boxed_165_ = lean_unbox(v_t_162_);
v_res_166_ = l_Lean_JsonRpc_ErrorCode_parseError_elim(v_motive_161_, v_t_boxed_165_, v_h_163_, v_parseError_164_);
lean_dec(v_parseError_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(lean_object* v_invalidRequest_167_){
_start:
{
lean_inc(v_invalidRequest_167_);
return v_invalidRequest_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg___boxed(lean_object* v_invalidRequest_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(v_invalidRequest_168_);
lean_dec(v_invalidRequest_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_object* v_motive_170_, uint8_t v_t_171_, lean_object* v_h_172_, lean_object* v_invalidRequest_173_){
_start:
{
lean_inc(v_invalidRequest_173_);
return v_invalidRequest_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___boxed(lean_object* v_motive_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_invalidRequest_177_){
_start:
{
uint8_t v_t_boxed_178_; lean_object* v_res_179_; 
v_t_boxed_178_ = lean_unbox(v_t_175_);
v_res_179_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(v_motive_174_, v_t_boxed_178_, v_h_176_, v_invalidRequest_177_);
lean_dec(v_invalidRequest_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(lean_object* v_methodNotFound_180_){
_start:
{
lean_inc(v_methodNotFound_180_);
return v_methodNotFound_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg___boxed(lean_object* v_methodNotFound_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(v_methodNotFound_181_);
lean_dec(v_methodNotFound_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(lean_object* v_motive_183_, uint8_t v_t_184_, lean_object* v_h_185_, lean_object* v_methodNotFound_186_){
_start:
{
lean_inc(v_methodNotFound_186_);
return v_methodNotFound_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___boxed(lean_object* v_motive_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_methodNotFound_190_){
_start:
{
uint8_t v_t_boxed_191_; lean_object* v_res_192_; 
v_t_boxed_191_ = lean_unbox(v_t_188_);
v_res_192_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(v_motive_187_, v_t_boxed_191_, v_h_189_, v_methodNotFound_190_);
lean_dec(v_methodNotFound_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(lean_object* v_invalidParams_193_){
_start:
{
lean_inc(v_invalidParams_193_);
return v_invalidParams_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg___boxed(lean_object* v_invalidParams_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(v_invalidParams_194_);
lean_dec(v_invalidParams_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_object* v_motive_196_, uint8_t v_t_197_, lean_object* v_h_198_, lean_object* v_invalidParams_199_){
_start:
{
lean_inc(v_invalidParams_199_);
return v_invalidParams_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___boxed(lean_object* v_motive_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_invalidParams_203_){
_start:
{
uint8_t v_t_boxed_204_; lean_object* v_res_205_; 
v_t_boxed_204_ = lean_unbox(v_t_201_);
v_res_205_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim(v_motive_200_, v_t_boxed_204_, v_h_202_, v_invalidParams_203_);
lean_dec(v_invalidParams_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(lean_object* v_internalError_206_){
_start:
{
lean_inc(v_internalError_206_);
return v_internalError_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg___boxed(lean_object* v_internalError_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(v_internalError_207_);
lean_dec(v_internalError_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_object* v_motive_209_, uint8_t v_t_210_, lean_object* v_h_211_, lean_object* v_internalError_212_){
_start:
{
lean_inc(v_internalError_212_);
return v_internalError_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___boxed(lean_object* v_motive_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_internalError_216_){
_start:
{
uint8_t v_t_boxed_217_; lean_object* v_res_218_; 
v_t_boxed_217_ = lean_unbox(v_t_214_);
v_res_218_ = l_Lean_JsonRpc_ErrorCode_internalError_elim(v_motive_213_, v_t_boxed_217_, v_h_215_, v_internalError_216_);
lean_dec(v_internalError_216_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(lean_object* v_serverNotInitialized_219_){
_start:
{
lean_inc(v_serverNotInitialized_219_);
return v_serverNotInitialized_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg___boxed(lean_object* v_serverNotInitialized_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(v_serverNotInitialized_220_);
lean_dec(v_serverNotInitialized_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_object* v_motive_222_, uint8_t v_t_223_, lean_object* v_h_224_, lean_object* v_serverNotInitialized_225_){
_start:
{
lean_inc(v_serverNotInitialized_225_);
return v_serverNotInitialized_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___boxed(lean_object* v_motive_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_serverNotInitialized_229_){
_start:
{
uint8_t v_t_boxed_230_; lean_object* v_res_231_; 
v_t_boxed_230_ = lean_unbox(v_t_227_);
v_res_231_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(v_motive_226_, v_t_boxed_230_, v_h_228_, v_serverNotInitialized_229_);
lean_dec(v_serverNotInitialized_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(lean_object* v_unknownErrorCode_232_){
_start:
{
lean_inc(v_unknownErrorCode_232_);
return v_unknownErrorCode_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg___boxed(lean_object* v_unknownErrorCode_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(v_unknownErrorCode_233_);
lean_dec(v_unknownErrorCode_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_object* v_motive_235_, uint8_t v_t_236_, lean_object* v_h_237_, lean_object* v_unknownErrorCode_238_){
_start:
{
lean_inc(v_unknownErrorCode_238_);
return v_unknownErrorCode_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___boxed(lean_object* v_motive_239_, lean_object* v_t_240_, lean_object* v_h_241_, lean_object* v_unknownErrorCode_242_){
_start:
{
uint8_t v_t_boxed_243_; lean_object* v_res_244_; 
v_t_boxed_243_ = lean_unbox(v_t_240_);
v_res_244_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(v_motive_239_, v_t_boxed_243_, v_h_241_, v_unknownErrorCode_242_);
lean_dec(v_unknownErrorCode_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(lean_object* v_contentModified_245_){
_start:
{
lean_inc(v_contentModified_245_);
return v_contentModified_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg___boxed(lean_object* v_contentModified_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(v_contentModified_246_);
lean_dec(v_contentModified_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_object* v_motive_248_, uint8_t v_t_249_, lean_object* v_h_250_, lean_object* v_contentModified_251_){
_start:
{
lean_inc(v_contentModified_251_);
return v_contentModified_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___boxed(lean_object* v_motive_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_contentModified_255_){
_start:
{
uint8_t v_t_boxed_256_; lean_object* v_res_257_; 
v_t_boxed_256_ = lean_unbox(v_t_253_);
v_res_257_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim(v_motive_252_, v_t_boxed_256_, v_h_254_, v_contentModified_255_);
lean_dec(v_contentModified_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(lean_object* v_requestCancelled_258_){
_start:
{
lean_inc(v_requestCancelled_258_);
return v_requestCancelled_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg___boxed(lean_object* v_requestCancelled_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(v_requestCancelled_259_);
lean_dec(v_requestCancelled_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_object* v_motive_261_, uint8_t v_t_262_, lean_object* v_h_263_, lean_object* v_requestCancelled_264_){
_start:
{
lean_inc(v_requestCancelled_264_);
return v_requestCancelled_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___boxed(lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_requestCancelled_268_){
_start:
{
uint8_t v_t_boxed_269_; lean_object* v_res_270_; 
v_t_boxed_269_ = lean_unbox(v_t_266_);
v_res_270_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(v_motive_265_, v_t_boxed_269_, v_h_267_, v_requestCancelled_268_);
lean_dec(v_requestCancelled_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(lean_object* v_rpcNeedsReconnect_271_){
_start:
{
lean_inc(v_rpcNeedsReconnect_271_);
return v_rpcNeedsReconnect_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg___boxed(lean_object* v_rpcNeedsReconnect_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(v_rpcNeedsReconnect_272_);
lean_dec(v_rpcNeedsReconnect_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(lean_object* v_motive_274_, uint8_t v_t_275_, lean_object* v_h_276_, lean_object* v_rpcNeedsReconnect_277_){
_start:
{
lean_inc(v_rpcNeedsReconnect_277_);
return v_rpcNeedsReconnect_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___boxed(lean_object* v_motive_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_rpcNeedsReconnect_281_){
_start:
{
uint8_t v_t_boxed_282_; lean_object* v_res_283_; 
v_t_boxed_282_ = lean_unbox(v_t_279_);
v_res_283_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(v_motive_278_, v_t_boxed_282_, v_h_280_, v_rpcNeedsReconnect_281_);
lean_dec(v_rpcNeedsReconnect_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(lean_object* v_workerExited_284_){
_start:
{
lean_inc(v_workerExited_284_);
return v_workerExited_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg___boxed(lean_object* v_workerExited_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(v_workerExited_285_);
lean_dec(v_workerExited_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim(lean_object* v_motive_287_, uint8_t v_t_288_, lean_object* v_h_289_, lean_object* v_workerExited_290_){
_start:
{
lean_inc(v_workerExited_290_);
return v_workerExited_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___boxed(lean_object* v_motive_291_, lean_object* v_t_292_, lean_object* v_h_293_, lean_object* v_workerExited_294_){
_start:
{
uint8_t v_t_boxed_295_; lean_object* v_res_296_; 
v_t_boxed_295_ = lean_unbox(v_t_292_);
v_res_296_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim(v_motive_291_, v_t_boxed_295_, v_h_293_, v_workerExited_294_);
lean_dec(v_workerExited_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(lean_object* v_workerCrashed_297_){
_start:
{
lean_inc(v_workerCrashed_297_);
return v_workerCrashed_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg___boxed(lean_object* v_workerCrashed_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(v_workerCrashed_298_);
lean_dec(v_workerCrashed_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_object* v_motive_300_, uint8_t v_t_301_, lean_object* v_h_302_, lean_object* v_workerCrashed_303_){
_start:
{
lean_inc(v_workerCrashed_303_);
return v_workerCrashed_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___boxed(lean_object* v_motive_304_, lean_object* v_t_305_, lean_object* v_h_306_, lean_object* v_workerCrashed_307_){
_start:
{
uint8_t v_t_boxed_308_; lean_object* v_res_309_; 
v_t_boxed_308_ = lean_unbox(v_t_305_);
v_res_309_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(v_motive_304_, v_t_boxed_308_, v_h_306_, v_workerCrashed_307_);
lean_dec(v_workerCrashed_307_);
return v_res_309_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode_default(void){
_start:
{
uint8_t v___x_310_; 
v___x_310_ = 0;
return v___x_310_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode(void){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = 0;
return v___x_311_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqErrorCode_beq(uint8_t v_x_312_, uint8_t v_y_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_312_);
v___x_315_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_y_313_);
v___x_316_ = lean_nat_dec_eq(v___x_314_, v___x_315_);
lean_dec(v___x_315_);
lean_dec(v___x_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode_beq___boxed(lean_object* v_x_317_, lean_object* v_y_318_){
_start:
{
uint8_t v_x_21__boxed_319_; uint8_t v_y_22__boxed_320_; uint8_t v_res_321_; lean_object* v_r_322_; 
v_x_21__boxed_319_ = lean_unbox(v_x_317_);
v_y_22__boxed_320_ = lean_unbox(v_y_318_);
v_res_321_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_x_21__boxed_319_, v_y_22__boxed_320_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(32700u);
v___x_329_ = lean_nat_to_int(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2);
v___x_331_ = lean_int_neg(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(32600u);
v___x_333_ = lean_nat_to_int(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4);
v___x_335_ = lean_int_neg(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_unsigned_to_nat(32601u);
v___x_337_ = lean_nat_to_int(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6);
v___x_339_ = lean_int_neg(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(32602u);
v___x_341_ = lean_nat_to_int(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8);
v___x_343_ = lean_int_neg(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(32603u);
v___x_345_ = lean_nat_to_int(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10);
v___x_347_ = lean_int_neg(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(32002u);
v___x_349_ = lean_nat_to_int(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12);
v___x_351_ = lean_int_neg(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(32001u);
v___x_353_ = lean_nat_to_int(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14);
v___x_355_ = lean_int_neg(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_unsigned_to_nat(32801u);
v___x_357_ = lean_nat_to_int(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16);
v___x_359_ = lean_int_neg(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(32800u);
v___x_361_ = lean_nat_to_int(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18);
v___x_363_ = lean_int_neg(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_unsigned_to_nat(32900u);
v___x_365_ = lean_nat_to_int(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20);
v___x_367_ = lean_int_neg(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(32901u);
v___x_369_ = lean_nat_to_int(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22);
v___x_371_ = lean_int_neg(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_unsigned_to_nat(32902u);
v___x_373_ = lean_nat_to_int(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24);
v___x_375_ = lean_int_neg(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(lean_object* v_x_412_){
_start:
{
if (lean_obj_tag(v_x_412_) == 2)
{
lean_object* v_n_415_; lean_object* v_mantissa_416_; lean_object* v_exponent_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_n_415_ = lean_ctor_get(v_x_412_, 0);
v_mantissa_416_ = lean_ctor_get(v_n_415_, 0);
v_exponent_417_ = lean_ctor_get(v_n_415_, 1);
v___x_418_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_419_ = lean_int_dec_eq(v_mantissa_416_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_421_ = lean_int_dec_eq(v_mantissa_416_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_423_ = lean_int_dec_eq(v_mantissa_416_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_425_ = lean_int_dec_eq(v_mantissa_416_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_427_ = lean_int_dec_eq(v_mantissa_416_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_429_ = lean_int_dec_eq(v_mantissa_416_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_431_ = lean_int_dec_eq(v_mantissa_416_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_433_ = lean_int_dec_eq(v_mantissa_416_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_435_ = lean_int_dec_eq(v_mantissa_416_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_437_ = lean_int_dec_eq(v_mantissa_416_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_439_ = lean_int_dec_eq(v_mantissa_416_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_441_ = lean_int_dec_eq(v_mantissa_416_, v___x_440_);
if (v___x_441_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_nat_dec_eq(v_exponent_417_, v___x_442_);
if (v___x_443_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_444_; 
v___x_444_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_444_;
}
}
}
else
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_nat_dec_eq(v_exponent_417_, v___x_445_);
if (v___x_446_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_447_;
}
}
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_nat_dec_eq(v_exponent_417_, v___x_448_);
if (v___x_449_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_450_; 
v___x_450_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_450_;
}
}
}
else
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_nat_dec_eq(v_exponent_417_, v___x_451_);
if (v___x_452_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_453_; 
v___x_453_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_453_;
}
}
}
else
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_nat_dec_eq(v_exponent_417_, v___x_454_);
if (v___x_455_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_456_;
}
}
}
else
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_nat_dec_eq(v_exponent_417_, v___x_457_);
if (v___x_458_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_459_;
}
}
}
else
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_nat_dec_eq(v_exponent_417_, v___x_460_);
if (v___x_461_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_462_;
}
}
}
else
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_nat_dec_eq(v_exponent_417_, v___x_463_);
if (v___x_464_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_465_; 
v___x_465_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_465_;
}
}
}
else
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_nat_dec_eq(v_exponent_417_, v___x_466_);
if (v___x_467_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_468_; 
v___x_468_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_468_;
}
}
}
else
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_nat_dec_eq(v_exponent_417_, v___x_469_);
if (v___x_470_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_471_;
}
}
}
else
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_nat_dec_eq(v_exponent_417_, v___x_472_);
if (v___x_473_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_474_;
}
}
}
else
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_nat_dec_eq(v_exponent_417_, v___x_475_);
if (v___x_476_ == 0)
{
goto v___jp_413_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_477_;
}
}
}
else
{
goto v___jp_413_;
}
v___jp_413_:
{
lean_object* v___x_414_; 
v___x_414_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed(lean_object* v_x_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(v_x_478_);
lean_dec(v_x_478_);
return v_res_479_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_483_ = l_Lean_JsonNumber_fromInt(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0);
v___x_485_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_487_ = l_Lean_JsonNumber_fromInt(v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2);
v___x_489_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_491_ = l_Lean_JsonNumber_fromInt(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4);
v___x_493_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_495_ = l_Lean_JsonNumber_fromInt(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6);
v___x_497_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_499_ = l_Lean_JsonNumber_fromInt(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8);
v___x_501_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_503_ = l_Lean_JsonNumber_fromInt(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10);
v___x_505_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_507_ = l_Lean_JsonNumber_fromInt(v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12);
v___x_509_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_511_ = l_Lean_JsonNumber_fromInt(v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14);
v___x_513_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_515_ = l_Lean_JsonNumber_fromInt(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16);
v___x_517_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_519_ = l_Lean_JsonNumber_fromInt(v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18);
v___x_521_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_523_ = l_Lean_JsonNumber_fromInt(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20);
v___x_525_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_527_ = l_Lean_JsonNumber_fromInt(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22);
v___x_529_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t v_x_530_){
_start:
{
switch(v_x_530_)
{
case 0:
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
return v___x_531_;
}
case 1:
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
return v___x_532_;
}
case 2:
{
lean_object* v___x_533_; 
v___x_533_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
return v___x_533_;
}
case 3:
{
lean_object* v___x_534_; 
v___x_534_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
return v___x_534_;
}
case 4:
{
lean_object* v___x_535_; 
v___x_535_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
return v___x_535_;
}
case 5:
{
lean_object* v___x_536_; 
v___x_536_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
return v___x_536_;
}
case 6:
{
lean_object* v___x_537_; 
v___x_537_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
return v___x_537_;
}
case 7:
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
return v___x_538_;
}
case 8:
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
return v___x_539_;
}
case 9:
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
return v___x_540_;
}
case 10:
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
return v___x_541_;
}
default: 
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object* v_x_543_){
_start:
{
uint8_t v_x_474__boxed_544_; lean_object* v_res_545_; 
v_x_474__boxed_544_ = lean_unbox(v_x_543_);
v_res_545_ = l_Lean_JsonRpc_instToJsonErrorCode___lam__0(v_x_474__boxed_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx(lean_object* v_x_548_){
_start:
{
switch(lean_obj_tag(v_x_548_))
{
case 0:
{
lean_object* v___x_549_; 
v___x_549_ = lean_unsigned_to_nat(0u);
return v___x_549_;
}
case 1:
{
lean_object* v___x_550_; 
v___x_550_ = lean_unsigned_to_nat(1u);
return v___x_550_;
}
case 2:
{
lean_object* v___x_551_; 
v___x_551_ = lean_unsigned_to_nat(2u);
return v___x_551_;
}
default: 
{
lean_object* v___x_552_; 
v___x_552_ = lean_unsigned_to_nat(3u);
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___boxed(lean_object* v_x_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_JsonRpc_Message_ctorIdx(v_x_553_);
lean_dec_ref(v_x_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___redArg(lean_object* v_t_555_, lean_object* v_k_556_){
_start:
{
switch(lean_obj_tag(v_t_555_))
{
case 0:
{
lean_object* v_id_557_; lean_object* v_method_558_; lean_object* v_params_x3f_559_; lean_object* v___x_560_; 
v_id_557_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_id_557_);
v_method_558_ = lean_ctor_get(v_t_555_, 1);
lean_inc_ref(v_method_558_);
v_params_x3f_559_ = lean_ctor_get(v_t_555_, 2);
lean_inc(v_params_x3f_559_);
lean_dec_ref_known(v_t_555_, 3);
v___x_560_ = lean_apply_3(v_k_556_, v_id_557_, v_method_558_, v_params_x3f_559_);
return v___x_560_;
}
case 1:
{
lean_object* v_method_561_; lean_object* v_params_x3f_562_; lean_object* v___x_563_; 
v_method_561_ = lean_ctor_get(v_t_555_, 0);
lean_inc_ref(v_method_561_);
v_params_x3f_562_ = lean_ctor_get(v_t_555_, 1);
lean_inc(v_params_x3f_562_);
lean_dec_ref_known(v_t_555_, 2);
v___x_563_ = lean_apply_2(v_k_556_, v_method_561_, v_params_x3f_562_);
return v___x_563_;
}
case 2:
{
lean_object* v_id_564_; lean_object* v_result_565_; lean_object* v___x_566_; 
v_id_564_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_id_564_);
v_result_565_ = lean_ctor_get(v_t_555_, 1);
lean_inc(v_result_565_);
lean_dec_ref_known(v_t_555_, 2);
v___x_566_ = lean_apply_2(v_k_556_, v_id_564_, v_result_565_);
return v___x_566_;
}
default: 
{
lean_object* v_id_567_; uint8_t v_code_568_; lean_object* v_message_569_; lean_object* v_data_x3f_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_id_567_ = lean_ctor_get(v_t_555_, 0);
lean_inc(v_id_567_);
v_code_568_ = lean_ctor_get_uint8(v_t_555_, sizeof(void*)*3);
v_message_569_ = lean_ctor_get(v_t_555_, 1);
lean_inc_ref(v_message_569_);
v_data_x3f_570_ = lean_ctor_get(v_t_555_, 2);
lean_inc(v_data_x3f_570_);
lean_dec_ref_known(v_t_555_, 3);
v___x_571_ = lean_box(v_code_568_);
v___x_572_ = lean_apply_4(v_k_556_, v_id_567_, v___x_571_, v_message_569_, v_data_x3f_570_);
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim(lean_object* v_motive_573_, lean_object* v_ctorIdx_574_, lean_object* v_t_575_, lean_object* v_h_576_, lean_object* v_k_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_575_, v_k_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___boxed(lean_object* v_motive_579_, lean_object* v_ctorIdx_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_k_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_JsonRpc_Message_ctorElim(v_motive_579_, v_ctorIdx_580_, v_t_581_, v_h_582_, v_k_583_);
lean_dec(v_ctorIdx_580_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim___redArg(lean_object* v_t_585_, lean_object* v_request_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_585_, v_request_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim(lean_object* v_motive_588_, lean_object* v_t_589_, lean_object* v_h_590_, lean_object* v_request_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_589_, v_request_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim___redArg(lean_object* v_t_593_, lean_object* v_notification_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_593_, v_notification_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim(lean_object* v_motive_596_, lean_object* v_t_597_, lean_object* v_h_598_, lean_object* v_notification_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_597_, v_notification_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim___redArg(lean_object* v_t_601_, lean_object* v_response_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_601_, v_response_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim(lean_object* v_motive_604_, lean_object* v_t_605_, lean_object* v_h_606_, lean_object* v_response_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_605_, v_response_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim___redArg(lean_object* v_t_609_, lean_object* v_responseError_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_609_, v_responseError_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim(lean_object* v_motive_612_, lean_object* v_t_613_, lean_object* v_h_614_, lean_object* v_responseError_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_613_, v_responseError_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default___redArg(lean_object* v_inst_623_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default));
v___x_625_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
lean_ctor_set(v___x_626_, 2, v_inst_623_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default(lean_object* v_00_u03b1_627_, lean_object* v_inst_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___redArg(lean_object* v_inst_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object* v_a_632_, lean_object* v_inst_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_633_);
return v___x_634_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq___redArg(lean_object* v_inst_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
lean_object* v_id_638_; lean_object* v_method_639_; lean_object* v_param_640_; lean_object* v_id_641_; lean_object* v_method_642_; lean_object* v_param_643_; uint8_t v___x_644_; 
v_id_638_ = lean_ctor_get(v_x_636_, 0);
lean_inc(v_id_638_);
v_method_639_ = lean_ctor_get(v_x_636_, 1);
lean_inc_ref(v_method_639_);
v_param_640_ = lean_ctor_get(v_x_636_, 2);
lean_inc(v_param_640_);
lean_dec_ref(v_x_636_);
v_id_641_ = lean_ctor_get(v_x_637_, 0);
lean_inc(v_id_641_);
v_method_642_ = lean_ctor_get(v_x_637_, 1);
lean_inc_ref(v_method_642_);
v_param_643_ = lean_ctor_get(v_x_637_, 2);
lean_inc(v_param_643_);
lean_dec_ref(v_x_637_);
v___x_644_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_638_, v_id_641_);
lean_dec(v_id_641_);
lean_dec(v_id_638_);
if (v___x_644_ == 0)
{
lean_dec(v_param_643_);
lean_dec_ref(v_method_642_);
lean_dec(v_param_640_);
lean_dec_ref(v_method_639_);
lean_dec_ref(v_inst_635_);
return v___x_644_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = lean_string_dec_eq(v_method_639_, v_method_642_);
lean_dec_ref(v_method_642_);
lean_dec_ref(v_method_639_);
if (v___x_645_ == 0)
{
lean_dec(v_param_643_);
lean_dec(v_param_640_);
lean_dec_ref(v_inst_635_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_apply_2(v_inst_635_, v_param_640_, v_param_643_);
v___x_647_ = lean_unbox(v___x_646_);
return v___x_647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___redArg___boxed(lean_object* v_inst_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_648_, v_x_649_, v_x_650_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq(lean_object* v_00_u03b1_653_, lean_object* v_inst_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_654_, v_x_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___boxed(lean_object* v_00_u03b1_658_, lean_object* v_inst_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
uint8_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_Lean_JsonRpc_instBEqRequest_beq(v_00_u03b1_658_, v_inst_659_, v_x_660_, v_x_661_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object* v_inst_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_665_, 0, lean_box(0));
lean_closure_set(v___x_665_, 1, v_inst_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object* v_00_u03b1_666_, lean_object* v_inst_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_668_, 0, lean_box(0));
lean_closure_set(v___x_668_, 1, v_inst_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object* v_inst_669_, lean_object* v_r_670_){
_start:
{
lean_object* v_id_671_; lean_object* v_method_672_; lean_object* v_param_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_693_; 
v_id_671_ = lean_ctor_get(v_r_670_, 0);
v_method_672_ = lean_ctor_get(v_r_670_, 1);
v_param_673_ = lean_ctor_get(v_r_670_, 2);
v_isSharedCheck_693_ = !lean_is_exclusive(v_r_670_);
if (v_isSharedCheck_693_ == 0)
{
v___x_675_ = v_r_670_;
v_isShared_676_ = v_isSharedCheck_693_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_param_673_);
lean_inc(v_method_672_);
lean_inc(v_id_671_);
lean_dec(v_r_670_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_693_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_669_, v_param_673_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v___x_678_; lean_object* v___x_680_; 
lean_dec_ref_known(v___x_677_, 1);
v___x_678_ = lean_box(0);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 2, v___x_678_);
v___x_680_ = v___x_675_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_id_671_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_method_672_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_692_; 
v_a_682_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_692_ == 0)
{
v___x_684_ = v___x_677_;
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_677_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_691_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 2, v___x_687_);
v___x_689_ = v___x_675_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_id_671_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_method_672_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object* v_inst_694_){
_start:
{
lean_object* v___f_695_; 
v___f_695_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_695_, 0, v_inst_694_);
return v___f_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object* v_00_u03b1_696_, lean_object* v_inst_697_){
_start:
{
lean_object* v___f_698_; 
v___f_698_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_698_, 0, v_inst_697_);
return v___f_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_x_699_) == 0)
{
lean_object* v___x_700_; 
v___x_700_ = lean_box(0);
return v___x_700_;
}
else
{
lean_object* v_val_701_; lean_object* v___x_702_; 
v_val_701_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_val_701_);
lean_dec_ref_known(v_x_699_, 1);
v___x_702_ = l_Lean_Json_Structured_toJson(v_val_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ofMessage_x3f(lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_object* v_id_704_; lean_object* v_method_705_; lean_object* v_params_x3f_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_715_; 
v_id_704_ = lean_ctor_get(v_x_703_, 0);
v_method_705_ = lean_ctor_get(v_x_703_, 1);
v_params_x3f_706_ = lean_ctor_get(v_x_703_, 2);
v_isSharedCheck_715_ = !lean_is_exclusive(v_x_703_);
if (v_isSharedCheck_715_ == 0)
{
v___x_708_ = v_x_703_;
v_isShared_709_ = v_isSharedCheck_715_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_params_x3f_706_);
lean_inc(v_method_705_);
lean_inc(v_id_704_);
lean_dec(v_x_703_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_715_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 2, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_id_704_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_method_705_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v___x_710_);
v___x_712_ = v_reuseFailAlloc_714_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; 
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
}
else
{
lean_object* v___x_716_; 
lean_dec_ref(v_x_703_);
v___x_716_ = lean_box(0);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default___redArg(lean_object* v_inst_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_inst_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default(lean_object* v_00_u03b1_720_, lean_object* v_inst_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___redArg(lean_object* v_inst_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object* v_a_725_, lean_object* v_inst_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_726_);
return v___x_727_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq___redArg(lean_object* v_inst_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
lean_object* v_method_731_; lean_object* v_param_732_; lean_object* v_method_733_; lean_object* v_param_734_; uint8_t v___x_735_; 
v_method_731_ = lean_ctor_get(v_x_729_, 0);
lean_inc_ref(v_method_731_);
v_param_732_ = lean_ctor_get(v_x_729_, 1);
lean_inc(v_param_732_);
lean_dec_ref(v_x_729_);
v_method_733_ = lean_ctor_get(v_x_730_, 0);
lean_inc_ref(v_method_733_);
v_param_734_ = lean_ctor_get(v_x_730_, 1);
lean_inc(v_param_734_);
lean_dec_ref(v_x_730_);
v___x_735_ = lean_string_dec_eq(v_method_731_, v_method_733_);
lean_dec_ref(v_method_733_);
lean_dec_ref(v_method_731_);
if (v___x_735_ == 0)
{
lean_dec(v_param_734_);
lean_dec(v_param_732_);
lean_dec_ref(v_inst_728_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_apply_2(v_inst_728_, v_param_732_, v_param_734_);
v___x_737_ = lean_unbox(v___x_736_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___redArg___boxed(lean_object* v_inst_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
uint8_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_738_, v_x_739_, v_x_740_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq(lean_object* v_00_u03b1_743_, lean_object* v_inst_744_, lean_object* v_x_745_, lean_object* v_x_746_){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_744_, v_x_745_, v_x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___boxed(lean_object* v_00_u03b1_748_, lean_object* v_inst_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l_Lean_JsonRpc_instBEqNotification_beq(v_00_u03b1_748_, v_inst_749_, v_x_750_, v_x_751_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___redArg(lean_object* v_inst_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(v___x_755_, 0, lean_box(0));
lean_closure_set(v___x_755_, 1, v_inst_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object* v_00_u03b1_756_, lean_object* v_inst_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(v___x_758_, 0, lean_box(0));
lean_closure_set(v___x_758_, 1, v_inst_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(lean_object* v_inst_759_, lean_object* v_r_760_){
_start:
{
lean_object* v_method_761_; lean_object* v_param_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_782_; 
v_method_761_ = lean_ctor_get(v_r_760_, 0);
v_param_762_ = lean_ctor_get(v_r_760_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v_r_760_);
if (v_isSharedCheck_782_ == 0)
{
v___x_764_ = v_r_760_;
v_isShared_765_ = v_isSharedCheck_782_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_param_762_);
lean_inc(v_method_761_);
lean_dec(v_r_760_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_782_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_759_, v_param_762_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_769_; 
lean_dec_ref_known(v___x_766_, 1);
v___x_767_ = lean_box(0);
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 1);
lean_ctor_set(v___x_764_, 1, v___x_767_);
v___x_769_ = v___x_764_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_method_761_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_781_; 
v_a_771_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_781_ == 0)
{
v___x_773_ = v___x_766_;
v_isShared_774_ = v_isSharedCheck_781_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_766_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_781_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_780_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 1);
lean_ctor_set(v___x_764_, 1, v___x_776_);
v___x_778_ = v___x_764_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_method_761_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(lean_object* v_inst_783_){
_start:
{
lean_object* v___f_784_; 
v___f_784_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_784_, 0, v_inst_783_);
return v___f_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object* v_00_u03b1_785_, lean_object* v_inst_786_){
_start:
{
lean_object* v___f_787_; 
v___f_787_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_787_, 0, v_inst_786_);
return v___f_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ofMessage_x3f(lean_object* v_x_788_){
_start:
{
if (lean_obj_tag(v_x_788_) == 1)
{
lean_object* v_method_789_; lean_object* v_params_x3f_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_799_; 
v_method_789_ = lean_ctor_get(v_x_788_, 0);
v_params_x3f_790_ = lean_ctor_get(v_x_788_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v_x_788_);
if (v_isSharedCheck_799_ == 0)
{
v___x_792_ = v_x_788_;
v_isShared_793_ = v_isSharedCheck_799_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_params_x3f_790_);
lean_inc(v_method_789_);
lean_dec(v_x_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_799_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_790_);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 0);
lean_ctor_set(v___x_792_, 1, v___x_794_);
v___x_796_ = v___x_792_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_method_789_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_794_);
v___x_796_ = v_reuseFailAlloc_798_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; 
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
}
else
{
lean_object* v___x_800_; 
lean_dec_ref(v_x_788_);
v___x_800_ = lean_box(0);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default___redArg(lean_object* v_inst_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default));
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v_inst_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default(lean_object* v_00_u03b1_804_, lean_object* v_inst_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___redArg(lean_object* v_inst_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object* v_a_809_, lean_object* v_inst_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_810_);
return v___x_811_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq___redArg(lean_object* v_inst_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
lean_object* v_id_815_; lean_object* v_result_816_; lean_object* v_id_817_; lean_object* v_result_818_; uint8_t v___x_819_; 
v_id_815_ = lean_ctor_get(v_x_813_, 0);
lean_inc(v_id_815_);
v_result_816_ = lean_ctor_get(v_x_813_, 1);
lean_inc(v_result_816_);
lean_dec_ref(v_x_813_);
v_id_817_ = lean_ctor_get(v_x_814_, 0);
lean_inc(v_id_817_);
v_result_818_ = lean_ctor_get(v_x_814_, 1);
lean_inc(v_result_818_);
lean_dec_ref(v_x_814_);
v___x_819_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_815_, v_id_817_);
lean_dec(v_id_817_);
lean_dec(v_id_815_);
if (v___x_819_ == 0)
{
lean_dec(v_result_818_);
lean_dec(v_result_816_);
lean_dec_ref(v_inst_812_);
return v___x_819_;
}
else
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = lean_apply_2(v_inst_812_, v_result_816_, v_result_818_);
v___x_821_ = lean_unbox(v___x_820_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___redArg___boxed(lean_object* v_inst_822_, lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
uint8_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_822_, v_x_823_, v_x_824_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq(lean_object* v_00_u03b1_827_, lean_object* v_inst_828_, lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_828_, v_x_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___boxed(lean_object* v_00_u03b1_832_, lean_object* v_inst_833_, lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Lean_JsonRpc_instBEqResponse_beq(v_00_u03b1_832_, v_inst_833_, v_x_834_, v_x_835_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object* v_inst_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_839_, 0, lean_box(0));
lean_closure_set(v___x_839_, 1, v_inst_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object* v_00_u03b1_840_, lean_object* v_inst_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_842_, 0, lean_box(0));
lean_closure_set(v___x_842_, 1, v_inst_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(lean_object* v_inst_843_, lean_object* v_r_844_){
_start:
{
lean_object* v_id_845_; lean_object* v_result_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
v_id_845_ = lean_ctor_get(v_r_844_, 0);
v_result_846_ = lean_ctor_get(v_r_844_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_r_844_);
if (v_isSharedCheck_854_ == 0)
{
v___x_848_ = v_r_844_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_result_846_);
lean_inc(v_id_845_);
lean_dec(v_r_844_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_apply_1(v_inst_843_, v_result_846_);
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 2);
lean_ctor_set(v___x_848_, 1, v___x_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_id_845_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object* v_inst_855_){
_start:
{
lean_object* v___f_856_; 
v___f_856_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_856_, 0, v_inst_855_);
return v___f_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object* v_00_u03b1_857_, lean_object* v_inst_858_){
_start:
{
lean_object* v___f_859_; 
v___f_859_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_859_, 0, v_inst_858_);
return v___f_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ofMessage_x3f(lean_object* v_x_860_){
_start:
{
if (lean_obj_tag(v_x_860_) == 2)
{
lean_object* v_id_861_; lean_object* v_result_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_870_; 
v_id_861_ = lean_ctor_get(v_x_860_, 0);
v_result_862_ = lean_ctor_get(v_x_860_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_x_860_);
if (v_isSharedCheck_870_ == 0)
{
v___x_864_ = v_x_860_;
v_isShared_865_ = v_isSharedCheck_870_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_result_862_);
lean_inc(v_id_861_);
lean_dec(v_x_860_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_870_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set_tag(v___x_864_, 0);
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_id_861_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_result_862_);
v___x_867_ = v_reuseFailAlloc_869_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; 
v___x_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
return v___x_868_;
}
}
}
else
{
lean_object* v___x_871_; 
lean_dec_ref(v_x_860_);
v___x_871_ = lean_box(0);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___redArg(){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___closed__0));
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___boxed(lean_object* v___dummy_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_JsonRpc_instInhabitedResponseError_default___redArg();
return v_res_880_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0(void){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_JsonRpc_instInhabitedResponseError_default___redArg();
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object* v_00_u03b1_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError___redArg(){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError___redArg___boxed(lean_object* v___dummy_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_JsonRpc_instInhabitedResponseError___redArg();
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object* v_a_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_889_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq___redArg(lean_object* v_inst_890_, lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
lean_object* v_id_893_; uint8_t v_code_894_; lean_object* v_message_895_; lean_object* v_data_x3f_896_; lean_object* v_id_897_; uint8_t v_code_898_; lean_object* v_message_899_; lean_object* v_data_x3f_900_; uint8_t v___x_901_; 
v_id_893_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_id_893_);
v_code_894_ = lean_ctor_get_uint8(v_x_891_, sizeof(void*)*3);
v_message_895_ = lean_ctor_get(v_x_891_, 1);
lean_inc_ref(v_message_895_);
v_data_x3f_896_ = lean_ctor_get(v_x_891_, 2);
lean_inc(v_data_x3f_896_);
lean_dec_ref(v_x_891_);
v_id_897_ = lean_ctor_get(v_x_892_, 0);
lean_inc(v_id_897_);
v_code_898_ = lean_ctor_get_uint8(v_x_892_, sizeof(void*)*3);
v_message_899_ = lean_ctor_get(v_x_892_, 1);
lean_inc_ref(v_message_899_);
v_data_x3f_900_ = lean_ctor_get(v_x_892_, 2);
lean_inc(v_data_x3f_900_);
lean_dec_ref(v_x_892_);
v___x_901_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_893_, v_id_897_);
lean_dec(v_id_897_);
lean_dec(v_id_893_);
if (v___x_901_ == 0)
{
lean_dec(v_data_x3f_900_);
lean_dec_ref(v_message_899_);
lean_dec(v_data_x3f_896_);
lean_dec_ref(v_message_895_);
lean_dec_ref(v_inst_890_);
return v___x_901_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_code_894_, v_code_898_);
if (v___x_902_ == 0)
{
lean_dec(v_data_x3f_900_);
lean_dec_ref(v_message_899_);
lean_dec(v_data_x3f_896_);
lean_dec_ref(v_message_895_);
lean_dec_ref(v_inst_890_);
return v___x_902_;
}
else
{
uint8_t v___x_903_; 
v___x_903_ = lean_string_dec_eq(v_message_895_, v_message_899_);
lean_dec_ref(v_message_899_);
lean_dec_ref(v_message_895_);
if (v___x_903_ == 0)
{
lean_dec(v_data_x3f_900_);
lean_dec(v_data_x3f_896_);
lean_dec_ref(v_inst_890_);
return v___x_903_;
}
else
{
uint8_t v___x_904_; 
v___x_904_ = l_Option_instBEq_beq___redArg(v_inst_890_, v_data_x3f_896_, v_data_x3f_900_);
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(lean_object* v_inst_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_905_, v_x_906_, v_x_907_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object* v_00_u03b1_910_, lean_object* v_inst_911_, lean_object* v_x_912_, lean_object* v_x_913_){
_start:
{
uint8_t v___x_914_; 
v___x_914_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_911_, v_x_912_, v_x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___boxed(lean_object* v_00_u03b1_915_, lean_object* v_inst_916_, lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
uint8_t v_res_919_; lean_object* v_r_920_; 
v_res_919_ = l_Lean_JsonRpc_instBEqResponseError_beq(v_00_u03b1_915_, v_inst_916_, v_x_917_, v_x_918_);
v_r_920_ = lean_box(v_res_919_);
return v_r_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object* v_inst_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_922_, 0, lean_box(0));
lean_closure_set(v___x_922_, 1, v_inst_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object* v_00_u03b1_923_, lean_object* v_inst_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_925_, 0, lean_box(0));
lean_closure_set(v___x_925_, 1, v_inst_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object* v_inst_926_, lean_object* v_r_927_){
_start:
{
lean_object* v_data_x3f_928_; 
v_data_x3f_928_ = lean_ctor_get(v_r_927_, 2);
lean_inc(v_data_x3f_928_);
if (lean_obj_tag(v_data_x3f_928_) == 0)
{
lean_object* v_id_929_; uint8_t v_code_930_; lean_object* v_message_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v_inst_926_);
v_id_929_ = lean_ctor_get(v_r_927_, 0);
v_code_930_ = lean_ctor_get_uint8(v_r_927_, sizeof(void*)*3);
v_message_931_ = lean_ctor_get(v_r_927_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_r_927_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v_r_927_, 2);
lean_dec(v_unused_940_);
v___x_933_ = v_r_927_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_message_931_);
lean_inc(v_id_929_);
lean_dec(v_r_927_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_box(0);
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 3);
lean_ctor_set(v___x_933_, 2, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_id_929_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_message_931_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v___x_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_938_, sizeof(void*)*3, v_code_930_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
else
{
lean_object* v_id_941_; uint8_t v_code_942_; lean_object* v_message_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_959_; 
v_id_941_ = lean_ctor_get(v_r_927_, 0);
v_code_942_ = lean_ctor_get_uint8(v_r_927_, sizeof(void*)*3);
v_message_943_ = lean_ctor_get(v_r_927_, 1);
v_isSharedCheck_959_ = !lean_is_exclusive(v_r_927_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v_r_927_, 2);
lean_dec(v_unused_960_);
v___x_945_ = v_r_927_;
v_isShared_946_ = v_isSharedCheck_959_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_message_943_);
lean_inc(v_id_941_);
lean_dec(v_r_927_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_959_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_val_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_958_; 
v_val_947_ = lean_ctor_get(v_data_x3f_928_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v_data_x3f_928_);
if (v_isSharedCheck_958_ == 0)
{
v___x_949_ = v_data_x3f_928_;
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_val_947_);
lean_dec(v_data_x3f_928_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_apply_1(v_inst_926_, v_val_947_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_951_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 3);
lean_ctor_set(v___x_945_, 2, v___x_953_);
v___x_955_ = v___x_945_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_id_941_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_message_943_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v___x_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, sizeof(void*)*3, v_code_942_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object* v_inst_961_){
_start:
{
lean_object* v___f_962_; 
v___f_962_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_962_, 0, v_inst_961_);
return v___f_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object* v_00_u03b1_963_, lean_object* v_inst_964_){
_start:
{
lean_object* v___f_965_; 
v___f_965_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_965_, 0, v_inst_964_);
return v___f_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object* v_r_966_){
_start:
{
lean_object* v_id_967_; uint8_t v_code_968_; lean_object* v_message_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_977_; 
v_id_967_ = lean_ctor_get(v_r_966_, 0);
v_code_968_ = lean_ctor_get_uint8(v_r_966_, sizeof(void*)*3);
v_message_969_ = lean_ctor_get(v_r_966_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_r_966_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v_r_966_, 2);
lean_dec(v_unused_978_);
v___x_971_ = v_r_966_;
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_message_969_);
lean_inc(v_id_967_);
lean_dec(v_r_966_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_977_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = lean_box(0);
if (v_isShared_972_ == 0)
{
lean_ctor_set_tag(v___x_971_, 3);
lean_ctor_set(v___x_971_, 2, v___x_973_);
v___x_975_ = v___x_971_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_id_967_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_message_969_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v___x_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_976_, sizeof(void*)*3, v_code_968_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ofMessage_x3f(lean_object* v_x_981_){
_start:
{
if (lean_obj_tag(v_x_981_) == 3)
{
lean_object* v_id_982_; uint8_t v_code_983_; lean_object* v_message_984_; lean_object* v_data_x3f_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v_id_982_ = lean_ctor_get(v_x_981_, 0);
v_code_983_ = lean_ctor_get_uint8(v_x_981_, sizeof(void*)*3);
v_message_984_ = lean_ctor_get(v_x_981_, 1);
v_data_x3f_985_ = lean_ctor_get(v_x_981_, 2);
v_isSharedCheck_993_ = !lean_is_exclusive(v_x_981_);
if (v_isSharedCheck_993_ == 0)
{
v___x_987_ = v_x_981_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_data_x3f_985_);
lean_inc(v_message_984_);
lean_inc(v_id_982_);
lean_dec(v_x_981_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 0);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_id_982_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_message_984_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_data_x3f_985_);
lean_ctor_set_uint8(v_reuseFailAlloc_992_, sizeof(void*)*3, v_code_983_);
v___x_990_ = v_reuseFailAlloc_992_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
}
else
{
lean_object* v___x_994_; 
lean_dec_ref(v_x_981_);
v___x_994_ = lean_box(0);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object* v_s_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v_s_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object* v_n_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_n_999_);
return v___x_1000_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_RequestID_lt(lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
switch(lean_obj_tag(v_x_1003_))
{
case 0:
{
if (lean_obj_tag(v_x_1004_) == 0)
{
lean_object* v_s_1005_; lean_object* v_s_1006_; uint8_t v___x_1007_; 
v_s_1005_ = lean_ctor_get(v_x_1003_, 0);
lean_inc_ref(v_s_1005_);
lean_dec_ref_known(v_x_1003_, 1);
v_s_1006_ = lean_ctor_get(v_x_1004_, 0);
lean_inc_ref(v_s_1006_);
lean_dec_ref_known(v_x_1004_, 1);
v___x_1007_ = lean_string_dec_lt(v_s_1005_, v_s_1006_);
lean_dec_ref(v_s_1006_);
lean_dec_ref(v_s_1005_);
return v___x_1007_;
}
else
{
uint8_t v___x_1008_; 
lean_dec_ref_known(v_x_1003_, 1);
lean_dec(v_x_1004_);
v___x_1008_ = 0;
return v___x_1008_;
}
}
case 1:
{
switch(lean_obj_tag(v_x_1004_))
{
case 1:
{
lean_object* v_n_1009_; lean_object* v_n_1010_; uint8_t v___x_1011_; 
v_n_1009_ = lean_ctor_get(v_x_1003_, 0);
lean_inc_ref(v_n_1009_);
lean_dec_ref_known(v_x_1003_, 1);
v_n_1010_ = lean_ctor_get(v_x_1004_, 0);
lean_inc_ref(v_n_1010_);
lean_dec_ref_known(v_x_1004_, 1);
v___x_1011_ = l_Lean_JsonNumber_lt(v_n_1009_, v_n_1010_);
return v___x_1011_;
}
case 0:
{
uint8_t v___x_1012_; 
lean_dec_ref_known(v_x_1004_, 1);
lean_dec_ref_known(v_x_1003_, 1);
v___x_1012_ = 1;
return v___x_1012_;
}
default: 
{
uint8_t v___x_1013_; 
lean_dec_ref_known(v_x_1003_, 1);
lean_dec(v_x_1004_);
v___x_1013_ = 0;
return v___x_1013_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_1004_))
{
case 1:
{
uint8_t v___x_1014_; 
lean_dec_ref_known(v_x_1004_, 1);
v___x_1014_ = 1;
return v___x_1014_;
}
case 0:
{
uint8_t v___x_1015_; 
lean_dec_ref_known(v_x_1004_, 1);
v___x_1015_ = 1;
return v___x_1015_;
}
default: 
{
uint8_t v___x_1016_; 
lean_dec(v_x_1004_);
v___x_1016_ = 0;
return v___x_1016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_lt___boxed(lean_object* v_x_1017_, lean_object* v_x_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = l_Lean_JsonRpc_RequestID_lt(v_x_1017_, v_x_1018_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
static lean_object* _init_l_Lean_JsonRpc_RequestID_ltProp(void){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_box(0);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instLTRequestID(void){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_box(0);
return v___x_1022_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object* v_a_1023_, lean_object* v_b_1024_){
_start:
{
uint8_t v___x_1025_; 
v___x_1025_ = l_Lean_JsonRpc_RequestID_lt(v_a_1023_, v_b_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object* v_a_1026_, lean_object* v_b_1027_){
_start:
{
uint8_t v_res_1028_; lean_object* v_r_1029_; 
v_res_1028_ = l_Lean_JsonRpc_instDecidableLtRequestID(v_a_1026_, v_b_1027_);
v_r_1029_ = lean_box(v_res_1028_);
return v_r_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object* v_j_1033_){
_start:
{
switch(lean_obj_tag(v_j_1033_))
{
case 3:
{
lean_object* v_s_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1042_; 
v_s_1034_ = lean_ctor_get(v_j_1033_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_j_1033_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1036_ = v_j_1033_;
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_s_1034_);
lean_dec(v_j_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 0);
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_s_1034_);
v___x_1039_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
}
case 2:
{
lean_object* v_n_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1051_; 
v_n_1043_ = lean_ctor_get(v_j_1033_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_j_1033_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1045_ = v_j_1033_;
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_n_1043_);
lean_dec(v_j_1033_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 1);
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_n_1043_);
v___x_1048_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
return v___x_1049_;
}
}
}
default: 
{
lean_object* v___x_1052_; 
lean_dec(v_j_1033_);
v___x_1052_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object* v_rid_1055_){
_start:
{
switch(lean_obj_tag(v_rid_1055_))
{
case 0:
{
lean_object* v_s_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_s_1056_ = lean_ctor_get(v_rid_1055_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_rid_1055_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v_rid_1055_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_s_1056_);
lean_dec(v_rid_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 3);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_s_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
case 1:
{
lean_object* v_n_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_n_1064_ = lean_ctor_get(v_rid_1055_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_rid_1055_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v_rid_1055_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_n_1064_);
lean_dec(v_rid_1055_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 2);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_n_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
default: 
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_box(0);
return v___x_1072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object* v___x_1090_, lean_object* v___x_1091_, lean_object* v_m_1092_){
_start:
{
lean_object* v___x_1093_; lean_object* v___y_1095_; 
v___x_1093_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_1092_))
{
case 0:
{
lean_object* v_id_1098_; lean_object* v_method_1099_; lean_object* v_params_x3f_1100_; lean_object* v___x_1101_; lean_object* v___y_1103_; 
lean_dec_ref(v___x_1091_);
v_id_1098_ = lean_ctor_get(v_m_1092_, 0);
lean_inc(v_id_1098_);
v_method_1099_ = lean_ctor_get(v_m_1092_, 1);
lean_inc_ref(v_method_1099_);
v_params_x3f_1100_ = lean_ctor_get(v_m_1092_, 2);
lean_inc(v_params_x3f_1100_);
lean_dec_ref_known(v_m_1092_, 3);
v___x_1101_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1098_))
{
case 0:
{
lean_object* v_s_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_s_1114_ = lean_ctor_get(v_id_1098_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_id_1098_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v_id_1098_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_s_1114_);
lean_dec(v_id_1098_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 3);
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_s_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
v___y_1103_ = v___x_1119_;
goto v___jp_1102_;
}
}
}
case 1:
{
lean_object* v_n_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_n_1122_ = lean_ctor_get(v_id_1098_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_id_1098_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v_id_1098_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_n_1122_);
lean_dec(v_id_1098_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 2);
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_n_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
v___y_1103_ = v___x_1127_;
goto v___jp_1102_;
}
}
}
default: 
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_box(0);
v___y_1103_ = v___x_1130_;
goto v___jp_1102_;
}
}
v___jp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1101_);
lean_ctor_set(v___x_1104_, 1, v___y_1103_);
v___x_1105_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_method_1099_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1104_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1112_ = l_Lean_Json_opt___redArg(v___x_1090_, v___x_1111_, v_params_x3f_1100_);
v___x_1113_ = l_List_appendTR___redArg(v___x_1110_, v___x_1112_);
v___y_1095_ = v___x_1113_;
goto v___jp_1094_;
}
}
case 1:
{
lean_object* v_method_1131_; lean_object* v_params_x3f_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1144_; 
lean_dec_ref(v___x_1091_);
v_method_1131_ = lean_ctor_get(v_m_1092_, 0);
v_params_x3f_1132_ = lean_ctor_get(v_m_1092_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_m_1092_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1134_ = v_m_1092_;
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_params_x3f_1132_);
lean_inc(v_method_1131_);
lean_dec(v_m_1092_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1136_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_method_1131_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 0);
lean_ctor_set(v___x_1134_, 1, v___x_1137_);
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1139_ = v___x_1134_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1141_ = l_Lean_Json_opt___redArg(v___x_1090_, v___x_1140_, v_params_x3f_1132_);
v___x_1142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1139_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___y_1095_ = v___x_1142_;
goto v___jp_1094_;
}
}
}
case 2:
{
lean_object* v_id_1145_; lean_object* v_result_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v___x_1091_);
lean_dec_ref(v___x_1090_);
v_id_1145_ = lean_ctor_get(v_m_1092_, 0);
v_result_1146_ = lean_ctor_get(v_m_1092_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_m_1092_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1148_ = v_m_1092_;
v_isShared_1149_ = v_isSharedCheck_1178_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_result_1146_);
lean_inc(v_id_1145_);
lean_dec(v_m_1092_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1178_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___y_1152_; 
v___x_1150_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1145_))
{
case 0:
{
lean_object* v_s_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_s_1161_ = lean_ctor_get(v_id_1145_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_id_1145_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v_id_1145_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_s_1161_);
lean_dec(v_id_1145_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set_tag(v___x_1163_, 3);
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_s_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
v___y_1152_ = v___x_1166_;
goto v___jp_1151_;
}
}
}
case 1:
{
lean_object* v_n_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v_n_1169_ = lean_ctor_get(v_id_1145_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_id_1145_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v_id_1145_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_n_1169_);
lean_dec(v_id_1145_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set_tag(v___x_1171_, 2);
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_n_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
v___y_1152_ = v___x_1174_;
goto v___jp_1151_;
}
}
}
default: 
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_box(0);
v___y_1152_ = v___x_1177_;
goto v___jp_1151_;
}
}
v___jp_1151_:
{
lean_object* v___x_1154_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 0);
lean_ctor_set(v___x_1148_, 1, v___y_1152_);
lean_ctor_set(v___x_1148_, 0, v___x_1150_);
v___x_1154_ = v___x_1148_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v___y_1152_);
v___x_1154_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1155_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v_result_1146_);
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1154_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___y_1095_ = v___x_1159_;
goto v___jp_1094_;
}
}
}
}
default: 
{
lean_object* v_id_1179_; uint8_t v_code_1180_; lean_object* v_message_1181_; lean_object* v_data_x3f_1182_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___x_1202_; lean_object* v___y_1204_; 
lean_dec_ref(v___x_1090_);
v_id_1179_ = lean_ctor_get(v_m_1092_, 0);
lean_inc(v_id_1179_);
v_code_1180_ = lean_ctor_get_uint8(v_m_1092_, sizeof(void*)*3);
v_message_1181_ = lean_ctor_get(v_m_1092_, 1);
lean_inc_ref(v_message_1181_);
v_data_x3f_1182_ = lean_ctor_get(v_m_1092_, 2);
lean_inc(v_data_x3f_1182_);
lean_dec_ref_known(v_m_1092_, 3);
v___x_1202_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1179_))
{
case 0:
{
lean_object* v_s_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_s_1220_ = lean_ctor_get(v_id_1179_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_id_1179_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v_id_1179_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_s_1220_);
lean_dec(v_id_1179_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set_tag(v___x_1222_, 3);
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_s_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
v___y_1204_ = v___x_1225_;
goto v___jp_1203_;
}
}
}
case 1:
{
lean_object* v_n_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_n_1228_ = lean_ctor_get(v_id_1179_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_id_1179_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v_id_1179_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_n_1228_);
lean_dec(v_id_1179_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 2);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_n_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
v___y_1204_ = v___x_1233_;
goto v___jp_1203_;
}
}
}
default: 
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_box(0);
v___y_1204_ = v___x_1236_;
goto v___jp_1203_;
}
}
v___jp_1183_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_inc(v___y_1187_);
lean_inc_ref(v___y_1184_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___y_1184_);
lean_ctor_set(v___x_1188_, 1, v___y_1187_);
v___x_1189_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_message_1181_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1188_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1196_ = l_Lean_Json_opt___redArg(v___x_1091_, v___x_1195_, v_data_x3f_1182_);
v___x_1197_ = l_List_appendTR___redArg(v___x_1194_, v___x_1196_);
v___x_1198_ = l_Lean_Json_mkObj(v___x_1197_);
lean_dec(v___x_1197_);
lean_inc_ref(v___y_1186_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___y_1186_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___x_1192_);
v___x_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___y_1185_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___y_1095_ = v___x_1201_;
goto v___jp_1094_;
}
v___jp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1202_);
lean_ctor_set(v___x_1205_, 1, v___y_1204_);
v___x_1206_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1207_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_1180_)
{
case 0:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1208_;
goto v___jp_1183_;
}
case 1:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1209_;
goto v___jp_1183_;
}
case 2:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1210_;
goto v___jp_1183_;
}
case 3:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1211_;
goto v___jp_1183_;
}
case 4:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1212_;
goto v___jp_1183_;
}
case 5:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1213_;
goto v___jp_1183_;
}
case 6:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1214_;
goto v___jp_1183_;
}
case 7:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1215_;
goto v___jp_1183_;
}
case 8:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1216_;
goto v___jp_1183_;
}
case 9:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1217_;
goto v___jp_1183_;
}
case 10:
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1218_;
goto v___jp_1183_;
}
default: 
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_1184_ = v___x_1207_;
v___y_1185_ = v___x_1205_;
v___y_1186_ = v___x_1206_;
v___y_1187_ = v___x_1219_;
goto v___jp_1183_;
}
}
}
}
}
v___jp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1093_);
lean_ctor_set(v___x_1096_, 1, v___y_1095_);
v___x_1097_ = l_Lean_Json_mkObj(v___x_1096_);
lean_dec_ref_known(v___x_1096_, 2);
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object* v___f_1246_, lean_object* v___f_1247_, lean_object* v___x_1248_, lean_object* v___x_1249_, lean_object* v_j_1250_){
_start:
{
lean_object* v___y_1254_; uint8_t v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1250_);
v___x_1266_ = l_Lean_Json_getObjVal_x3f(v_j_1250_, v___x_1265_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_j_1250_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v___x_1248_);
lean_dec_ref(v___f_1247_);
lean_dec_ref(v___f_1246_);
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_object* v_a_1275_; 
v_a_1275_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1266_, 1);
if (lean_obj_tag(v_a_1275_) == 3)
{
lean_object* v_s_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v_s_1276_ = lean_ctor_get(v_a_1275_, 0);
lean_inc_ref(v_s_1276_);
lean_dec_ref_known(v_a_1275_, 1);
v___x_1277_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1278_ = lean_string_dec_eq(v_s_1276_, v___x_1277_);
lean_dec_ref(v_s_1276_);
if (v___x_1278_ == 0)
{
lean_dec(v_j_1250_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v___x_1248_);
lean_dec_ref(v___f_1247_);
lean_dec_ref(v___f_1246_);
goto v___jp_1251_;
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1250_);
v___x_1280_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1250_, v___f_1246_, v___x_1279_);
if (lean_obj_tag(v___x_1280_) == 0)
{
goto v___jp_1337_;
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v_a_1364_ = lean_ctor_get(v___x_1280_, 0);
v___x_1365_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1248_);
lean_inc(v_j_1250_);
v___x_1366_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1250_, v___x_1248_, v___x_1365_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_dec_ref_known(v___x_1366_, 1);
goto v___jp_1337_;
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1388_; 
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1280_, 1);
lean_dec_ref(v___x_1248_);
lean_dec_ref(v___f_1247_);
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1388_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1388_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___y_1372_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1378_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1250_, v___x_1249_, v___x_1377_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1379_; 
lean_dec_ref_known(v___x_1378_, 1);
v___x_1379_ = lean_box(0);
v___y_1372_ = v___x_1379_;
goto v___jp_1371_;
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
v_a_1380_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1378_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1378_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
v___y_1372_ = v___x_1385_;
goto v___jp_1371_;
}
}
}
v___jp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1373_, 0, v_a_1364_);
lean_ctor_set(v___x_1373_, 1, v_a_1367_);
lean_ctor_set(v___x_1373_, 2, v___y_1372_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1373_);
v___x_1375_ = v___x_1369_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
v___jp_1281_:
{
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_j_1250_);
lean_dec_ref(v___x_1248_);
lean_dec_ref(v___f_1247_);
v_a_1282_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1280_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_a_1290_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1291_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1292_ = l_Lean_Json_getObjVal_x3f(v_j_1250_, v___x_1291_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_a_1290_);
lean_dec_ref(v___x_1248_);
lean_dec_ref(v___f_1247_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_a_1301_ = lean_ctor_get(v___x_1292_, 0);
lean_inc_n(v_a_1301_, 2);
lean_dec_ref_known(v___x_1292_, 1);
v___x_1302_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1303_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1301_, v___f_1247_, v___x_1302_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_a_1301_);
lean_dec(v_a_1290_);
lean_dec_ref(v___x_1248_);
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_a_1312_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1313_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1301_);
v___x_1314_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1301_, v___x_1248_, v___x_1313_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec(v_a_1312_);
lean_dec(v_a_1301_);
lean_dec(v_a_1290_);
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
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
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_a_1323_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1324_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1325_ = l_Lean_Json_getObjVal_x3f(v_a_1301_, v___x_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
lean_dec_ref_known(v___x_1325_, 1);
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_unbox(v_a_1312_);
lean_dec(v_a_1312_);
v___y_1254_ = v_a_1290_;
v___y_1255_ = v___x_1327_;
v___y_1256_ = v_a_1323_;
v___y_1257_ = v___x_1326_;
goto v___jp_1253_;
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1336_; 
v_a_1328_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1330_ = v___x_1325_;
v_isShared_1331_ = v_isSharedCheck_1336_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1325_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1336_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_unbox(v_a_1312_);
lean_dec(v_a_1312_);
v___y_1254_ = v_a_1290_;
v___y_1255_ = v___x_1334_;
v___y_1256_ = v_a_1323_;
v___y_1257_ = v___x_1333_;
goto v___jp_1253_;
}
}
}
}
}
}
}
}
v___jp_1337_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1248_);
lean_inc(v_j_1250_);
v___x_1339_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1250_, v___x_1248_, v___x_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_dec_ref_known(v___x_1339_, 1);
lean_dec_ref(v___x_1249_);
if (lean_obj_tag(v___x_1280_) == 0)
{
goto v___jp_1281_;
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_a_1340_ = lean_ctor_get(v___x_1280_, 0);
v___x_1341_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1250_);
v___x_1342_ = l_Lean_Json_getObjVal_x3f(v_j_1250_, v___x_1341_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_dec_ref_known(v___x_1342_, 1);
goto v___jp_1281_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1351_; 
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1280_, 1);
lean_dec(v_j_1250_);
lean_dec_ref(v___x_1248_);
lean_dec_ref(v___f_1247_);
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_a_1340_);
lean_ctor_set(v___x_1347_, 1, v_a_1343_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v___x_1248_);
lean_dec_ref(v___f_1247_);
v_a_1352_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1339_, 1);
v___x_1353_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1354_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1250_, v___x_1249_, v___x_1353_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1355_; 
lean_dec_ref_known(v___x_1354_, 1);
v___x_1355_ = lean_box(0);
v___y_1261_ = v_a_1352_;
v___y_1262_ = v___x_1355_;
goto v___jp_1260_;
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
v_a_1356_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1354_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1354_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
v___y_1261_ = v_a_1352_;
v___y_1262_ = v___x_1361_;
goto v___jp_1260_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1275_);
lean_dec(v_j_1250_);
lean_dec_ref(v___x_1249_);
lean_dec_ref(v___x_1248_);
lean_dec_ref(v___f_1247_);
lean_dec_ref(v___f_1246_);
goto v___jp_1251_;
}
}
v___jp_1251_:
{
lean_object* v___x_1252_; 
v___x_1252_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1));
return v___x_1252_;
}
v___jp_1253_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1258_, 0, v___y_1254_);
lean_ctor_set(v___x_1258_, 1, v___y_1256_);
lean_ctor_set(v___x_1258_, 2, v___y_1257_);
lean_ctor_set_uint8(v___x_1258_, sizeof(void*)*3, v___y_1255_);
v___x_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
v___jp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___y_1261_);
lean_ctor_set(v___x_1263_, 1, v___y_1262_);
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object* v___x_1402_, lean_object* v_inst_1403_, lean_object* v_j_1404_){
_start:
{
lean_object* v_method_1408_; lean_object* v_params_x3f_1409_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1404_);
v___x_1432_ = l_Lean_Json_getObjVal_x3f(v_j_1404_, v___x_1431_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec(v_j_1404_);
lean_dec_ref(v_inst_1403_);
lean_dec_ref(v___x_1402_);
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_object* v_a_1441_; 
v_a_1441_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1432_, 1);
if (lean_obj_tag(v_a_1441_) == 3)
{
lean_object* v_s_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_s_1442_ = lean_ctor_get(v_a_1441_, 0);
lean_inc_ref(v_s_1442_);
lean_dec_ref_known(v_a_1441_, 1);
v___x_1443_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1444_ = lean_string_dec_eq(v_s_1442_, v___x_1443_);
lean_dec_ref(v_s_1442_);
if (v___x_1444_ == 0)
{
lean_dec(v_j_1404_);
lean_dec_ref(v_inst_1403_);
lean_dec_ref(v___x_1402_);
goto v___jp_1429_;
}
else
{
lean_object* v___f_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___f_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___f_1445_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___closed__0));
v___x_1446_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__0));
v___x_1447_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__1));
v___f_1448_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___closed__0));
v___x_1449_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1404_);
v___x_1450_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1404_, v___f_1445_, v___x_1449_);
if (lean_obj_tag(v___x_1450_) == 0)
{
goto v___jp_1491_;
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1404_);
v___x_1509_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1404_, v___x_1446_, v___x_1508_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_dec_ref_known(v___x_1509_, 1);
goto v___jp_1491_;
}
else
{
lean_dec_ref_known(v___x_1509_, 1);
lean_dec_ref_known(v___x_1450_, 1);
lean_dec(v_j_1404_);
lean_dec_ref(v_inst_1403_);
lean_dec_ref(v___x_1402_);
goto v___jp_1405_;
}
}
v___jp_1451_:
{
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec(v_j_1404_);
v_a_1452_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1450_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1450_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_dec_ref_known(v___x_1450_, 1);
v___x_1460_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1461_ = l_Lean_Json_getObjVal_x3f(v_j_1404_, v___x_1460_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_a_1470_ = lean_ctor_get(v___x_1461_, 0);
lean_inc_n(v_a_1470_, 2);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1471_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1472_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1470_, v___f_1448_, v___x_1471_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_a_1470_);
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec_ref_known(v___x_1472_, 1);
v___x_1481_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1482_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1470_, v___x_1446_, v___x_1481_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
else
{
lean_dec_ref_known(v___x_1482_, 1);
goto v___jp_1405_;
}
}
}
}
}
v___jp_1491_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1404_);
v___x_1493_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1404_, v___x_1446_, v___x_1492_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_dec_ref_known(v___x_1493_, 1);
lean_dec_ref(v_inst_1403_);
lean_dec_ref(v___x_1402_);
if (lean_obj_tag(v___x_1450_) == 0)
{
goto v___jp_1451_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1404_);
v___x_1495_ = l_Lean_Json_getObjVal_x3f(v_j_1404_, v___x_1494_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_dec_ref_known(v___x_1495_, 1);
goto v___jp_1451_;
}
else
{
lean_dec_ref_known(v___x_1495_, 1);
lean_dec_ref_known(v___x_1450_, 1);
lean_dec(v_j_1404_);
goto v___jp_1405_;
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_dec_ref(v___x_1450_);
v_a_1496_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1493_, 1);
v___x_1497_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1498_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1404_, v___x_1447_, v___x_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v___x_1499_; 
lean_dec_ref_known(v___x_1498_, 1);
v___x_1499_ = lean_box(0);
v_method_1408_ = v_a_1496_;
v_params_x3f_1409_ = v___x_1499_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_a_1500_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1498_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1498_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
v_method_1408_ = v_a_1496_;
v_params_x3f_1409_ = v___x_1505_;
goto v___jp_1407_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1441_);
lean_dec(v_j_1404_);
lean_dec_ref(v_inst_1403_);
lean_dec_ref(v___x_1402_);
goto v___jp_1429_;
}
}
v___jp_1405_:
{
lean_object* v___x_1406_; 
v___x_1406_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1));
return v___x_1406_;
}
v___jp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = l_Lean_Option_toJson___redArg(v___x_1402_, v_params_x3f_1409_);
v___x_1411_ = lean_apply_1(v_inst_1403_, v___x_1410_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec_ref(v_method_1408_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1428_; 
v_a_1420_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1422_ = v___x_1411_;
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1411_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_method_1408_);
lean_ctor_set(v___x_1424_, 1, v_a_1420_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
v___jp_1429_:
{
lean_object* v___x_1430_; 
v___x_1430_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2));
return v___x_1430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object* v_inst_1510_){
_start:
{
lean_object* v___x_1511_; lean_object* v___f_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1512_, 0, v___x_1511_);
lean_closure_set(v___f_1512_, 1, v_inst_1510_);
return v___f_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object* v_00_u03b1_1513_, lean_object* v_inst_1514_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_JsonRpc_instFromJsonNotification___redArg(v_inst_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx(lean_object* v_x_1516_){
_start:
{
switch(lean_obj_tag(v_x_1516_))
{
case 0:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_unsigned_to_nat(0u);
return v___x_1517_;
}
case 1:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_unsigned_to_nat(1u);
return v___x_1518_;
}
case 2:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_unsigned_to_nat(2u);
return v___x_1519_;
}
default: 
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_unsigned_to_nat(3u);
return v___x_1520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___boxed(lean_object* v_x_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_JsonRpc_MessageMetaData_ctorIdx(v_x_1521_);
lean_dec_ref(v_x_1521_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(lean_object* v_t_1523_, lean_object* v_k_1524_){
_start:
{
switch(lean_obj_tag(v_t_1523_))
{
case 0:
{
lean_object* v_id_1525_; lean_object* v_method_1526_; lean_object* v___x_1527_; 
v_id_1525_ = lean_ctor_get(v_t_1523_, 0);
lean_inc(v_id_1525_);
v_method_1526_ = lean_ctor_get(v_t_1523_, 1);
lean_inc_ref(v_method_1526_);
lean_dec_ref_known(v_t_1523_, 2);
v___x_1527_ = lean_apply_2(v_k_1524_, v_id_1525_, v_method_1526_);
return v___x_1527_;
}
case 1:
{
lean_object* v_method_1528_; lean_object* v___x_1529_; 
v_method_1528_ = lean_ctor_get(v_t_1523_, 0);
lean_inc_ref(v_method_1528_);
lean_dec_ref_known(v_t_1523_, 1);
v___x_1529_ = lean_apply_1(v_k_1524_, v_method_1528_);
return v___x_1529_;
}
case 2:
{
lean_object* v_id_1530_; lean_object* v___x_1531_; 
v_id_1530_ = lean_ctor_get(v_t_1523_, 0);
lean_inc(v_id_1530_);
lean_dec_ref_known(v_t_1523_, 1);
v___x_1531_ = lean_apply_1(v_k_1524_, v_id_1530_);
return v___x_1531_;
}
default: 
{
lean_object* v_id_1532_; uint8_t v_code_1533_; lean_object* v_message_1534_; lean_object* v_data_x3f_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_id_1532_ = lean_ctor_get(v_t_1523_, 0);
lean_inc(v_id_1532_);
v_code_1533_ = lean_ctor_get_uint8(v_t_1523_, sizeof(void*)*3);
v_message_1534_ = lean_ctor_get(v_t_1523_, 1);
lean_inc_ref(v_message_1534_);
v_data_x3f_1535_ = lean_ctor_get(v_t_1523_, 2);
lean_inc(v_data_x3f_1535_);
lean_dec_ref_known(v_t_1523_, 3);
v___x_1536_ = lean_box(v_code_1533_);
v___x_1537_ = lean_apply_4(v_k_1524_, v_id_1532_, v___x_1536_, v_message_1534_, v_data_x3f_1535_);
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim(lean_object* v_motive_1538_, lean_object* v_ctorIdx_1539_, lean_object* v_t_1540_, lean_object* v_h_1541_, lean_object* v_k_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1540_, v_k_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(lean_object* v_motive_1544_, lean_object* v_ctorIdx_1545_, lean_object* v_t_1546_, lean_object* v_h_1547_, lean_object* v_k_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_JsonRpc_MessageMetaData_ctorElim(v_motive_1544_, v_ctorIdx_1545_, v_t_1546_, v_h_1547_, v_k_1548_);
lean_dec(v_ctorIdx_1545_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim___redArg(lean_object* v_t_1550_, lean_object* v_request_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1550_, v_request_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim(lean_object* v_motive_1553_, lean_object* v_t_1554_, lean_object* v_h_1555_, lean_object* v_request_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1554_, v_request_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(lean_object* v_t_1558_, lean_object* v_notification_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1558_, v_notification_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim(lean_object* v_motive_1561_, lean_object* v_t_1562_, lean_object* v_h_1563_, lean_object* v_notification_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1562_, v_notification_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(lean_object* v_t_1566_, lean_object* v_response_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1566_, v_response_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim(lean_object* v_motive_1569_, lean_object* v_t_1570_, lean_object* v_h_1571_, lean_object* v_response_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1570_, v_response_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim___redArg(lean_object* v_t_1574_, lean_object* v_responseError_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1574_, v_responseError_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim(lean_object* v_motive_1577_, lean_object* v_t_1578_, lean_object* v_h_1579_, lean_object* v_responseError_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1578_, v_responseError_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_metaData(lean_object* v_x_1587_){
_start:
{
switch(lean_obj_tag(v_x_1587_))
{
case 0:
{
lean_object* v_id_1588_; lean_object* v_method_1589_; lean_object* v___x_1590_; 
v_id_1588_ = lean_ctor_get(v_x_1587_, 0);
lean_inc(v_id_1588_);
v_method_1589_ = lean_ctor_get(v_x_1587_, 1);
lean_inc_ref(v_method_1589_);
lean_dec_ref_known(v_x_1587_, 3);
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_id_1588_);
lean_ctor_set(v___x_1590_, 1, v_method_1589_);
return v___x_1590_;
}
case 1:
{
lean_object* v_method_1591_; lean_object* v___x_1592_; 
v_method_1591_ = lean_ctor_get(v_x_1587_, 0);
lean_inc_ref(v_method_1591_);
lean_dec_ref_known(v_x_1587_, 2);
v___x_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1592_, 0, v_method_1591_);
return v___x_1592_;
}
case 2:
{
lean_object* v_id_1593_; lean_object* v___x_1594_; 
v_id_1593_ = lean_ctor_get(v_x_1587_, 0);
lean_inc(v_id_1593_);
lean_dec_ref_known(v_x_1587_, 2);
v___x_1594_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_id_1593_);
return v___x_1594_;
}
default: 
{
lean_object* v_id_1595_; uint8_t v_code_1596_; lean_object* v_message_1597_; lean_object* v_data_x3f_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_id_1595_ = lean_ctor_get(v_x_1587_, 0);
v_code_1596_ = lean_ctor_get_uint8(v_x_1587_, sizeof(void*)*3);
v_message_1597_ = lean_ctor_get(v_x_1587_, 1);
v_data_x3f_1598_ = lean_ctor_get(v_x_1587_, 2);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_x_1587_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v_x_1587_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_data_x3f_1598_);
lean_inc(v_message_1597_);
lean_inc(v_id_1595_);
lean_dec(v_x_1587_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_id_1595_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_message_1597_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_data_x3f_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1604_, sizeof(void*)*3, v_code_1596_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_toMessage(lean_object* v_x_1606_){
_start:
{
switch(lean_obj_tag(v_x_1606_))
{
case 0:
{
lean_object* v_id_1607_; lean_object* v_method_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_id_1607_ = lean_ctor_get(v_x_1606_, 0);
lean_inc(v_id_1607_);
v_method_1608_ = lean_ctor_get(v_x_1606_, 1);
lean_inc_ref(v_method_1608_);
lean_dec_ref_known(v_x_1606_, 2);
v___x_1609_ = lean_box(0);
v___x_1610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1610_, 0, v_id_1607_);
lean_ctor_set(v___x_1610_, 1, v_method_1608_);
lean_ctor_set(v___x_1610_, 2, v___x_1609_);
return v___x_1610_;
}
case 1:
{
lean_object* v_method_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_method_1611_ = lean_ctor_get(v_x_1606_, 0);
lean_inc_ref(v_method_1611_);
lean_dec_ref_known(v_x_1606_, 1);
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1613_, 0, v_method_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
return v___x_1613_;
}
case 2:
{
lean_object* v_id_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_id_1614_ = lean_ctor_get(v_x_1606_, 0);
lean_inc(v_id_1614_);
lean_dec_ref_known(v_x_1606_, 1);
v___x_1615_ = lean_box(0);
v___x_1616_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_id_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
return v___x_1616_;
}
default: 
{
lean_object* v_id_1617_; uint8_t v_code_1618_; lean_object* v_message_1619_; lean_object* v_data_x3f_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_id_1617_ = lean_ctor_get(v_x_1606_, 0);
v_code_1618_ = lean_ctor_get_uint8(v_x_1606_, sizeof(void*)*3);
v_message_1619_ = lean_ctor_get(v_x_1606_, 1);
v_data_x3f_1620_ = lean_ctor_get(v_x_1606_, 2);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_x_1606_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v_x_1606_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_data_x3f_1620_);
lean_inc(v_message_1619_);
lean_inc(v_id_1617_);
lean_dec(v_x_1606_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_id_1617_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_message_1619_);
lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_data_x3f_1620_);
lean_ctor_set_uint8(v_reuseFailAlloc_1626_, sizeof(void*)*3, v_code_1618_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(lean_object* v_a_1631_){
_start:
{
lean_object* v_fst_1632_; lean_object* v_snd_1633_; lean_object* v___x_1634_; uint8_t v_decide_1635_; 
v_fst_1632_ = lean_ctor_get(v_a_1631_, 0);
v_snd_1633_ = lean_ctor_get(v_a_1631_, 1);
v___x_1634_ = lean_string_utf8_byte_size(v_fst_1632_);
v_decide_1635_ = lean_nat_dec_eq(v_snd_1633_, v___x_1634_);
if (v_decide_1635_ == 0)
{
uint32_t v___x_1636_; uint32_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1636_ = lean_string_utf8_get_fast(v_fst_1632_, v_snd_1633_);
v___x_1637_ = 34;
v___x_1638_ = lean_uint32_dec_eq(v___x_1636_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1));
v___x_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1640_, 0, v_a_1631_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
return v___x_1640_;
}
else
{
lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1650_; 
lean_inc(v_snd_1633_);
lean_inc(v_fst_1632_);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_a_1631_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; lean_object* v_unused_1652_; 
v_unused_1651_ = lean_ctor_get(v_a_1631_, 1);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_a_1631_, 0);
lean_dec(v_unused_1652_);
v___x_1642_ = v_a_1631_;
v_isShared_1643_ = v_isSharedCheck_1650_;
goto v_resetjp_1641_;
}
else
{
lean_dec(v_a_1631_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1650_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_string_utf8_next_fast(v_fst_1632_, v_snd_1633_);
lean_dec(v_snd_1633_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___x_1644_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_fst_1632_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_1648_ = l_Lean_Json_Parser_strCore(v___x_1647_, v___x_1646_);
return v___x_1648_;
}
}
}
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_a_1631_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1656_; 
lean_inc_ref(v_a_1655_);
v___x_1656_ = l_Lean_Json_Parser_num(v_a_1655_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_pos_1657_; lean_object* v_res_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v_a_1655_);
v_pos_1657_ = lean_ctor_get(v___x_1656_, 0);
v_res_1658_ = lean_ctor_get(v___x_1656_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1660_ = v___x_1656_;
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_res_1658_);
lean_inc(v_pos_1657_);
lean_dec(v___x_1656_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v_res_1658_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v___x_1662_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_pos_1657_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
else
{
lean_object* v_pos_1667_; lean_object* v_err_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1721_; 
v_pos_1667_ = lean_ctor_get(v___x_1656_, 0);
v_err_1668_ = lean_ctor_get(v___x_1656_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1670_ = v___x_1656_;
v_isShared_1671_ = v_isSharedCheck_1721_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_err_1668_);
lean_inc(v_pos_1667_);
lean_dec(v___x_1656_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1721_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v_snd_1672_; lean_object* v_snd_1673_; uint8_t v_decide_1674_; 
v_snd_1672_ = lean_ctor_get(v_a_1655_, 1);
lean_inc(v_snd_1672_);
lean_dec_ref(v_a_1655_);
v_snd_1673_ = lean_ctor_get(v_pos_1667_, 1);
v_decide_1674_ = lean_nat_dec_eq(v_snd_1672_, v_snd_1673_);
lean_dec(v_snd_1672_);
if (v_decide_1674_ == 0)
{
lean_object* v___x_1676_; 
if (v_isShared_1671_ == 0)
{
v___x_1676_ = v___x_1670_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_pos_1667_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_err_1668_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
else
{
lean_object* v___x_1678_; 
lean_inc(v_snd_1673_);
lean_del_object(v___x_1670_);
lean_dec(v_err_1668_);
v___x_1678_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v_pos_1667_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_pos_1679_; lean_object* v_res_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_snd_1673_);
v_pos_1679_ = lean_ctor_get(v___x_1678_, 0);
v_res_1680_ = lean_ctor_get(v___x_1678_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1682_ = v___x_1678_;
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_res_1680_);
lean_inc(v_pos_1679_);
lean_dec(v___x_1678_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_res_1680_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 1, v___x_1684_);
v___x_1686_ = v___x_1682_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_pos_1679_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
lean_object* v_pos_1689_; lean_object* v_err_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1720_; 
v_pos_1689_ = lean_ctor_get(v___x_1678_, 0);
v_err_1690_ = lean_ctor_get(v___x_1678_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1692_ = v___x_1678_;
v_isShared_1693_ = v_isSharedCheck_1720_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_err_1690_);
lean_inc(v_pos_1689_);
lean_dec(v___x_1678_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1720_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_snd_1694_; uint8_t v_decide_1695_; 
v_snd_1694_ = lean_ctor_get(v_pos_1689_, 1);
v_decide_1695_ = lean_nat_dec_eq(v_snd_1673_, v_snd_1694_);
lean_dec(v_snd_1673_);
if (v_decide_1695_ == 0)
{
lean_object* v___x_1697_; 
if (v_isShared_1693_ == 0)
{
v___x_1697_ = v___x_1692_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_pos_1689_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_err_1690_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_del_object(v___x_1692_);
lean_dec(v_err_1690_);
v___x_1699_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___x_1700_ = l_Std_Internal_Parsec_String_pstring(v___x_1699_, v_pos_1689_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_pos_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1709_; 
v_pos_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; 
v_unused_1710_ = lean_ctor_get(v___x_1700_, 1);
lean_dec(v_unused_1710_);
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1709_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_pos_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1709_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = lean_box(2);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v___x_1705_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_pos_1701_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
else
{
lean_object* v_pos_1711_; lean_object* v_err_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v_pos_1711_ = lean_ctor_get(v___x_1700_, 0);
v_err_1712_ = lean_ctor_get(v___x_1700_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1700_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_err_1712_);
lean_inc(v_pos_1711_);
lean_dec(v___x_1700_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_pos_1711_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_err_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object* v_j_1722_, lean_object* v_k_1723_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Lean_Json_getObjValD(v_j_1722_, v_k_1723_);
switch(lean_obj_tag(v___x_1724_))
{
case 3:
{
lean_object* v_s_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1733_; 
v_s_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_s_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 0);
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_s_1725_);
v___x_1730_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
case 2:
{
lean_object* v_n_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1742_; 
v_n_1734_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1736_ = v___x_1724_;
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_n_1734_);
lean_dec(v___x_1724_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set_tag(v___x_1736_, 1);
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_n_1734_);
v___x_1739_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
return v___x_1740_;
}
}
}
default: 
{
lean_object* v___x_1743_; 
lean_dec(v___x_1724_);
v___x_1743_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object* v_j_1744_, lean_object* v_k_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_j_1744_, v_k_1745_);
lean_dec_ref(v_k_1745_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object* v_j_1747_, lean_object* v_k_1748_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Json_getObjValD(v_j_1747_, v_k_1748_);
if (lean_obj_tag(v___x_1751_) == 2)
{
lean_object* v_n_1752_; lean_object* v_mantissa_1753_; lean_object* v_exponent_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_n_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc_ref(v_n_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v_mantissa_1753_ = lean_ctor_get(v_n_1752_, 0);
lean_inc(v_mantissa_1753_);
v_exponent_1754_ = lean_ctor_get(v_n_1752_, 1);
lean_inc(v_exponent_1754_);
lean_dec_ref(v_n_1752_);
v___x_1755_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_1756_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_1758_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_1760_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_1762_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_1764_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1763_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_1766_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_1768_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_1770_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_1772_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_1774_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_1776_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_1778_ = lean_int_dec_eq(v_mantissa_1753_, v___x_1777_);
lean_dec(v_mantissa_1753_);
if (v___x_1778_ == 0)
{
lean_dec(v_exponent_1754_);
goto v___jp_1749_;
}
else
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = lean_unsigned_to_nat(0u);
v___x_1780_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1779_);
lean_dec(v_exponent_1754_);
if (v___x_1780_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1781_; 
v___x_1781_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_1781_;
}
}
}
else
{
lean_object* v___x_1782_; uint8_t v___x_1783_; 
lean_dec(v_mantissa_1753_);
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1782_);
lean_dec(v_exponent_1754_);
if (v___x_1783_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1784_; 
v___x_1784_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_1784_;
}
}
}
else
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
lean_dec(v_mantissa_1753_);
v___x_1785_ = lean_unsigned_to_nat(0u);
v___x_1786_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1785_);
lean_dec(v_exponent_1754_);
if (v___x_1786_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1787_; 
v___x_1787_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_1787_;
}
}
}
else
{
lean_object* v___x_1788_; uint8_t v___x_1789_; 
lean_dec(v_mantissa_1753_);
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1788_);
lean_dec(v_exponent_1754_);
if (v___x_1789_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1790_; 
v___x_1790_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_1790_;
}
}
}
else
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
lean_dec(v_mantissa_1753_);
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1791_);
lean_dec(v_exponent_1754_);
if (v___x_1792_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1793_; 
v___x_1793_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_1793_;
}
}
}
else
{
lean_object* v___x_1794_; uint8_t v___x_1795_; 
lean_dec(v_mantissa_1753_);
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1794_);
lean_dec(v_exponent_1754_);
if (v___x_1795_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1796_; 
v___x_1796_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_1796_;
}
}
}
else
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
lean_dec(v_mantissa_1753_);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1797_);
lean_dec(v_exponent_1754_);
if (v___x_1798_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1799_; 
v___x_1799_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_1799_;
}
}
}
else
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
lean_dec(v_mantissa_1753_);
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1800_);
lean_dec(v_exponent_1754_);
if (v___x_1801_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1802_; 
v___x_1802_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_1802_;
}
}
}
else
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
lean_dec(v_mantissa_1753_);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1803_);
lean_dec(v_exponent_1754_);
if (v___x_1804_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1805_; 
v___x_1805_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_1805_;
}
}
}
else
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
lean_dec(v_mantissa_1753_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1806_);
lean_dec(v_exponent_1754_);
if (v___x_1807_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1808_; 
v___x_1808_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_1808_;
}
}
}
else
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
lean_dec(v_mantissa_1753_);
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1809_);
lean_dec(v_exponent_1754_);
if (v___x_1810_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1811_; 
v___x_1811_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_1811_;
}
}
}
else
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
lean_dec(v_mantissa_1753_);
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = lean_nat_dec_eq(v_exponent_1754_, v___x_1812_);
lean_dec(v_exponent_1754_);
if (v___x_1813_ == 0)
{
goto v___jp_1749_;
}
else
{
lean_object* v___x_1814_; 
v___x_1814_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_1814_;
}
}
}
else
{
lean_dec(v___x_1751_);
goto v___jp_1749_;
}
v___jp_1749_:
{
lean_object* v___x_1750_; 
v___x_1750_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object* v_j_1815_, lean_object* v_k_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_j_1815_, v_k_1816_);
lean_dec_ref(v_k_1816_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object* v_j_1818_, lean_object* v_k_1819_){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = l_Lean_Json_getObjValD(v_j_1818_, v_k_1819_);
v___x_1821_ = l_Lean_Json_getStr_x3f(v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object* v_j_1822_, lean_object* v_k_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_j_1822_, v_k_1823_);
lean_dec_ref(v_k_1823_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object* v_input_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v_fst_1861_; lean_object* v_snd_1862_; lean_object* v___x_1863_; uint8_t v_decide_1864_; 
v_fst_1861_ = lean_ctor_get(v_a_1835_, 0);
v_snd_1862_ = lean_ctor_get(v_a_1835_, 1);
v___x_1863_ = lean_string_utf8_byte_size(v_fst_1861_);
v_decide_1864_ = lean_nat_dec_eq(v_snd_1862_, v___x_1863_);
if (v_decide_1864_ == 0)
{
lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_2214_; 
lean_inc(v_snd_1862_);
lean_inc(v_fst_1861_);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_a_1835_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; lean_object* v_unused_2216_; 
v_unused_2215_ = lean_ctor_get(v_a_1835_, 1);
lean_dec(v_unused_2215_);
v_unused_2216_ = lean_ctor_get(v_a_1835_, 0);
lean_dec(v_unused_2216_);
v___x_1866_ = v_a_1835_;
v_isShared_1867_ = v_isSharedCheck_2214_;
goto v_resetjp_1865_;
}
else
{
lean_dec(v_a_1835_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_2214_;
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
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_fst_1861_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_2213_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; 
v___x_1871_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1870_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_pos_1872_; lean_object* v_res_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_2203_; 
v_pos_1872_ = lean_ctor_get(v___x_1871_, 0);
v_res_1873_ = lean_ctor_get(v___x_1871_, 1);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_1875_ = v___x_1871_;
v_isShared_1876_ = v_isSharedCheck_2203_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_res_1873_);
lean_inc(v_pos_1872_);
lean_dec(v___x_1871_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_2203_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_fst_1877_; lean_object* v_snd_1878_; lean_object* v___x_1879_; uint8_t v_decide_1880_; 
v_fst_1877_ = lean_ctor_get(v_pos_1872_, 0);
v_snd_1878_ = lean_ctor_get(v_pos_1872_, 1);
v___x_1879_ = lean_string_utf8_byte_size(v_fst_1877_);
v_decide_1880_ = lean_nat_dec_eq(v_snd_1878_, v___x_1879_);
if (v_decide_1880_ == 0)
{
lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_2196_; 
lean_inc(v_snd_1878_);
lean_inc(v_fst_1877_);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_pos_1872_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; lean_object* v_unused_2198_; 
v_unused_2197_ = lean_ctor_get(v_pos_1872_, 1);
lean_dec(v_unused_2197_);
v_unused_2198_ = lean_ctor_get(v_pos_1872_, 0);
lean_dec(v_unused_2198_);
v___x_1882_ = v_pos_1872_;
v_isShared_1883_ = v_isSharedCheck_2196_;
goto v_resetjp_1881_;
}
else
{
lean_dec(v_pos_1872_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_2196_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1884_ = lean_string_utf8_next_fast(v_fst_1877_, v_snd_1878_);
lean_dec(v_snd_1878_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 1, v___x_1884_);
v___x_1886_ = v___x_1882_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_fst_1877_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_2195_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v_id_1888_; uint8_t v_code_1889_; lean_object* v_message_1890_; lean_object* v_data_x3f_1891_; lean_object* v_a_1900_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
v___x_1906_ = lean_string_dec_eq(v_res_1873_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
v___x_1908_ = lean_string_dec_eq(v_res_1873_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1910_ = lean_string_dec_eq(v_res_1873_, v___x_1909_);
lean_dec(v_res_1873_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_del_object(v___x_1875_);
lean_dec_ref(v_input_1834_);
v___x_1911_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3));
v___x_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1886_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
return v___x_1912_;
}
else
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_Json_parse(v_input_1834_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1922_; 
lean_del_object(v___x_1875_);
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1922_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 1);
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1920_; 
v___x_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1886_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
return v___x_1920_;
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1924_; 
v_a_1923_ = lean_ctor_get(v___x_1913_, 0);
lean_inc_n(v_a_1923_, 2);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1924_ = l_Lean_Json_getObjVal_x3f(v_a_1923_, v___x_1907_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; 
lean_dec(v_a_1923_);
lean_del_object(v___x_1875_);
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v_a_1900_ = v_a_1925_;
goto v___jp_1899_;
}
else
{
lean_object* v_a_1926_; 
v_a_1926_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1924_, 1);
if (lean_obj_tag(v_a_1926_) == 3)
{
lean_object* v_s_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v_s_1927_ = lean_ctor_get(v_a_1926_, 0);
lean_inc_ref(v_s_1927_);
lean_dec_ref_known(v_a_1926_, 1);
v___x_1928_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1929_ = lean_string_dec_eq(v_s_1927_, v___x_1928_);
lean_dec_ref(v_s_1927_);
if (v___x_1929_ == 0)
{
lean_dec(v_a_1923_);
lean_del_object(v___x_1875_);
goto v___jp_1903_;
}
else
{
lean_object* v___x_1930_; 
lean_inc(v_a_1923_);
v___x_1930_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_1923_, v___x_1905_);
if (lean_obj_tag(v___x_1930_) == 0)
{
goto v___jp_1958_;
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1923_);
v___x_1964_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1923_, v___x_1963_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_dec_ref_known(v___x_1964_, 1);
goto v___jp_1958_;
}
else
{
lean_dec_ref_known(v___x_1964_, 1);
lean_dec_ref_known(v___x_1930_, 1);
lean_dec(v_a_1923_);
lean_del_object(v___x_1875_);
goto v___jp_1896_;
}
}
v___jp_1931_:
{
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1932_; 
lean_dec(v_a_1923_);
lean_del_object(v___x_1875_);
v_a_1932_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1930_, 1);
v_a_1900_ = v_a_1932_;
goto v___jp_1899_;
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1934_ = l_Lean_Json_getObjVal_x3f(v_a_1923_, v___x_1909_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; 
lean_dec(v_a_1933_);
lean_del_object(v___x_1875_);
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v_a_1900_ = v_a_1935_;
goto v___jp_1899_;
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v_a_1936_ = lean_ctor_get(v___x_1934_, 0);
lean_inc_n(v_a_1936_, 2);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1937_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1938_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_1936_, v___x_1937_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; 
lean_dec(v_a_1936_);
lean_dec(v_a_1933_);
lean_del_object(v___x_1875_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v_a_1900_ = v_a_1939_;
goto v___jp_1899_;
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_a_1940_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1941_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1936_);
v___x_1942_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1936_, v___x_1941_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; 
lean_dec(v_a_1940_);
lean_dec(v_a_1936_);
lean_dec(v_a_1933_);
lean_del_object(v___x_1875_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v_a_1900_ = v_a_1943_;
goto v___jp_1899_;
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_a_1944_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1945_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1946_ = l_Lean_Json_getObjVal_x3f(v_a_1936_, v___x_1945_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v___x_1947_; uint8_t v___x_1948_; 
lean_dec_ref_known(v___x_1946_, 1);
v___x_1947_ = lean_box(0);
v___x_1948_ = lean_unbox(v_a_1940_);
lean_dec(v_a_1940_);
v_id_1888_ = v_a_1933_;
v_code_1889_ = v___x_1948_;
v_message_1890_ = v_a_1944_;
v_data_x3f_1891_ = v___x_1947_;
goto v___jp_1887_;
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1957_; 
v_a_1949_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1951_ = v___x_1946_;
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1946_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
uint8_t v___x_1955_; 
v___x_1955_ = lean_unbox(v_a_1940_);
lean_dec(v_a_1940_);
v_id_1888_ = v_a_1933_;
v_code_1889_ = v___x_1955_;
v_message_1890_ = v_a_1944_;
v_data_x3f_1891_ = v___x_1954_;
goto v___jp_1887_;
}
}
}
}
}
}
}
}
v___jp_1958_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1923_);
v___x_1960_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1923_, v___x_1959_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_dec_ref_known(v___x_1960_, 1);
if (lean_obj_tag(v___x_1930_) == 0)
{
goto v___jp_1931_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_1923_);
v___x_1962_ = l_Lean_Json_getObjVal_x3f(v_a_1923_, v___x_1961_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_dec_ref_known(v___x_1962_, 1);
goto v___jp_1931_;
}
else
{
lean_dec_ref_known(v___x_1962_, 1);
lean_dec_ref_known(v___x_1930_, 1);
lean_dec(v_a_1923_);
lean_del_object(v___x_1875_);
goto v___jp_1896_;
}
}
}
else
{
lean_dec_ref_known(v___x_1960_, 1);
lean_dec_ref(v___x_1930_);
lean_dec(v_a_1923_);
lean_del_object(v___x_1875_);
goto v___jp_1896_;
}
}
}
}
else
{
lean_dec(v_a_1926_);
lean_dec(v_a_1923_);
lean_del_object(v___x_1875_);
goto v___jp_1903_;
}
}
}
}
}
else
{
lean_object* v___x_1965_; 
lean_del_object(v___x_1875_);
lean_dec(v_res_1873_);
lean_dec_ref(v_input_1834_);
v___x_1965_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1886_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_pos_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2014_; 
v_pos_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2014_ == 0)
{
lean_object* v_unused_2015_; 
v_unused_2015_ = lean_ctor_get(v___x_1965_, 1);
lean_dec(v_unused_2015_);
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_2014_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_pos_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2014_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_fst_1970_; lean_object* v_snd_1971_; uint8_t v___y_1973_; lean_object* v___x_2012_; uint8_t v_decide_2013_; 
v_fst_1970_ = lean_ctor_get(v_pos_1966_, 0);
v_snd_1971_ = lean_ctor_get(v_pos_1966_, 1);
v___x_2012_ = lean_string_utf8_byte_size(v_fst_1970_);
v_decide_2013_ = lean_nat_dec_eq(v_snd_1971_, v___x_2012_);
if (v_decide_2013_ == 0)
{
v___y_1973_ = v___x_1908_;
goto v___jp_1972_;
}
else
{
v___y_1973_ = v___x_1906_;
goto v___jp_1972_;
}
v___jp_1972_:
{
if (v___y_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
v___x_1974_ = lean_box(0);
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 1);
lean_ctor_set(v___x_1968_, 1, v___x_1974_);
v___x_1976_ = v___x_1968_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_pos_1966_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
else
{
lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2009_; 
lean_inc(v_snd_1971_);
lean_inc(v_fst_1970_);
lean_del_object(v___x_1968_);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_pos_1966_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; lean_object* v_unused_2011_; 
v_unused_2010_ = lean_ctor_get(v_pos_1966_, 1);
lean_dec(v_unused_2010_);
v_unused_2011_ = lean_ctor_get(v_pos_1966_, 0);
lean_dec(v_unused_2011_);
v___x_1979_ = v_pos_1966_;
v_isShared_1980_ = v_isSharedCheck_2009_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v_pos_1966_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2009_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1981_ = lean_string_utf8_next_fast(v_fst_1970_, v_snd_1971_);
lean_dec(v_snd_1971_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v___x_1981_);
v___x_1983_ = v___x_1979_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_fst_1970_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_2008_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1984_; 
v___x_1984_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1983_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_pos_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1997_; 
v_pos_1985_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; 
v_unused_1998_ = lean_ctor_get(v___x_1984_, 1);
lean_dec(v_unused_1998_);
v___x_1987_ = v___x_1984_;
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_pos_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v_fst_1989_; lean_object* v_snd_1990_; lean_object* v___x_1991_; uint8_t v_decide_1992_; 
v_fst_1989_ = lean_ctor_get(v_pos_1985_, 0);
v_snd_1990_ = lean_ctor_get(v_pos_1985_, 1);
v___x_1991_ = lean_string_utf8_byte_size(v_fst_1989_);
v_decide_1992_ = lean_nat_dec_eq(v_snd_1990_, v___x_1991_);
if (v_decide_1992_ == 0)
{
lean_inc(v_snd_1990_);
lean_inc(v_fst_1989_);
lean_del_object(v___x_1987_);
lean_dec(v_pos_1985_);
v___y_1837_ = v_fst_1989_;
v___y_1838_ = v_snd_1990_;
goto v___jp_1836_;
}
else
{
if (v___x_1906_ == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = lean_box(0);
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 1);
lean_ctor_set(v___x_1987_, 1, v___x_1993_);
v___x_1995_ = v___x_1987_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_pos_1985_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
else
{
lean_inc(v_snd_1990_);
lean_inc(v_fst_1989_);
lean_del_object(v___x_1987_);
lean_dec(v_pos_1985_);
v___y_1837_ = v_fst_1989_;
v___y_1838_ = v_snd_1990_;
goto v___jp_1836_;
}
}
}
}
else
{
lean_object* v_pos_1999_; lean_object* v_err_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
v_pos_1999_ = lean_ctor_get(v___x_1984_, 0);
v_err_2000_ = lean_ctor_get(v___x_1984_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1984_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_err_2000_);
lean_inc(v_pos_1999_);
lean_dec(v___x_1984_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_pos_1999_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_err_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
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
lean_object* v_pos_2016_; lean_object* v_err_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
v_pos_2016_ = lean_ctor_get(v___x_1965_, 0);
v_err_2017_ = lean_ctor_get(v___x_1965_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1965_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_err_2017_);
lean_inc(v_pos_2016_);
lean_dec(v___x_1965_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_pos_2016_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_err_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
else
{
lean_object* v___x_2025_; 
lean_del_object(v___x_1875_);
lean_dec(v_res_1873_);
lean_dec_ref(v_input_1834_);
v___x_2025_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(v___x_1886_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_pos_2026_; lean_object* v_res_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2185_; 
v_pos_2026_ = lean_ctor_get(v___x_2025_, 0);
v_res_2027_ = lean_ctor_get(v___x_2025_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2029_ = v___x_2025_;
v_isShared_2030_ = v_isSharedCheck_2185_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_res_2027_);
lean_inc(v_pos_2026_);
lean_dec(v___x_2025_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2185_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_fst_2036_; lean_object* v_snd_2037_; lean_object* v___x_2038_; uint8_t v_decide_2039_; 
v_fst_2036_ = lean_ctor_get(v_pos_2026_, 0);
v_snd_2037_ = lean_ctor_get(v_pos_2026_, 1);
v___x_2038_ = lean_string_utf8_byte_size(v_fst_2036_);
v_decide_2039_ = lean_nat_dec_eq(v_snd_2037_, v___x_2038_);
if (v_decide_2039_ == 0)
{
if (v___x_1906_ == 0)
{
lean_dec(v_res_2027_);
goto v___jp_2031_;
}
else
{
lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2182_; 
lean_inc(v_snd_2037_);
lean_inc(v_fst_2036_);
lean_del_object(v___x_2029_);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_pos_2026_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; lean_object* v_unused_2184_; 
v_unused_2183_ = lean_ctor_get(v_pos_2026_, 1);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_pos_2026_, 0);
lean_dec(v_unused_2184_);
v___x_2041_ = v_pos_2026_;
v_isShared_2042_ = v_isSharedCheck_2182_;
goto v_resetjp_2040_;
}
else
{
lean_dec(v_pos_2026_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2182_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2043_ = lean_string_utf8_next_fast(v_fst_2036_, v_snd_2037_);
lean_dec(v_snd_2037_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 1, v___x_2043_);
v___x_2045_ = v___x_2041_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_fst_2036_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; 
v___x_2046_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2045_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_pos_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2170_; 
v_pos_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v___x_2046_, 1);
lean_dec(v_unused_2171_);
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2170_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_pos_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2170_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v___x_2053_; uint8_t v_decide_2054_; 
v_fst_2051_ = lean_ctor_get(v_pos_2047_, 0);
v_snd_2052_ = lean_ctor_get(v_pos_2047_, 1);
v___x_2053_ = lean_string_utf8_byte_size(v_fst_2051_);
v_decide_2054_ = lean_nat_dec_eq(v_snd_2052_, v___x_2053_);
if (v_decide_2054_ == 0)
{
lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2163_; 
lean_inc(v_snd_2052_);
lean_inc(v_fst_2051_);
lean_del_object(v___x_2049_);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_pos_2047_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; lean_object* v_unused_2165_; 
v_unused_2164_ = lean_ctor_get(v_pos_2047_, 1);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_pos_2047_, 0);
lean_dec(v_unused_2165_);
v___x_2056_ = v_pos_2047_;
v_isShared_2057_ = v_isSharedCheck_2163_;
goto v_resetjp_2055_;
}
else
{
lean_dec(v_pos_2047_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2163_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = lean_string_utf8_next_fast(v_fst_2051_, v_snd_2052_);
lean_dec(v_snd_2052_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v___x_2058_);
v___x_2060_ = v___x_2056_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_fst_2051_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; 
v___x_2061_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2060_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_pos_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2151_; 
v_pos_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v___x_2061_, 1);
lean_dec(v_unused_2152_);
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2151_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_pos_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2151_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v_fst_2066_; lean_object* v_snd_2067_; lean_object* v___x_2068_; uint8_t v_decide_2069_; 
v_fst_2066_ = lean_ctor_get(v_pos_2062_, 0);
v_snd_2067_ = lean_ctor_get(v_pos_2062_, 1);
v___x_2068_ = lean_string_utf8_byte_size(v_fst_2066_);
v_decide_2069_ = lean_nat_dec_eq(v_snd_2067_, v___x_2068_);
if (v_decide_2069_ == 0)
{
lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2144_; 
lean_inc(v_snd_2067_);
lean_inc(v_fst_2066_);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_pos_2062_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; lean_object* v_unused_2146_; 
v_unused_2145_ = lean_ctor_get(v_pos_2062_, 1);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_pos_2062_, 0);
lean_dec(v_unused_2146_);
v___x_2071_ = v_pos_2062_;
v_isShared_2072_ = v_isSharedCheck_2144_;
goto v_resetjp_2070_;
}
else
{
lean_dec(v_pos_2062_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2144_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = lean_string_utf8_next_fast(v_fst_2066_, v_snd_2067_);
lean_dec(v_snd_2067_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v___x_2073_);
v___x_2075_ = v___x_2071_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_fst_2066_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; 
v___x_2076_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2075_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_pos_2077_; lean_object* v_res_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2133_; 
v_pos_2077_ = lean_ctor_get(v___x_2076_, 0);
v_res_2078_ = lean_ctor_get(v___x_2076_, 1);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2080_ = v___x_2076_;
v_isShared_2081_ = v_isSharedCheck_2133_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_res_2078_);
lean_inc(v_pos_2077_);
lean_dec(v___x_2076_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2133_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2088_ = lean_string_dec_eq(v_res_2078_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
lean_del_object(v___x_2080_);
v___x_2089_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2090_ = lean_string_dec_eq(v_res_2078_, v___x_2089_);
lean_dec(v_res_2078_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
lean_dec(v_res_2027_);
v___x_2091_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5));
if (v_isShared_2065_ == 0)
{
lean_ctor_set_tag(v___x_2064_, 1);
lean_ctor_set(v___x_2064_, 1, v___x_2091_);
lean_ctor_set(v___x_2064_, 0, v_pos_2077_);
v___x_2093_ = v___x_2064_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_pos_2077_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2095_, 0, v_res_2027_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v___x_2095_);
lean_ctor_set(v___x_2064_, 0, v_pos_2077_);
v___x_2097_ = v___x_2064_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_pos_2077_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
else
{
lean_object* v_fst_2099_; lean_object* v_snd_2100_; lean_object* v___x_2101_; uint8_t v_decide_2102_; 
lean_dec(v_res_2078_);
lean_del_object(v___x_2064_);
v_fst_2099_ = lean_ctor_get(v_pos_2077_, 0);
v_snd_2100_ = lean_ctor_get(v_pos_2077_, 1);
v___x_2101_ = lean_string_utf8_byte_size(v_fst_2099_);
v_decide_2102_ = lean_nat_dec_eq(v_snd_2100_, v___x_2101_);
if (v_decide_2102_ == 0)
{
if (v___x_2088_ == 0)
{
lean_dec(v_res_2027_);
goto v___jp_2082_;
}
else
{
lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2130_; 
lean_inc(v_snd_2100_);
lean_inc(v_fst_2099_);
lean_del_object(v___x_2080_);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_pos_2077_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; lean_object* v_unused_2132_; 
v_unused_2131_ = lean_ctor_get(v_pos_2077_, 1);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_pos_2077_, 0);
lean_dec(v_unused_2132_);
v___x_2104_ = v_pos_2077_;
v_isShared_2105_ = v_isSharedCheck_2130_;
goto v_resetjp_2103_;
}
else
{
lean_dec(v_pos_2077_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2130_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_string_utf8_next_fast(v_fst_2099_, v_snd_2100_);
lean_dec(v_snd_2100_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 1, v___x_2106_);
v___x_2108_ = v___x_2104_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_fst_2099_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; 
v___x_2109_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2108_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_pos_2110_; lean_object* v_res_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2119_; 
v_pos_2110_ = lean_ctor_get(v___x_2109_, 0);
v_res_2111_ = lean_ctor_get(v___x_2109_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2113_ = v___x_2109_;
v_isShared_2114_ = v_isSharedCheck_2119_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_res_2111_);
lean_inc(v_pos_2110_);
lean_dec(v___x_2109_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2119_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v_res_2027_);
lean_ctor_set(v___x_2115_, 1, v_res_2111_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 1, v___x_2115_);
v___x_2117_ = v___x_2113_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_pos_2110_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
lean_object* v_pos_2120_; lean_object* v_err_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_res_2027_);
v_pos_2120_ = lean_ctor_get(v___x_2109_, 0);
v_err_2121_ = lean_ctor_get(v___x_2109_, 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2109_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_err_2121_);
lean_inc(v_pos_2120_);
lean_dec(v___x_2109_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_pos_2120_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_err_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2027_);
goto v___jp_2082_;
}
}
v___jp_2082_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_box(0);
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 1);
lean_ctor_set(v___x_2080_, 1, v___x_2083_);
v___x_2085_ = v___x_2080_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_pos_2077_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_pos_2134_; lean_object* v_err_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_del_object(v___x_2064_);
lean_dec(v_res_2027_);
v_pos_2134_ = lean_ctor_get(v___x_2076_, 0);
v_err_2135_ = lean_ctor_get(v___x_2076_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2076_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_err_2135_);
lean_inc(v_pos_2134_);
lean_dec(v___x_2076_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_pos_2134_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_err_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
lean_dec(v_res_2027_);
v___x_2147_ = lean_box(0);
if (v_isShared_2065_ == 0)
{
lean_ctor_set_tag(v___x_2064_, 1);
lean_ctor_set(v___x_2064_, 1, v___x_2147_);
v___x_2149_ = v___x_2064_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_pos_2062_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
else
{
lean_object* v_pos_2153_; lean_object* v_err_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_res_2027_);
v_pos_2153_ = lean_ctor_get(v___x_2061_, 0);
v_err_2154_ = lean_ctor_get(v___x_2061_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2061_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_err_2154_);
lean_inc(v_pos_2153_);
lean_dec(v___x_2061_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_pos_2153_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_err_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
lean_dec(v_res_2027_);
v___x_2166_ = lean_box(0);
if (v_isShared_2050_ == 0)
{
lean_ctor_set_tag(v___x_2049_, 1);
lean_ctor_set(v___x_2049_, 1, v___x_2166_);
v___x_2168_ = v___x_2049_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_pos_2047_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
else
{
lean_object* v_pos_2172_; lean_object* v_err_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_res_2027_);
v_pos_2172_ = lean_ctor_get(v___x_2046_, 0);
v_err_2173_ = lean_ctor_get(v___x_2046_, 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2046_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_err_2173_);
lean_inc(v_pos_2172_);
lean_dec(v___x_2046_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_pos_2172_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_err_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2027_);
goto v___jp_2031_;
}
v___jp_2031_:
{
lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2032_ = lean_box(0);
if (v_isShared_2030_ == 0)
{
lean_ctor_set_tag(v___x_2029_, 1);
lean_ctor_set(v___x_2029_, 1, v___x_2032_);
v___x_2034_ = v___x_2029_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_pos_2026_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v_pos_2186_; lean_object* v_err_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
v_pos_2186_ = lean_ctor_get(v___x_2025_, 0);
v_err_2187_ = lean_ctor_get(v___x_2025_, 1);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2025_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_err_2187_);
lean_inc(v_pos_2186_);
lean_dec(v___x_2025_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_pos_2186_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_err_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
v___jp_1887_:
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1892_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1892_, 0, v_id_1888_);
lean_ctor_set(v___x_1892_, 1, v_message_1890_);
lean_ctor_set(v___x_1892_, 2, v_data_x3f_1891_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3, v_code_1889_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 1, v___x_1892_);
lean_ctor_set(v___x_1875_, 0, v___x_1886_);
v___x_1894_ = v___x_1875_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
v___jp_1896_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1));
v___x_1898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1886_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
return v___x_1898_;
}
v___jp_1899_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v_a_1900_);
v___x_1902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1886_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
return v___x_1902_;
}
v___jp_1903_:
{
lean_object* v___x_1904_; 
v___x_1904_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_1900_ = v___x_1904_;
goto v___jp_1899_;
}
}
}
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
lean_dec(v_res_1873_);
lean_dec_ref(v_input_1834_);
v___x_2199_ = lean_box(0);
if (v_isShared_1876_ == 0)
{
lean_ctor_set_tag(v___x_1875_, 1);
lean_ctor_set(v___x_1875_, 1, v___x_2199_);
v___x_2201_ = v___x_1875_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_pos_1872_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
else
{
lean_object* v_pos_2204_; lean_object* v_err_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec_ref(v_input_1834_);
v_pos_2204_ = lean_ctor_get(v___x_1871_, 0);
v_err_2205_ = lean_ctor_get(v___x_1871_, 1);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_1871_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_err_2205_);
lean_inc(v_pos_2204_);
lean_dec(v___x_1871_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_pos_2204_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_err_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec_ref(v_input_1834_);
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2218_, 0, v_a_1835_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
return v___x_2218_;
}
v___jp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = lean_string_utf8_next_fast(v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___y_1837_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1840_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_pos_1842_; lean_object* v_res_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
v_pos_1842_ = lean_ctor_get(v___x_1841_, 0);
v_res_1843_ = lean_ctor_get(v___x_1841_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1845_ = v___x_1841_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_res_1843_);
lean_inc(v_pos_1842_);
lean_dec(v___x_1841_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_res_1843_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v___x_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_pos_1842_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
else
{
lean_object* v_pos_1852_; lean_object* v_err_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
v_pos_1852_ = lean_ctor_get(v___x_1841_, 0);
v_err_1853_ = lean_ctor_get(v___x_1841_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1841_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_err_1853_);
lean_inc(v_pos_1852_);
lean_dec(v___x_1841_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_pos_1852_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_err_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object* v_input_2219_){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_inc_ref(v_input_2219_);
v___x_2220_ = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser), 2, 1);
lean_closure_set(v___x_2220_, 0, v_input_2219_);
v___x_2221_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2220_, v_input_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx(uint8_t v_x_2222_){
_start:
{
if (v_x_2222_ == 0)
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_unsigned_to_nat(0u);
return v___x_2223_;
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_unsigned_to_nat(1u);
return v___x_2224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___boxed(lean_object* v_x_2225_){
_start:
{
uint8_t v_x_boxed_2226_; lean_object* v_res_2227_; 
v_x_boxed_2226_ = lean_unbox(v_x_2225_);
v_res_2227_ = l_Lean_JsonRpc_MessageDirection_ctorIdx(v_x_boxed_2226_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object* v_k_2228_){
_start:
{
lean_inc(v_k_2228_);
return v_k_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object* v_k_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(v_k_2229_);
lean_dec(v_k_2229_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object* v_motive_2231_, lean_object* v_ctorIdx_2232_, uint8_t v_t_2233_, lean_object* v_h_2234_, lean_object* v_k_2235_){
_start:
{
lean_inc(v_k_2235_);
return v_k_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object* v_motive_2236_, lean_object* v_ctorIdx_2237_, lean_object* v_t_2238_, lean_object* v_h_2239_, lean_object* v_k_2240_){
_start:
{
uint8_t v_t_boxed_2241_; lean_object* v_res_2242_; 
v_t_boxed_2241_ = lean_unbox(v_t_2238_);
v_res_2242_ = l_Lean_JsonRpc_MessageDirection_ctorElim(v_motive_2236_, v_ctorIdx_2237_, v_t_boxed_2241_, v_h_2239_, v_k_2240_);
lean_dec(v_k_2240_);
lean_dec(v_ctorIdx_2237_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object* v_clientToServer_2243_){
_start:
{
lean_inc(v_clientToServer_2243_);
return v_clientToServer_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object* v_clientToServer_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(v_clientToServer_2244_);
lean_dec(v_clientToServer_2244_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object* v_motive_2246_, uint8_t v_t_2247_, lean_object* v_h_2248_, lean_object* v_clientToServer_2249_){
_start:
{
lean_inc(v_clientToServer_2249_);
return v_clientToServer_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object* v_motive_2250_, lean_object* v_t_2251_, lean_object* v_h_2252_, lean_object* v_clientToServer_2253_){
_start:
{
uint8_t v_t_boxed_2254_; lean_object* v_res_2255_; 
v_t_boxed_2254_ = lean_unbox(v_t_2251_);
v_res_2255_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(v_motive_2250_, v_t_boxed_2254_, v_h_2252_, v_clientToServer_2253_);
lean_dec(v_clientToServer_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object* v_serverToClient_2256_){
_start:
{
lean_inc(v_serverToClient_2256_);
return v_serverToClient_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object* v_serverToClient_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(v_serverToClient_2257_);
lean_dec(v_serverToClient_2257_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object* v_motive_2259_, uint8_t v_t_2260_, lean_object* v_h_2261_, lean_object* v_serverToClient_2262_){
_start:
{
lean_inc(v_serverToClient_2262_);
return v_serverToClient_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object* v_motive_2263_, lean_object* v_t_2264_, lean_object* v_h_2265_, lean_object* v_serverToClient_2266_){
_start:
{
uint8_t v_t_boxed_2267_; lean_object* v_res_2268_; 
v_t_boxed_2267_ = lean_unbox(v_t_2264_);
v_res_2268_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(v_motive_2263_, v_t_boxed_2267_, v_h_2265_, v_serverToClient_2266_);
lean_dec(v_serverToClient_2266_);
return v_res_2268_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default(void){
_start:
{
uint8_t v___x_2269_; 
v___x_2269_ = 0;
return v___x_2269_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection(void){
_start:
{
uint8_t v___x_2270_; 
v___x_2270_ = 0;
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object* v_json_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Json_getTag_x3f(v_json_2285_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v___x_2287_; 
v___x_2287_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1));
return v___x_2287_;
}
else
{
lean_object* v_val_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; 
v_val_2288_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_val_2288_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2289_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2));
v___x_2290_ = lean_string_dec_eq(v_val_2288_, v___x_2289_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3));
v___x_2292_ = lean_string_dec_eq(v_val_2288_, v___x_2291_);
lean_dec(v_val_2288_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; 
v___x_2293_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5));
return v___x_2293_;
}
else
{
lean_object* v___x_2294_; 
v___x_2294_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6));
return v___x_2294_;
}
}
else
{
lean_object* v___x_2295_; 
lean_dec(v_val_2288_);
v___x_2295_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7));
return v___x_2295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t v_x_2302_){
_start:
{
if (v_x_2302_ == 0)
{
lean_object* v___x_2303_; 
v___x_2303_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0));
return v___x_2303_;
}
else
{
lean_object* v___x_2304_; 
v___x_2304_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1));
return v___x_2304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object* v_x_2305_){
_start:
{
uint8_t v_x_44__boxed_2306_; lean_object* v_res_2307_; 
v_x_44__boxed_2306_ = lean_unbox(v_x_2305_);
v_res_2307_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_x_44__boxed_2306_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx(uint8_t v_x_2310_){
_start:
{
switch(v_x_2310_)
{
case 0:
{
lean_object* v___x_2311_; 
v___x_2311_ = lean_unsigned_to_nat(0u);
return v___x_2311_;
}
case 1:
{
lean_object* v___x_2312_; 
v___x_2312_ = lean_unsigned_to_nat(1u);
return v___x_2312_;
}
case 2:
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_unsigned_to_nat(2u);
return v___x_2313_;
}
default: 
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_unsigned_to_nat(3u);
return v___x_2314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___boxed(lean_object* v_x_2315_){
_start:
{
uint8_t v_x_boxed_2316_; lean_object* v_res_2317_; 
v_x_boxed_2316_ = lean_unbox(v_x_2315_);
v_res_2317_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_boxed_2316_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object* v_k_2318_){
_start:
{
lean_inc(v_k_2318_);
return v_k_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object* v_k_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_JsonRpc_MessageKind_ctorElim___redArg(v_k_2319_);
lean_dec(v_k_2319_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object* v_motive_2321_, lean_object* v_ctorIdx_2322_, uint8_t v_t_2323_, lean_object* v_h_2324_, lean_object* v_k_2325_){
_start:
{
lean_inc(v_k_2325_);
return v_k_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object* v_motive_2326_, lean_object* v_ctorIdx_2327_, lean_object* v_t_2328_, lean_object* v_h_2329_, lean_object* v_k_2330_){
_start:
{
uint8_t v_t_boxed_2331_; lean_object* v_res_2332_; 
v_t_boxed_2331_ = lean_unbox(v_t_2328_);
v_res_2332_ = l_Lean_JsonRpc_MessageKind_ctorElim(v_motive_2326_, v_ctorIdx_2327_, v_t_boxed_2331_, v_h_2329_, v_k_2330_);
lean_dec(v_k_2330_);
lean_dec(v_ctorIdx_2327_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object* v_request_2333_){
_start:
{
lean_inc(v_request_2333_);
return v_request_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object* v_request_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_JsonRpc_MessageKind_request_elim___redArg(v_request_2334_);
lean_dec(v_request_2334_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object* v_motive_2336_, uint8_t v_t_2337_, lean_object* v_h_2338_, lean_object* v_request_2339_){
_start:
{
lean_inc(v_request_2339_);
return v_request_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object* v_motive_2340_, lean_object* v_t_2341_, lean_object* v_h_2342_, lean_object* v_request_2343_){
_start:
{
uint8_t v_t_boxed_2344_; lean_object* v_res_2345_; 
v_t_boxed_2344_ = lean_unbox(v_t_2341_);
v_res_2345_ = l_Lean_JsonRpc_MessageKind_request_elim(v_motive_2340_, v_t_boxed_2344_, v_h_2342_, v_request_2343_);
lean_dec(v_request_2343_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object* v_notification_2346_){
_start:
{
lean_inc(v_notification_2346_);
return v_notification_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object* v_notification_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_JsonRpc_MessageKind_notification_elim___redArg(v_notification_2347_);
lean_dec(v_notification_2347_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object* v_motive_2349_, uint8_t v_t_2350_, lean_object* v_h_2351_, lean_object* v_notification_2352_){
_start:
{
lean_inc(v_notification_2352_);
return v_notification_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object* v_motive_2353_, lean_object* v_t_2354_, lean_object* v_h_2355_, lean_object* v_notification_2356_){
_start:
{
uint8_t v_t_boxed_2357_; lean_object* v_res_2358_; 
v_t_boxed_2357_ = lean_unbox(v_t_2354_);
v_res_2358_ = l_Lean_JsonRpc_MessageKind_notification_elim(v_motive_2353_, v_t_boxed_2357_, v_h_2355_, v_notification_2356_);
lean_dec(v_notification_2356_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object* v_response_2359_){
_start:
{
lean_inc(v_response_2359_);
return v_response_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object* v_response_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_JsonRpc_MessageKind_response_elim___redArg(v_response_2360_);
lean_dec(v_response_2360_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object* v_motive_2362_, uint8_t v_t_2363_, lean_object* v_h_2364_, lean_object* v_response_2365_){
_start:
{
lean_inc(v_response_2365_);
return v_response_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object* v_motive_2366_, lean_object* v_t_2367_, lean_object* v_h_2368_, lean_object* v_response_2369_){
_start:
{
uint8_t v_t_boxed_2370_; lean_object* v_res_2371_; 
v_t_boxed_2370_ = lean_unbox(v_t_2367_);
v_res_2371_ = l_Lean_JsonRpc_MessageKind_response_elim(v_motive_2366_, v_t_boxed_2370_, v_h_2368_, v_response_2369_);
lean_dec(v_response_2369_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object* v_responseError_2372_){
_start:
{
lean_inc(v_responseError_2372_);
return v_responseError_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object* v_responseError_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(v_responseError_2373_);
lean_dec(v_responseError_2373_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object* v_motive_2375_, uint8_t v_t_2376_, lean_object* v_h_2377_, lean_object* v_responseError_2378_){
_start:
{
lean_inc(v_responseError_2378_);
return v_responseError_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object* v_motive_2379_, lean_object* v_t_2380_, lean_object* v_h_2381_, lean_object* v_responseError_2382_){
_start:
{
uint8_t v_t_boxed_2383_; lean_object* v_res_2384_; 
v_t_boxed_2383_ = lean_unbox(v_t_2380_);
v_res_2384_ = l_Lean_JsonRpc_MessageKind_responseError_elim(v_motive_2379_, v_t_boxed_2383_, v_h_2381_, v_responseError_2382_);
lean_dec(v_responseError_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object* v_json_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_Json_getTag_x3f(v_json_2405_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v___x_2407_; 
v___x_2407_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0));
return v___x_2407_;
}
else
{
lean_object* v_val_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v_val_2408_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_val_2408_);
lean_dec_ref_known(v___x_2406_, 1);
v___x_2409_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1));
v___x_2410_ = lean_string_dec_eq(v_val_2408_, v___x_2409_);
if (v___x_2410_ == 0)
{
lean_object* v___x_2411_; uint8_t v___x_2412_; 
v___x_2411_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2));
v___x_2412_ = lean_string_dec_eq(v_val_2408_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2413_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3));
v___x_2414_ = lean_string_dec_eq(v_val_2408_, v___x_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2415_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4));
v___x_2416_ = lean_string_dec_eq(v_val_2408_, v___x_2415_);
lean_dec(v_val_2408_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; 
v___x_2417_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5));
return v___x_2417_;
}
else
{
lean_object* v___x_2418_; 
v___x_2418_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6));
return v___x_2418_;
}
}
else
{
lean_object* v___x_2419_; 
lean_dec(v_val_2408_);
v___x_2419_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7));
return v___x_2419_;
}
}
else
{
lean_object* v___x_2420_; 
lean_dec(v_val_2408_);
v___x_2420_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8));
return v___x_2420_;
}
}
else
{
lean_object* v___x_2421_; 
lean_dec(v_val_2408_);
v___x_2421_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9));
return v___x_2421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t v_x_2432_){
_start:
{
switch(v_x_2432_)
{
case 0:
{
lean_object* v___x_2433_; 
v___x_2433_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0));
return v___x_2433_;
}
case 1:
{
lean_object* v___x_2434_; 
v___x_2434_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1));
return v___x_2434_;
}
case 2:
{
lean_object* v___x_2435_; 
v___x_2435_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2));
return v___x_2435_;
}
default: 
{
lean_object* v___x_2436_; 
v___x_2436_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3));
return v___x_2436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object* v_x_2437_){
_start:
{
uint8_t v_x_84__boxed_2438_; lean_object* v_res_2439_; 
v_x_84__boxed_2438_ = lean_unbox(v_x_2437_);
v_res_2439_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_x_84__boxed_2438_);
return v_res_2439_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object* v_x_2442_){
_start:
{
switch(lean_obj_tag(v_x_2442_))
{
case 0:
{
uint8_t v___x_2443_; 
v___x_2443_ = 0;
return v___x_2443_;
}
case 1:
{
uint8_t v___x_2444_; 
v___x_2444_ = 1;
return v___x_2444_;
}
case 2:
{
uint8_t v___x_2445_; 
v___x_2445_ = 2;
return v___x_2445_;
}
default: 
{
uint8_t v___x_2446_; 
v___x_2446_ = 3;
return v___x_2446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object* v_x_2447_){
_start:
{
uint8_t v_res_2448_; lean_object* v_r_2449_; 
v_res_2448_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_x_2447_);
lean_dec_ref(v_x_2447_);
v_r_2449_ = lean_box(v_res_2448_);
return v_r_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(lean_object* v_j_2450_, lean_object* v_k_2451_){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = l_Lean_Json_getObjValD(v_j_2450_, v_k_2451_);
v___x_2453_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2452_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0___boxed(lean_object* v_j_2454_, lean_object* v_k_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_j_2454_, v_k_2455_);
lean_dec_ref(v_k_2455_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage(lean_object* v_h_2459_, lean_object* v_nBytes_2460_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Lean_IO_FS_Stream_readJson(v_h_2459_, v_nBytes_2460_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2582_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2465_ = v___x_2462_;
v_isShared_2466_ = v_isSharedCheck_2582_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2462_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2582_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___y_2468_; uint8_t v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v_a_2482_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_a_2463_);
v___x_2494_ = l_Lean_Json_getObjVal_x3f(v_a_2463_, v___x_2493_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; 
lean_del_object(v___x_2465_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v_a_2482_ = v_a_2495_;
goto v___jp_2481_;
}
else
{
lean_object* v_a_2496_; 
v_a_2496_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2494_, 1);
if (lean_obj_tag(v_a_2496_) == 3)
{
lean_object* v_s_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v_s_2497_ = lean_ctor_get(v_a_2496_, 0);
lean_inc_ref(v_s_2497_);
lean_dec_ref_known(v_a_2496_, 1);
v___x_2498_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_2499_ = lean_string_dec_eq(v_s_2497_, v___x_2498_);
lean_dec_ref(v_s_2497_);
if (v___x_2499_ == 0)
{
lean_del_object(v___x_2465_);
goto v___jp_2491_;
}
else
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_a_2463_);
v___x_2501_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_2463_, v___x_2500_);
if (lean_obj_tag(v___x_2501_) == 0)
{
goto v___jp_2530_;
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_a_2557_ = lean_ctor_get(v___x_2501_, 0);
v___x_2558_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2463_);
v___x_2559_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2463_, v___x_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_dec_ref_known(v___x_2559_, 1);
goto v___jp_2530_;
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2581_; 
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2501_, 1);
lean_del_object(v___x_2465_);
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2581_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2581_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___y_2565_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2571_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2463_, v___x_2570_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2572_; 
lean_dec_ref_known(v___x_2571_, 1);
v___x_2572_ = lean_box(0);
v___y_2565_ = v___x_2572_;
goto v___jp_2564_;
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
v_a_2573_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2571_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2571_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
v___y_2565_ = v___x_2578_;
goto v___jp_2564_;
}
}
}
v___jp_2564_:
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2566_, 0, v_a_2557_);
lean_ctor_set(v___x_2566_, 1, v_a_2560_);
lean_ctor_set(v___x_2566_, 2, v___y_2565_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2566_);
v___x_2568_ = v___x_2562_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
v___jp_2502_:
{
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2503_; 
lean_del_object(v___x_2465_);
v_a_2503_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2501_, 1);
v_a_2482_ = v_a_2503_;
goto v___jp_2481_;
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v_a_2504_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2501_, 1);
v___x_2505_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
lean_inc(v_a_2463_);
v___x_2506_ = l_Lean_Json_getObjVal_x3f(v_a_2463_, v___x_2505_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; 
lean_dec(v_a_2504_);
lean_del_object(v___x_2465_);
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v_a_2482_ = v_a_2507_;
goto v___jp_2481_;
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v_a_2508_ = lean_ctor_get(v___x_2506_, 0);
lean_inc_n(v_a_2508_, 2);
lean_dec_ref_known(v___x_2506_, 1);
v___x_2509_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_2510_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_2508_, v___x_2509_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; 
lean_dec(v_a_2508_);
lean_dec(v_a_2504_);
lean_del_object(v___x_2465_);
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v___x_2510_, 1);
v_a_2482_ = v_a_2511_;
goto v___jp_2481_;
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_a_2512_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2510_, 1);
v___x_2513_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_2508_);
v___x_2514_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2508_, v___x_2513_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; 
lean_dec(v_a_2512_);
lean_dec(v_a_2508_);
lean_dec(v_a_2504_);
lean_del_object(v___x_2465_);
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v_a_2482_ = v_a_2515_;
goto v___jp_2481_;
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_dec(v_a_2463_);
v_a_2516_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2517_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2518_ = l_Lean_Json_getObjVal_x3f(v_a_2508_, v___x_2517_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v___x_2519_; uint8_t v___x_2520_; 
lean_dec_ref_known(v___x_2518_, 1);
v___x_2519_ = lean_box(0);
v___x_2520_ = lean_unbox(v_a_2512_);
lean_dec(v_a_2512_);
v___y_2468_ = v_a_2516_;
v___y_2469_ = v___x_2520_;
v___y_2470_ = v_a_2504_;
v___y_2471_ = v___x_2519_;
goto v___jp_2467_;
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2529_; 
v_a_2521_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2523_ = v___x_2518_;
v_isShared_2524_ = v_isSharedCheck_2529_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2518_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2529_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
uint8_t v___x_2527_; 
v___x_2527_ = lean_unbox(v_a_2512_);
lean_dec(v_a_2512_);
v___y_2468_ = v_a_2516_;
v___y_2469_ = v___x_2527_;
v___y_2470_ = v_a_2504_;
v___y_2471_ = v___x_2526_;
goto v___jp_2467_;
}
}
}
}
}
}
}
}
v___jp_2530_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2463_);
v___x_2532_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2463_, v___x_2531_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_dec_ref_known(v___x_2532_, 1);
if (lean_obj_tag(v___x_2501_) == 0)
{
goto v___jp_2502_;
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v_a_2533_ = lean_ctor_get(v___x_2501_, 0);
v___x_2534_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_2463_);
v___x_2535_ = l_Lean_Json_getObjVal_x3f(v_a_2463_, v___x_2534_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_dec_ref_known(v___x_2535_, 1);
goto v___jp_2502_;
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2544_; 
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2501_, 1);
lean_del_object(v___x_2465_);
lean_dec(v_a_2463_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2540_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2540_, 0, v_a_2533_);
lean_ctor_set(v___x_2540_, 1, v_a_2536_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set_tag(v___x_2538_, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2540_);
v___x_2542_ = v___x_2538_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec_ref(v___x_2501_);
lean_del_object(v___x_2465_);
v_a_2545_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2546_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2547_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2463_, v___x_2546_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v___x_2548_; 
lean_dec_ref_known(v___x_2547_, 1);
v___x_2548_ = lean_box(0);
v___y_2477_ = v_a_2545_;
v___y_2478_ = v___x_2548_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_a_2549_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2547_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2547_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
v___y_2477_ = v_a_2545_;
v___y_2478_ = v___x_2554_;
goto v___jp_2476_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2496_);
lean_del_object(v___x_2465_);
goto v___jp_2491_;
}
}
v___jp_2467_:
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2472_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2472_, 0, v___y_2470_);
lean_ctor_set(v___x_2472_, 1, v___y_2468_);
lean_ctor_set(v___x_2472_, 2, v___y_2471_);
lean_ctor_set_uint8(v___x_2472_, sizeof(void*)*3, v___y_2469_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2472_);
v___x_2474_ = v___x_2465_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
v___jp_2476_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___y_2477_);
lean_ctor_set(v___x_2479_, 1, v___y_2478_);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
v___jp_2481_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2483_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__0));
v___x_2484_ = l_Lean_Json_compress(v_a_2463_);
v___x_2485_ = lean_string_append(v___x_2483_, v___x_2484_);
lean_dec_ref(v___x_2484_);
v___x_2486_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__1));
v___x_2487_ = lean_string_append(v___x_2485_, v___x_2486_);
v___x_2488_ = lean_string_append(v___x_2487_, v_a_2482_);
lean_dec_ref(v_a_2482_);
v___x_2489_ = lean_mk_io_user_error(v___x_2488_);
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
return v___x_2490_;
}
v___jp_2491_:
{
lean_object* v___x_2492_; 
v___x_2492_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_2482_ = v___x_2492_;
goto v___jp_2481_;
}
}
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_a_2583_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2462_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2462_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage___boxed(lean_object* v_h_2591_, lean_object* v_nBytes_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_IO_FS_Stream_readMessage(v_h_2591_, v_nBytes_2592_);
lean_dec(v_nBytes_2592_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg(lean_object* v_h_2602_, lean_object* v_nBytes_2603_, lean_object* v_expectedMethod_2604_, lean_object* v_inst_2605_){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2608_ = l_Lean_IO_FS_Stream_readMessage(v_h_2602_, v_nBytes_2603_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2794_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2794_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2794_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
if (lean_obj_tag(v_a_2609_) == 0)
{
lean_object* v_id_2613_; lean_object* v_method_2614_; lean_object* v_params_x3f_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2654_; 
v_id_2613_ = lean_ctor_get(v_a_2609_, 0);
v_method_2614_ = lean_ctor_get(v_a_2609_, 1);
v_params_x3f_2615_ = lean_ctor_get(v_a_2609_, 2);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_a_2609_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2617_ = v_a_2609_;
v_isShared_2618_ = v_isSharedCheck_2654_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_params_x3f_2615_);
lean_inc(v_method_2614_);
lean_inc(v_id_2613_);
lean_dec(v_a_2609_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2654_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
uint8_t v___x_2619_; 
v___x_2619_ = lean_string_dec_eq(v_method_2614_, v_expectedMethod_2604_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
lean_del_object(v___x_2617_);
lean_dec(v_params_x3f_2615_);
lean_dec(v_id_2613_);
lean_dec_ref(v_inst_2605_);
v___x_2620_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2621_ = lean_string_append(v___x_2620_, v_expectedMethod_2604_);
lean_dec_ref(v_expectedMethod_2604_);
v___x_2622_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2623_ = lean_string_append(v___x_2621_, v___x_2622_);
v___x_2624_ = lean_string_append(v___x_2623_, v_method_2614_);
lean_dec_ref(v_method_2614_);
v___x_2625_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2626_ = lean_string_append(v___x_2624_, v___x_2625_);
v___x_2627_ = lean_mk_io_user_error(v___x_2626_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 1);
lean_ctor_set(v___x_2611_, 0, v___x_2627_);
v___x_2629_ = v___x_2611_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec_ref(v_method_2614_);
v___x_2631_ = l_Lean_Option_toJson___redArg(v___x_2607_, v_params_x3f_2615_);
lean_inc(v___x_2631_);
v___x_2632_ = lean_apply_1(v_inst_2605_, v___x_2631_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
lean_del_object(v___x_2617_);
lean_dec(v_id_2613_);
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2635_ = l_Lean_Json_compress(v___x_2631_);
v___x_2636_ = lean_string_append(v___x_2634_, v___x_2635_);
lean_dec_ref(v___x_2635_);
v___x_2637_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2638_ = lean_string_append(v___x_2636_, v___x_2637_);
v___x_2639_ = lean_string_append(v___x_2638_, v_expectedMethod_2604_);
lean_dec_ref(v_expectedMethod_2604_);
v___x_2640_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2641_ = lean_string_append(v___x_2639_, v___x_2640_);
v___x_2642_ = lean_string_append(v___x_2641_, v_a_2633_);
lean_dec(v_a_2633_);
v___x_2643_ = lean_mk_io_user_error(v___x_2642_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 1);
lean_ctor_set(v___x_2611_, 0, v___x_2643_);
v___x_2645_ = v___x_2611_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; 
lean_dec(v___x_2631_);
v_a_2647_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2632_, 1);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 2, v_a_2647_);
lean_ctor_set(v___x_2617_, 1, v_expectedMethod_2604_);
v___x_2649_ = v___x_2617_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_id_2613_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_expectedMethod_2604_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_a_2647_);
v___x_2649_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2651_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2649_);
v___x_2651_ = v___x_2611_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___y_2658_; 
lean_dec_ref(v_inst_2605_);
lean_dec_ref(v_expectedMethod_2604_);
v___x_2655_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__6));
v___x_2656_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2609_))
{
case 0:
{
lean_object* v_id_2669_; lean_object* v_method_2670_; lean_object* v_params_x3f_2671_; lean_object* v___x_2672_; lean_object* v___y_2674_; 
v_id_2669_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_id_2669_);
v_method_2670_ = lean_ctor_get(v_a_2609_, 1);
lean_inc_ref(v_method_2670_);
v_params_x3f_2671_ = lean_ctor_get(v_a_2609_, 2);
lean_inc(v_params_x3f_2671_);
lean_dec_ref_known(v_a_2609_, 3);
v___x_2672_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2669_) == 0)
{
lean_object* v_s_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
v_s_2685_ = lean_ctor_get(v_id_2669_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_id_2669_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v_id_2669_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_s_2685_);
lean_dec(v_id_2669_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set_tag(v___x_2687_, 3);
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_s_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
v___y_2674_ = v___x_2690_;
goto v___jp_2673_;
}
}
}
else
{
lean_object* v_n_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
v_n_2693_ = lean_ctor_get(v_id_2669_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_id_2669_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v_id_2669_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_n_2693_);
lean_dec(v_id_2669_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
lean_ctor_set_tag(v___x_2695_, 2);
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_n_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
v___y_2674_ = v___x_2698_;
goto v___jp_2673_;
}
}
}
v___jp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2672_);
lean_ctor_set(v___x_2675_, 1, v___y_2674_);
v___x_2676_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_method_2670_);
v___x_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = lean_box(0);
v___x_2680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2675_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
v___x_2682_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2683_ = l_Lean_Json_opt___redArg(v___x_2607_, v___x_2682_, v_params_x3f_2671_);
v___x_2684_ = l_List_appendTR___redArg(v___x_2681_, v___x_2683_);
v___y_2658_ = v___x_2684_;
goto v___jp_2657_;
}
}
case 1:
{
lean_object* v_method_2701_; lean_object* v_params_x3f_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_method_2701_ = lean_ctor_get(v_a_2609_, 0);
lean_inc_ref(v_method_2701_);
v_params_x3f_2702_ = lean_ctor_get(v_a_2609_, 1);
lean_inc(v_params_x3f_2702_);
lean_dec_ref_known(v_a_2609_, 2);
v___x_2703_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2704_, 0, v_method_2701_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2707_ = l_Lean_Json_opt___redArg(v___x_2607_, v___x_2706_, v_params_x3f_2702_);
v___x_2708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2705_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___y_2658_ = v___x_2708_;
goto v___jp_2657_;
}
case 2:
{
lean_object* v_id_2709_; lean_object* v_result_2710_; lean_object* v___x_2711_; lean_object* v___y_2713_; 
v_id_2709_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_id_2709_);
v_result_2710_ = lean_ctor_get(v_a_2609_, 1);
lean_inc(v_result_2710_);
lean_dec_ref_known(v_a_2609_, 2);
v___x_2711_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2709_) == 0)
{
lean_object* v_s_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
v_s_2720_ = lean_ctor_get(v_id_2709_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_id_2709_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v_id_2709_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_s_2720_);
lean_dec(v_id_2709_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set_tag(v___x_2722_, 3);
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_s_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
v___y_2713_ = v___x_2725_;
goto v___jp_2712_;
}
}
}
else
{
lean_object* v_n_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
v_n_2728_ = lean_ctor_get(v_id_2709_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_id_2709_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v_id_2709_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_n_2728_);
lean_dec(v_id_2709_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set_tag(v___x_2730_, 2);
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_n_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
v___y_2713_ = v___x_2733_;
goto v___jp_2712_;
}
}
}
v___jp_2712_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2711_);
lean_ctor_set(v___x_2714_, 1, v___y_2713_);
v___x_2715_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v_result_2710_);
v___x_2717_ = lean_box(0);
v___x_2718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2716_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2714_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___y_2658_ = v___x_2719_;
goto v___jp_2657_;
}
}
default: 
{
lean_object* v_id_2736_; uint8_t v_code_2737_; lean_object* v_message_2738_; lean_object* v_data_x3f_2739_; lean_object* v___x_2740_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___x_2760_; lean_object* v___y_2762_; 
v_id_2736_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_id_2736_);
v_code_2737_ = lean_ctor_get_uint8(v_a_2609_, sizeof(void*)*3);
v_message_2738_ = lean_ctor_get(v_a_2609_, 1);
lean_inc_ref(v_message_2738_);
v_data_x3f_2739_ = lean_ctor_get(v_a_2609_, 2);
lean_inc(v_data_x3f_2739_);
lean_dec_ref_known(v_a_2609_, 3);
v___x_2740_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2760_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2736_) == 0)
{
lean_object* v_s_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
v_s_2778_ = lean_ctor_get(v_id_2736_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_id_2736_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v_id_2736_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_s_2778_);
lean_dec(v_id_2736_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set_tag(v___x_2780_, 3);
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_s_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
v___y_2762_ = v___x_2783_;
goto v___jp_2761_;
}
}
}
else
{
lean_object* v_n_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
v_n_2786_ = lean_ctor_get(v_id_2736_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_id_2736_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v_id_2736_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_n_2786_);
lean_dec(v_id_2736_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
lean_ctor_set_tag(v___x_2788_, 2);
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_n_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
v___y_2762_ = v___x_2791_;
goto v___jp_2761_;
}
}
}
v___jp_2741_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_inc(v___y_2745_);
lean_inc_ref(v___y_2743_);
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___y_2743_);
lean_ctor_set(v___x_2746_, 1, v___y_2745_);
v___x_2747_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2748_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2748_, 0, v_message_2738_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2746_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2754_ = l_Lean_Json_opt___redArg(v___x_2740_, v___x_2753_, v_data_x3f_2739_);
v___x_2755_ = l_List_appendTR___redArg(v___x_2752_, v___x_2754_);
v___x_2756_ = l_Lean_Json_mkObj(v___x_2755_);
lean_dec(v___x_2755_);
lean_inc_ref(v___y_2744_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___y_2744_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
lean_ctor_set(v___x_2758_, 1, v___x_2750_);
v___x_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___y_2742_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___y_2658_ = v___x_2759_;
goto v___jp_2657_;
}
v___jp_2761_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2760_);
lean_ctor_set(v___x_2763_, 1, v___y_2762_);
v___x_2764_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2765_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2737_)
{
case 0:
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2766_;
goto v___jp_2741_;
}
case 1:
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2767_;
goto v___jp_2741_;
}
case 2:
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2768_;
goto v___jp_2741_;
}
case 3:
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2769_;
goto v___jp_2741_;
}
case 4:
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2770_;
goto v___jp_2741_;
}
case 5:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2771_;
goto v___jp_2741_;
}
case 6:
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2772_;
goto v___jp_2741_;
}
case 7:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2773_;
goto v___jp_2741_;
}
case 8:
{
lean_object* v___x_2774_; 
v___x_2774_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2774_;
goto v___jp_2741_;
}
case 9:
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2775_;
goto v___jp_2741_;
}
case 10:
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2776_;
goto v___jp_2741_;
}
default: 
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2742_ = v___x_2763_;
v___y_2743_ = v___x_2765_;
v___y_2744_ = v___x_2764_;
v___y_2745_ = v___x_2777_;
goto v___jp_2741_;
}
}
}
}
}
v___jp_2657_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2656_);
lean_ctor_set(v___x_2659_, 1, v___y_2658_);
v___x_2660_ = l_Lean_Json_mkObj(v___x_2659_);
lean_dec_ref_known(v___x_2659_, 2);
v___x_2661_ = l_Lean_Json_compress(v___x_2660_);
v___x_2662_ = lean_string_append(v___x_2655_, v___x_2661_);
lean_dec_ref(v___x_2661_);
v___x_2663_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2664_ = lean_string_append(v___x_2662_, v___x_2663_);
v___x_2665_ = lean_mk_io_user_error(v___x_2664_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 1);
lean_ctor_set(v___x_2611_, 0, v___x_2665_);
v___x_2667_ = v___x_2611_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec_ref(v_inst_2605_);
lean_dec_ref(v_expectedMethod_2604_);
v_a_2795_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2608_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2608_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* v_h_2803_, lean_object* v_nBytes_2804_, lean_object* v_expectedMethod_2805_, lean_object* v_inst_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2803_, v_nBytes_2804_, v_expectedMethod_2805_, v_inst_2806_);
lean_dec(v_nBytes_2804_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs(lean_object* v_h_2809_, lean_object* v_nBytes_2810_, lean_object* v_expectedMethod_2811_, lean_object* v_00_u03b1_2812_, lean_object* v_inst_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2809_, v_nBytes_2810_, v_expectedMethod_2811_, v_inst_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___boxed(lean_object* v_h_2816_, lean_object* v_nBytes_2817_, lean_object* v_expectedMethod_2818_, lean_object* v_00_u03b1_2819_, lean_object* v_inst_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_IO_FS_Stream_readRequestAs(v_h_2816_, v_nBytes_2817_, v_expectedMethod_2818_, v_00_u03b1_2819_, v_inst_2820_);
lean_dec(v_nBytes_2817_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg(lean_object* v_h_2824_, lean_object* v_nBytes_2825_, lean_object* v_expectedMethod_2826_, lean_object* v_inst_2827_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2830_ = l_Lean_IO_FS_Stream_readMessage(v_h_2824_, v_nBytes_2825_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_3015_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_2833_ = v___x_2830_;
v_isShared_2834_ = v_isSharedCheck_3015_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2830_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_3015_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
if (lean_obj_tag(v_a_2831_) == 1)
{
lean_object* v_method_2835_; lean_object* v_params_x3f_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2875_; 
v_method_2835_ = lean_ctor_get(v_a_2831_, 0);
v_params_x3f_2836_ = lean_ctor_get(v_a_2831_, 1);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_a_2831_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2838_ = v_a_2831_;
v_isShared_2839_ = v_isSharedCheck_2875_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_params_x3f_2836_);
lean_inc(v_method_2835_);
lean_dec(v_a_2831_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2875_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
uint8_t v___x_2840_; 
v___x_2840_ = lean_string_dec_eq(v_method_2835_, v_expectedMethod_2826_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
lean_del_object(v___x_2838_);
lean_dec(v_params_x3f_2836_);
lean_dec_ref(v_inst_2827_);
v___x_2841_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2842_ = lean_string_append(v___x_2841_, v_expectedMethod_2826_);
lean_dec_ref(v_expectedMethod_2826_);
v___x_2843_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2844_ = lean_string_append(v___x_2842_, v___x_2843_);
v___x_2845_ = lean_string_append(v___x_2844_, v_method_2835_);
lean_dec_ref(v_method_2835_);
v___x_2846_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2847_ = lean_string_append(v___x_2845_, v___x_2846_);
v___x_2848_ = lean_mk_io_user_error(v___x_2847_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 1);
lean_ctor_set(v___x_2833_, 0, v___x_2848_);
v___x_2850_ = v___x_2833_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
else
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec_ref(v_method_2835_);
v___x_2852_ = l_Lean_Option_toJson___redArg(v___x_2829_, v_params_x3f_2836_);
lean_inc(v___x_2852_);
v___x_2853_ = lean_apply_1(v_inst_2827_, v___x_2852_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
lean_del_object(v___x_2838_);
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v___x_2855_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2856_ = l_Lean_Json_compress(v___x_2852_);
v___x_2857_ = lean_string_append(v___x_2855_, v___x_2856_);
lean_dec_ref(v___x_2856_);
v___x_2858_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2859_ = lean_string_append(v___x_2857_, v___x_2858_);
v___x_2860_ = lean_string_append(v___x_2859_, v_expectedMethod_2826_);
lean_dec_ref(v_expectedMethod_2826_);
v___x_2861_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2862_ = lean_string_append(v___x_2860_, v___x_2861_);
v___x_2863_ = lean_string_append(v___x_2862_, v_a_2854_);
lean_dec(v_a_2854_);
v___x_2864_ = lean_mk_io_user_error(v___x_2863_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 1);
lean_ctor_set(v___x_2833_, 0, v___x_2864_);
v___x_2866_ = v___x_2833_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; 
lean_dec(v___x_2852_);
v_a_2868_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2853_, 1);
if (v_isShared_2839_ == 0)
{
lean_ctor_set_tag(v___x_2838_, 0);
lean_ctor_set(v___x_2838_, 1, v_a_2868_);
lean_ctor_set(v___x_2838_, 0, v_expectedMethod_2826_);
v___x_2870_ = v___x_2838_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_expectedMethod_2826_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_a_2868_);
v___x_2870_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2872_; 
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2870_);
v___x_2872_ = v___x_2833_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
}
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___y_2879_; 
lean_dec_ref(v_inst_2827_);
lean_dec_ref(v_expectedMethod_2826_);
v___x_2876_ = ((lean_object*)(l_Lean_IO_FS_Stream_readNotificationAs___redArg___closed__0));
v___x_2877_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2831_))
{
case 0:
{
lean_object* v_id_2890_; lean_object* v_method_2891_; lean_object* v_params_x3f_2892_; lean_object* v___x_2893_; lean_object* v___y_2895_; 
v_id_2890_ = lean_ctor_get(v_a_2831_, 0);
lean_inc(v_id_2890_);
v_method_2891_ = lean_ctor_get(v_a_2831_, 1);
lean_inc_ref(v_method_2891_);
v_params_x3f_2892_ = lean_ctor_get(v_a_2831_, 2);
lean_inc(v_params_x3f_2892_);
lean_dec_ref_known(v_a_2831_, 3);
v___x_2893_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2890_) == 0)
{
lean_object* v_s_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_s_2906_ = lean_ctor_get(v_id_2890_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_id_2890_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v_id_2890_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_s_2906_);
lean_dec(v_id_2890_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set_tag(v___x_2908_, 3);
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_s_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
v___y_2895_ = v___x_2911_;
goto v___jp_2894_;
}
}
}
else
{
lean_object* v_n_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
v_n_2914_ = lean_ctor_get(v_id_2890_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_id_2890_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v_id_2890_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_n_2914_);
lean_dec(v_id_2890_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
lean_ctor_set_tag(v___x_2916_, 2);
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_n_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
v___y_2895_ = v___x_2919_;
goto v___jp_2894_;
}
}
}
v___jp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2893_);
lean_ctor_set(v___x_2896_, 1, v___y_2895_);
v___x_2897_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2898_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2898_, 0, v_method_2891_);
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2897_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = lean_box(0);
v___x_2901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2896_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2904_ = l_Lean_Json_opt___redArg(v___x_2829_, v___x_2903_, v_params_x3f_2892_);
v___x_2905_ = l_List_appendTR___redArg(v___x_2902_, v___x_2904_);
v___y_2879_ = v___x_2905_;
goto v___jp_2878_;
}
}
case 1:
{
lean_object* v_method_2922_; lean_object* v_params_x3f_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v_method_2922_ = lean_ctor_get(v_a_2831_, 0);
lean_inc_ref(v_method_2922_);
v_params_x3f_2923_ = lean_ctor_get(v_a_2831_, 1);
lean_inc(v_params_x3f_2923_);
lean_dec_ref_known(v_a_2831_, 2);
v___x_2924_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2925_, 0, v_method_2922_);
v___x_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2928_ = l_Lean_Json_opt___redArg(v___x_2829_, v___x_2927_, v_params_x3f_2923_);
v___x_2929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2926_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
v___y_2879_ = v___x_2929_;
goto v___jp_2878_;
}
case 2:
{
lean_object* v_id_2930_; lean_object* v_result_2931_; lean_object* v___x_2932_; lean_object* v___y_2934_; 
v_id_2930_ = lean_ctor_get(v_a_2831_, 0);
lean_inc(v_id_2930_);
v_result_2931_ = lean_ctor_get(v_a_2831_, 1);
lean_inc(v_result_2931_);
lean_dec_ref_known(v_a_2831_, 2);
v___x_2932_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2930_) == 0)
{
lean_object* v_s_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
v_s_2941_ = lean_ctor_get(v_id_2930_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_id_2930_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v_id_2930_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_s_2941_);
lean_dec(v_id_2930_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set_tag(v___x_2943_, 3);
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_s_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
v___y_2934_ = v___x_2946_;
goto v___jp_2933_;
}
}
}
else
{
lean_object* v_n_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_n_2949_ = lean_ctor_get(v_id_2930_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_id_2930_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v_id_2930_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_n_2949_);
lean_dec(v_id_2930_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 2);
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_n_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
v___y_2934_ = v___x_2954_;
goto v___jp_2933_;
}
}
}
v___jp_2933_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2932_);
lean_ctor_set(v___x_2935_, 1, v___y_2934_);
v___x_2936_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v_result_2931_);
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2937_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2935_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___y_2879_ = v___x_2940_;
goto v___jp_2878_;
}
}
default: 
{
lean_object* v_id_2957_; uint8_t v_code_2958_; lean_object* v_message_2959_; lean_object* v_data_x3f_2960_; lean_object* v___x_2961_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___x_2981_; lean_object* v___y_2983_; 
v_id_2957_ = lean_ctor_get(v_a_2831_, 0);
lean_inc(v_id_2957_);
v_code_2958_ = lean_ctor_get_uint8(v_a_2831_, sizeof(void*)*3);
v_message_2959_ = lean_ctor_get(v_a_2831_, 1);
lean_inc_ref(v_message_2959_);
v_data_x3f_2960_ = lean_ctor_get(v_a_2831_, 2);
lean_inc(v_data_x3f_2960_);
lean_dec_ref_known(v_a_2831_, 3);
v___x_2961_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2981_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2957_) == 0)
{
lean_object* v_s_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_s_2999_ = lean_ctor_get(v_id_2957_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_id_2957_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v_id_2957_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_s_2999_);
lean_dec(v_id_2957_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set_tag(v___x_3001_, 3);
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_s_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
v___y_2983_ = v___x_3004_;
goto v___jp_2982_;
}
}
}
else
{
lean_object* v_n_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
v_n_3007_ = lean_ctor_get(v_id_2957_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_id_2957_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v_id_2957_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_n_3007_);
lean_dec(v_id_2957_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
lean_ctor_set_tag(v___x_3009_, 2);
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_n_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
v___y_2983_ = v___x_3012_;
goto v___jp_2982_;
}
}
}
v___jp_2962_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2964_);
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___y_2964_);
lean_ctor_set(v___x_2967_, 1, v___y_2966_);
v___x_2968_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2969_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2969_, 0, v_message_2959_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2968_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2970_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2967_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2975_ = l_Lean_Json_opt___redArg(v___x_2961_, v___x_2974_, v_data_x3f_2960_);
v___x_2976_ = l_List_appendTR___redArg(v___x_2973_, v___x_2975_);
v___x_2977_ = l_Lean_Json_mkObj(v___x_2976_);
lean_dec(v___x_2976_);
lean_inc_ref(v___y_2965_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___y_2965_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
lean_ctor_set(v___x_2979_, 1, v___x_2971_);
v___x_2980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___y_2963_);
lean_ctor_set(v___x_2980_, 1, v___x_2979_);
v___y_2879_ = v___x_2980_;
goto v___jp_2878_;
}
v___jp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2981_);
lean_ctor_set(v___x_2984_, 1, v___y_2983_);
v___x_2985_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2986_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2958_)
{
case 0:
{
lean_object* v___x_2987_; 
v___x_2987_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2987_;
goto v___jp_2962_;
}
case 1:
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2988_;
goto v___jp_2962_;
}
case 2:
{
lean_object* v___x_2989_; 
v___x_2989_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2989_;
goto v___jp_2962_;
}
case 3:
{
lean_object* v___x_2990_; 
v___x_2990_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2990_;
goto v___jp_2962_;
}
case 4:
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2991_;
goto v___jp_2962_;
}
case 5:
{
lean_object* v___x_2992_; 
v___x_2992_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2992_;
goto v___jp_2962_;
}
case 6:
{
lean_object* v___x_2993_; 
v___x_2993_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2993_;
goto v___jp_2962_;
}
case 7:
{
lean_object* v___x_2994_; 
v___x_2994_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2994_;
goto v___jp_2962_;
}
case 8:
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2995_;
goto v___jp_2962_;
}
case 9:
{
lean_object* v___x_2996_; 
v___x_2996_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2996_;
goto v___jp_2962_;
}
case 10:
{
lean_object* v___x_2997_; 
v___x_2997_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2997_;
goto v___jp_2962_;
}
default: 
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2963_ = v___x_2984_;
v___y_2964_ = v___x_2986_;
v___y_2965_ = v___x_2985_;
v___y_2966_ = v___x_2998_;
goto v___jp_2962_;
}
}
}
}
}
v___jp_2878_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2888_; 
v___x_2880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2877_);
lean_ctor_set(v___x_2880_, 1, v___y_2879_);
v___x_2881_ = l_Lean_Json_mkObj(v___x_2880_);
lean_dec_ref_known(v___x_2880_, 2);
v___x_2882_ = l_Lean_Json_compress(v___x_2881_);
v___x_2883_ = lean_string_append(v___x_2876_, v___x_2882_);
lean_dec_ref(v___x_2882_);
v___x_2884_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2885_ = lean_string_append(v___x_2883_, v___x_2884_);
v___x_2886_ = lean_mk_io_user_error(v___x_2885_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set_tag(v___x_2833_, 1);
lean_ctor_set(v___x_2833_, 0, v___x_2886_);
v___x_2888_ = v___x_2833_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec_ref(v_inst_2827_);
lean_dec_ref(v_expectedMethod_2826_);
v_a_3016_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2830_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2830_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* v_h_3024_, lean_object* v_nBytes_3025_, lean_object* v_expectedMethod_3026_, lean_object* v_inst_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3024_, v_nBytes_3025_, v_expectedMethod_3026_, v_inst_3027_);
lean_dec(v_nBytes_3025_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs(lean_object* v_h_3030_, lean_object* v_nBytes_3031_, lean_object* v_expectedMethod_3032_, lean_object* v_00_u03b1_3033_, lean_object* v_inst_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3030_, v_nBytes_3031_, v_expectedMethod_3032_, v_inst_3034_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___boxed(lean_object* v_h_3037_, lean_object* v_nBytes_3038_, lean_object* v_expectedMethod_3039_, lean_object* v_00_u03b1_3040_, lean_object* v_inst_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_IO_FS_Stream_readNotificationAs(v_h_3037_, v_nBytes_3038_, v_expectedMethod_3039_, v_00_u03b1_3040_, v_inst_3041_);
lean_dec(v_nBytes_3038_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg(lean_object* v_h_3048_, lean_object* v_nBytes_3049_, lean_object* v_expectedID_3050_, lean_object* v_inst_3051_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_Lean_IO_FS_Stream_readMessage(v_h_3048_, v_nBytes_3049_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3257_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3056_ = v___x_3053_;
v_isShared_3057_ = v_isSharedCheck_3257_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3053_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3257_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___y_3059_; lean_object* v___y_3060_; 
if (lean_obj_tag(v_a_3054_) == 2)
{
lean_object* v_id_3066_; lean_object* v_result_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3118_; 
v_id_3066_ = lean_ctor_get(v_a_3054_, 0);
v_result_3067_ = lean_ctor_get(v_a_3054_, 1);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_a_3054_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3069_ = v_a_3054_;
v_isShared_3070_ = v_isSharedCheck_3118_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_result_3067_);
lean_inc(v_id_3066_);
lean_dec(v_a_3054_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3118_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
uint8_t v___x_3071_; 
v___x_3071_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3066_, v_expectedID_3050_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; lean_object* v___y_3074_; 
lean_del_object(v___x_3069_);
lean_dec(v_result_3067_);
lean_dec_ref(v_inst_3051_);
v___x_3072_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__0));
switch(lean_obj_tag(v_expectedID_3050_))
{
case 0:
{
lean_object* v_s_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v_s_3084_ = lean_ctor_get(v_expectedID_3050_, 0);
lean_inc_ref(v_s_3084_);
lean_dec_ref_known(v_expectedID_3050_, 1);
v___x_3085_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3086_ = lean_string_append(v___x_3085_, v_s_3084_);
lean_dec_ref(v_s_3084_);
v___x_3087_ = lean_string_append(v___x_3086_, v___x_3085_);
v___y_3074_ = v___x_3087_;
goto v___jp_3073_;
}
case 1:
{
lean_object* v_n_3088_; lean_object* v___x_3089_; 
v_n_3088_ = lean_ctor_get(v_expectedID_3050_, 0);
lean_inc_ref(v_n_3088_);
lean_dec_ref_known(v_expectedID_3050_, 1);
v___x_3089_ = l_Lean_JsonNumber_toString(v_n_3088_);
v___y_3074_ = v___x_3089_;
goto v___jp_3073_;
}
default: 
{
lean_object* v___x_3090_; 
v___x_3090_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___y_3074_ = v___x_3090_;
goto v___jp_3073_;
}
}
v___jp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_string_append(v___x_3072_, v___y_3074_);
lean_dec_ref(v___y_3074_);
v___x_3076_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__1));
v___x_3077_ = lean_string_append(v___x_3075_, v___x_3076_);
if (lean_obj_tag(v_id_3066_) == 0)
{
lean_object* v_s_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v_s_3078_ = lean_ctor_get(v_id_3066_, 0);
lean_inc_ref(v_s_3078_);
lean_dec_ref_known(v_id_3066_, 1);
v___x_3079_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3080_ = lean_string_append(v___x_3079_, v_s_3078_);
lean_dec_ref(v_s_3078_);
v___x_3081_ = lean_string_append(v___x_3080_, v___x_3079_);
v___y_3059_ = v___x_3077_;
v___y_3060_ = v___x_3081_;
goto v___jp_3058_;
}
else
{
lean_object* v_n_3082_; lean_object* v___x_3083_; 
v_n_3082_ = lean_ctor_get(v_id_3066_, 0);
lean_inc_ref(v_n_3082_);
lean_dec_ref_known(v_id_3066_, 1);
v___x_3083_ = l_Lean_JsonNumber_toString(v_n_3082_);
v___y_3059_ = v___x_3077_;
v___y_3060_ = v___x_3083_;
goto v___jp_3058_;
}
}
}
else
{
lean_object* v___x_3091_; 
lean_dec(v_id_3066_);
lean_del_object(v___x_3056_);
lean_inc(v_result_3067_);
v___x_3091_ = lean_apply_1(v_inst_3051_, v_result_3067_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3106_; 
lean_del_object(v___x_3069_);
lean_dec(v_expectedID_3050_);
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3106_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3106_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3096_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__2));
v___x_3097_ = l_Lean_Json_compress(v_result_3067_);
v___x_3098_ = lean_string_append(v___x_3096_, v___x_3097_);
lean_dec_ref(v___x_3097_);
v___x_3099_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_3100_ = lean_string_append(v___x_3098_, v___x_3099_);
v___x_3101_ = lean_string_append(v___x_3100_, v_a_3092_);
lean_dec(v_a_3092_);
v___x_3102_ = lean_mk_io_user_error(v___x_3101_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set_tag(v___x_3094_, 1);
lean_ctor_set(v___x_3094_, 0, v___x_3102_);
v___x_3104_ = v___x_3094_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v_result_3067_);
v_a_3107_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3109_ = v___x_3091_;
v_isShared_3110_ = v_isSharedCheck_3117_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3091_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3117_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set_tag(v___x_3069_, 0);
lean_ctor_set(v___x_3069_, 1, v_a_3107_);
lean_ctor_set(v___x_3069_, 0, v_expectedID_3050_);
v___x_3112_ = v___x_3069_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_expectedID_3050_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3114_; 
if (v_isShared_3110_ == 0)
{
lean_ctor_set_tag(v___x_3109_, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3112_);
v___x_3114_ = v___x_3109_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___y_3123_; 
lean_del_object(v___x_3056_);
lean_dec_ref(v_inst_3051_);
lean_dec(v_expectedID_3050_);
v___x_3119_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__3));
v___x_3120_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_3121_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_3054_))
{
case 0:
{
lean_object* v_id_3132_; lean_object* v_method_3133_; lean_object* v_params_x3f_3134_; lean_object* v___x_3135_; lean_object* v___y_3137_; 
v_id_3132_ = lean_ctor_get(v_a_3054_, 0);
lean_inc(v_id_3132_);
v_method_3133_ = lean_ctor_get(v_a_3054_, 1);
lean_inc_ref(v_method_3133_);
v_params_x3f_3134_ = lean_ctor_get(v_a_3054_, 2);
lean_inc(v_params_x3f_3134_);
lean_dec_ref_known(v_a_3054_, 3);
v___x_3135_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3132_) == 0)
{
lean_object* v_s_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
v_s_3148_ = lean_ctor_get(v_id_3132_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_id_3132_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v_id_3132_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_s_3148_);
lean_dec(v_id_3132_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
lean_ctor_set_tag(v___x_3150_, 3);
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_s_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
v___y_3137_ = v___x_3153_;
goto v___jp_3136_;
}
}
}
else
{
lean_object* v_n_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
v_n_3156_ = lean_ctor_get(v_id_3132_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_id_3132_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v_id_3132_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_n_3156_);
lean_dec(v_id_3132_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 2);
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_n_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
v___y_3137_ = v___x_3161_;
goto v___jp_3136_;
}
}
}
v___jp_3136_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3135_);
lean_ctor_set(v___x_3138_, 1, v___y_3137_);
v___x_3139_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3140_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_method_3133_);
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3139_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = lean_box(0);
v___x_3143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3141_);
lean_ctor_set(v___x_3143_, 1, v___x_3142_);
v___x_3144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3138_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3146_ = l_Lean_Json_opt___redArg(v___x_3120_, v___x_3145_, v_params_x3f_3134_);
v___x_3147_ = l_List_appendTR___redArg(v___x_3144_, v___x_3146_);
v___y_3123_ = v___x_3147_;
goto v___jp_3122_;
}
}
case 1:
{
lean_object* v_method_3164_; lean_object* v_params_x3f_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v_method_3164_ = lean_ctor_get(v_a_3054_, 0);
lean_inc_ref(v_method_3164_);
v_params_x3f_3165_ = lean_ctor_get(v_a_3054_, 1);
lean_inc(v_params_x3f_3165_);
lean_dec_ref_known(v_a_3054_, 2);
v___x_3166_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3167_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3167_, 0, v_method_3164_);
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3166_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3170_ = l_Lean_Json_opt___redArg(v___x_3120_, v___x_3169_, v_params_x3f_3165_);
v___x_3171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3168_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___y_3123_ = v___x_3171_;
goto v___jp_3122_;
}
case 2:
{
lean_object* v_id_3172_; lean_object* v_result_3173_; lean_object* v___x_3174_; lean_object* v___y_3176_; 
v_id_3172_ = lean_ctor_get(v_a_3054_, 0);
lean_inc(v_id_3172_);
v_result_3173_ = lean_ctor_get(v_a_3054_, 1);
lean_inc(v_result_3173_);
lean_dec_ref_known(v_a_3054_, 2);
v___x_3174_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3172_) == 0)
{
lean_object* v_s_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
v_s_3183_ = lean_ctor_get(v_id_3172_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_id_3172_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v_id_3172_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_s_3183_);
lean_dec(v_id_3172_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set_tag(v___x_3185_, 3);
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_s_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
v___y_3176_ = v___x_3188_;
goto v___jp_3175_;
}
}
}
else
{
lean_object* v_n_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
v_n_3191_ = lean_ctor_get(v_id_3172_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_id_3172_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v_id_3172_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_n_3191_);
lean_dec(v_id_3172_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
lean_ctor_set_tag(v___x_3193_, 2);
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_n_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
v___y_3176_ = v___x_3196_;
goto v___jp_3175_;
}
}
}
v___jp_3175_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3174_);
lean_ctor_set(v___x_3177_, 1, v___y_3176_);
v___x_3178_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v_result_3173_);
v___x_3180_ = lean_box(0);
v___x_3181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3179_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3177_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___y_3123_ = v___x_3182_;
goto v___jp_3122_;
}
}
default: 
{
lean_object* v_id_3199_; uint8_t v_code_3200_; lean_object* v_message_3201_; lean_object* v_data_x3f_3202_; lean_object* v___x_3203_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___x_3223_; lean_object* v___y_3225_; 
v_id_3199_ = lean_ctor_get(v_a_3054_, 0);
lean_inc(v_id_3199_);
v_code_3200_ = lean_ctor_get_uint8(v_a_3054_, sizeof(void*)*3);
v_message_3201_ = lean_ctor_get(v_a_3054_, 1);
lean_inc_ref(v_message_3201_);
v_data_x3f_3202_ = lean_ctor_get(v_a_3054_, 2);
lean_inc(v_data_x3f_3202_);
lean_dec_ref_known(v_a_3054_, 3);
v___x_3203_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_3223_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3199_) == 0)
{
lean_object* v_s_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
v_s_3241_ = lean_ctor_get(v_id_3199_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_id_3199_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v_id_3199_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_s_3241_);
lean_dec(v_id_3199_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
lean_ctor_set_tag(v___x_3243_, 3);
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_s_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
v___y_3225_ = v___x_3246_;
goto v___jp_3224_;
}
}
}
else
{
lean_object* v_n_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
v_n_3249_ = lean_ctor_get(v_id_3199_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_id_3199_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v_id_3199_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_n_3249_);
lean_dec(v_id_3199_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
lean_ctor_set_tag(v___x_3251_, 2);
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_n_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
v___y_3225_ = v___x_3254_;
goto v___jp_3224_;
}
}
}
v___jp_3204_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_inc(v___y_3208_);
lean_inc_ref(v___y_3207_);
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___y_3207_);
lean_ctor_set(v___x_3209_, 1, v___y_3208_);
v___x_3210_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3211_, 0, v_message_3201_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = lean_box(0);
v___x_3214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3212_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3209_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3217_ = l_Lean_Json_opt___redArg(v___x_3203_, v___x_3216_, v_data_x3f_3202_);
v___x_3218_ = l_List_appendTR___redArg(v___x_3215_, v___x_3217_);
v___x_3219_ = l_Lean_Json_mkObj(v___x_3218_);
lean_dec(v___x_3218_);
lean_inc_ref(v___y_3205_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___y_3205_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set(v___x_3221_, 1, v___x_3213_);
v___x_3222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___y_3206_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___y_3123_ = v___x_3222_;
goto v___jp_3122_;
}
v___jp_3224_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3223_);
lean_ctor_set(v___x_3226_, 1, v___y_3225_);
v___x_3227_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3228_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3200_)
{
case 0:
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3229_;
goto v___jp_3204_;
}
case 1:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3230_;
goto v___jp_3204_;
}
case 2:
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3231_;
goto v___jp_3204_;
}
case 3:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3232_;
goto v___jp_3204_;
}
case 4:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3233_;
goto v___jp_3204_;
}
case 5:
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3234_;
goto v___jp_3204_;
}
case 6:
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3235_;
goto v___jp_3204_;
}
case 7:
{
lean_object* v___x_3236_; 
v___x_3236_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3236_;
goto v___jp_3204_;
}
case 8:
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3237_;
goto v___jp_3204_;
}
case 9:
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3238_;
goto v___jp_3204_;
}
case 10:
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3239_;
goto v___jp_3204_;
}
default: 
{
lean_object* v___x_3240_; 
v___x_3240_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3205_ = v___x_3227_;
v___y_3206_ = v___x_3226_;
v___y_3207_ = v___x_3228_;
v___y_3208_ = v___x_3240_;
goto v___jp_3204_;
}
}
}
}
}
v___jp_3122_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3121_);
lean_ctor_set(v___x_3124_, 1, v___y_3123_);
v___x_3125_ = l_Lean_Json_mkObj(v___x_3124_);
lean_dec_ref_known(v___x_3124_, 2);
v___x_3126_ = l_Lean_Json_compress(v___x_3125_);
v___x_3127_ = lean_string_append(v___x_3119_, v___x_3126_);
lean_dec_ref(v___x_3126_);
v___x_3128_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_3129_ = lean_string_append(v___x_3127_, v___x_3128_);
v___x_3130_ = lean_mk_io_user_error(v___x_3129_);
v___x_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
return v___x_3131_;
}
}
v___jp_3058_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3061_ = lean_string_append(v___y_3059_, v___y_3060_);
lean_dec_ref(v___y_3060_);
v___x_3062_ = lean_mk_io_user_error(v___x_3061_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set_tag(v___x_3056_, 1);
lean_ctor_set(v___x_3056_, 0, v___x_3062_);
v___x_3064_ = v___x_3056_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v_inst_3051_);
lean_dec(v_expectedID_3050_);
v_a_3258_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3053_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3053_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* v_h_3266_, lean_object* v_nBytes_3267_, lean_object* v_expectedID_3268_, lean_object* v_inst_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3266_, v_nBytes_3267_, v_expectedID_3268_, v_inst_3269_);
lean_dec(v_nBytes_3267_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs(lean_object* v_h_3272_, lean_object* v_nBytes_3273_, lean_object* v_expectedID_3274_, lean_object* v_00_u03b1_3275_, lean_object* v_inst_3276_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3272_, v_nBytes_3273_, v_expectedID_3274_, v_inst_3276_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___boxed(lean_object* v_h_3279_, lean_object* v_nBytes_3280_, lean_object* v_expectedID_3281_, lean_object* v_00_u03b1_3282_, lean_object* v_inst_3283_, lean_object* v_a_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_IO_FS_Stream_readResponseAs(v_h_3279_, v_nBytes_3280_, v_expectedID_3281_, v_00_u03b1_3282_, v_inst_3283_);
lean_dec(v_nBytes_3280_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(lean_object* v_k_3286_, lean_object* v_x_3287_){
_start:
{
if (lean_obj_tag(v_x_3287_) == 0)
{
lean_object* v___x_3288_; 
lean_dec_ref(v_k_3286_);
v___x_3288_ = lean_box(0);
return v___x_3288_;
}
else
{
lean_object* v_val_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_val_3289_ = lean_ctor_get(v_x_3287_, 0);
lean_inc(v_val_3289_);
lean_dec_ref_known(v_x_3287_, 1);
v___x_3290_ = l_Lean_Json_Structured_toJson(v_val_3289_);
v___x_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3291_, 0, v_k_3286_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = lean_box(0);
v___x_3293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(lean_object* v_k_3294_, lean_object* v_x_3295_){
_start:
{
if (lean_obj_tag(v_x_3295_) == 0)
{
lean_object* v___x_3296_; 
lean_dec_ref(v_k_3294_);
v___x_3296_ = lean_box(0);
return v___x_3296_;
}
else
{
lean_object* v_val_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_val_3297_ = lean_ctor_get(v_x_3295_, 0);
lean_inc(v_val_3297_);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v_k_3294_);
lean_ctor_set(v___x_3298_, 1, v_val_3297_);
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
return v___x_3300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* v_k_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v_k_3301_, v_x_3302_);
lean_dec(v_x_3302_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage(lean_object* v_h_3304_, lean_object* v_m_3305_){
_start:
{
lean_object* v___x_3307_; lean_object* v___y_3309_; 
v___x_3307_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_3305_))
{
case 0:
{
lean_object* v_id_3313_; lean_object* v_method_3314_; lean_object* v_params_x3f_3315_; lean_object* v___x_3316_; lean_object* v___y_3318_; 
v_id_3313_ = lean_ctor_get(v_m_3305_, 0);
lean_inc(v_id_3313_);
v_method_3314_ = lean_ctor_get(v_m_3305_, 1);
lean_inc_ref(v_method_3314_);
v_params_x3f_3315_ = lean_ctor_get(v_m_3305_, 2);
lean_inc(v_params_x3f_3315_);
lean_dec_ref_known(v_m_3305_, 3);
v___x_3316_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3313_))
{
case 0:
{
lean_object* v_s_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
v_s_3329_ = lean_ctor_get(v_id_3313_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_id_3313_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v_id_3313_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_s_3329_);
lean_dec(v_id_3313_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set_tag(v___x_3331_, 3);
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_s_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
v___y_3318_ = v___x_3334_;
goto v___jp_3317_;
}
}
}
case 1:
{
lean_object* v_n_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
v_n_3337_ = lean_ctor_get(v_id_3313_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_id_3313_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v_id_3313_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_n_3337_);
lean_dec(v_id_3313_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
lean_ctor_set_tag(v___x_3339_, 2);
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_n_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
v___y_3318_ = v___x_3342_;
goto v___jp_3317_;
}
}
}
default: 
{
lean_object* v___x_3345_; 
v___x_3345_ = lean_box(0);
v___y_3318_ = v___x_3345_;
goto v___jp_3317_;
}
}
v___jp_3317_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3316_);
lean_ctor_set(v___x_3319_, 1, v___y_3318_);
v___x_3320_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3321_, 0, v_method_3314_);
v___x_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3319_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3327_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3326_, v_params_x3f_3315_);
v___x_3328_ = l_List_appendTR___redArg(v___x_3325_, v___x_3327_);
v___y_3309_ = v___x_3328_;
goto v___jp_3308_;
}
}
case 1:
{
lean_object* v_method_3346_; lean_object* v_params_x3f_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3359_; 
v_method_3346_ = lean_ctor_get(v_m_3305_, 0);
v_params_x3f_3347_ = lean_ctor_get(v_m_3305_, 1);
v_isSharedCheck_3359_ = !lean_is_exclusive(v_m_3305_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3349_ = v_m_3305_;
v_isShared_3350_ = v_isSharedCheck_3359_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_params_x3f_3347_);
lean_inc(v_method_3346_);
lean_dec(v_m_3305_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3359_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3351_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3352_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3352_, 0, v_method_3346_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set_tag(v___x_3349_, 0);
lean_ctor_set(v___x_3349_, 1, v___x_3352_);
lean_ctor_set(v___x_3349_, 0, v___x_3351_);
v___x_3354_ = v___x_3349_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3351_);
lean_ctor_set(v_reuseFailAlloc_3358_, 1, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3355_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3356_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3355_, v_params_x3f_3347_);
v___x_3357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3354_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___y_3309_ = v___x_3357_;
goto v___jp_3308_;
}
}
}
case 2:
{
lean_object* v_id_3360_; lean_object* v_result_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3393_; 
v_id_3360_ = lean_ctor_get(v_m_3305_, 0);
v_result_3361_ = lean_ctor_get(v_m_3305_, 1);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_m_3305_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3363_ = v_m_3305_;
v_isShared_3364_ = v_isSharedCheck_3393_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_result_3361_);
lean_inc(v_id_3360_);
lean_dec(v_m_3305_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3393_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; lean_object* v___y_3367_; 
v___x_3365_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3360_))
{
case 0:
{
lean_object* v_s_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
v_s_3376_ = lean_ctor_get(v_id_3360_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_id_3360_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v_id_3360_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_s_3376_);
lean_dec(v_id_3360_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
lean_ctor_set_tag(v___x_3378_, 3);
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_s_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
v___y_3367_ = v___x_3381_;
goto v___jp_3366_;
}
}
}
case 1:
{
lean_object* v_n_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
v_n_3384_ = lean_ctor_get(v_id_3360_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_id_3360_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v_id_3360_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_n_3384_);
lean_dec(v_id_3360_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
lean_ctor_set_tag(v___x_3386_, 2);
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_n_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
v___y_3367_ = v___x_3389_;
goto v___jp_3366_;
}
}
}
default: 
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_box(0);
v___y_3367_ = v___x_3392_;
goto v___jp_3366_;
}
}
v___jp_3366_:
{
lean_object* v___x_3369_; 
if (v_isShared_3364_ == 0)
{
lean_ctor_set_tag(v___x_3363_, 0);
lean_ctor_set(v___x_3363_, 1, v___y_3367_);
lean_ctor_set(v___x_3363_, 0, v___x_3365_);
v___x_3369_ = v___x_3363_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3365_);
lean_ctor_set(v_reuseFailAlloc_3375_, 1, v___y_3367_);
v___x_3369_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3370_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3370_);
lean_ctor_set(v___x_3371_, 1, v_result_3361_);
v___x_3372_ = lean_box(0);
v___x_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3371_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
v___x_3374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3369_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___y_3309_ = v___x_3374_;
goto v___jp_3308_;
}
}
}
}
default: 
{
lean_object* v_id_3394_; uint8_t v_code_3395_; lean_object* v_message_3396_; lean_object* v_data_x3f_3397_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___x_3417_; lean_object* v___y_3419_; 
v_id_3394_ = lean_ctor_get(v_m_3305_, 0);
lean_inc(v_id_3394_);
v_code_3395_ = lean_ctor_get_uint8(v_m_3305_, sizeof(void*)*3);
v_message_3396_ = lean_ctor_get(v_m_3305_, 1);
lean_inc_ref(v_message_3396_);
v_data_x3f_3397_ = lean_ctor_get(v_m_3305_, 2);
lean_inc(v_data_x3f_3397_);
lean_dec_ref_known(v_m_3305_, 3);
v___x_3417_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3394_))
{
case 0:
{
lean_object* v_s_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
v_s_3435_ = lean_ctor_get(v_id_3394_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_id_3394_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v_id_3394_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_s_3435_);
lean_dec(v_id_3394_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
lean_ctor_set_tag(v___x_3437_, 3);
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_s_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
v___y_3419_ = v___x_3440_;
goto v___jp_3418_;
}
}
}
case 1:
{
lean_object* v_n_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
v_n_3443_ = lean_ctor_get(v_id_3394_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_id_3394_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v_id_3394_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_n_3443_);
lean_dec(v_id_3394_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
lean_ctor_set_tag(v___x_3445_, 2);
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_n_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
v___y_3419_ = v___x_3448_;
goto v___jp_3418_;
}
}
}
default: 
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_box(0);
v___y_3419_ = v___x_3451_;
goto v___jp_3418_;
}
}
v___jp_3398_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
lean_inc(v___y_3402_);
lean_inc_ref(v___y_3399_);
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___y_3399_);
lean_ctor_set(v___x_3403_, 1, v___y_3402_);
v___x_3404_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3405_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3405_, 0, v_message_3396_);
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = lean_box(0);
v___x_3408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3406_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3403_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3411_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v___x_3410_, v_data_x3f_3397_);
lean_dec(v_data_x3f_3397_);
v___x_3412_ = l_List_appendTR___redArg(v___x_3409_, v___x_3411_);
v___x_3413_ = l_Lean_Json_mkObj(v___x_3412_);
lean_dec(v___x_3412_);
lean_inc_ref(v___y_3400_);
v___x_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___y_3400_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
v___x_3415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
lean_ctor_set(v___x_3415_, 1, v___x_3407_);
v___x_3416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___y_3401_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___y_3309_ = v___x_3416_;
goto v___jp_3308_;
}
v___jp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3417_);
lean_ctor_set(v___x_3420_, 1, v___y_3419_);
v___x_3421_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3422_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3395_)
{
case 0:
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3423_;
goto v___jp_3398_;
}
case 1:
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3424_;
goto v___jp_3398_;
}
case 2:
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3425_;
goto v___jp_3398_;
}
case 3:
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3426_;
goto v___jp_3398_;
}
case 4:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3427_;
goto v___jp_3398_;
}
case 5:
{
lean_object* v___x_3428_; 
v___x_3428_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3428_;
goto v___jp_3398_;
}
case 6:
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3429_;
goto v___jp_3398_;
}
case 7:
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3430_;
goto v___jp_3398_;
}
case 8:
{
lean_object* v___x_3431_; 
v___x_3431_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3431_;
goto v___jp_3398_;
}
case 9:
{
lean_object* v___x_3432_; 
v___x_3432_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3432_;
goto v___jp_3398_;
}
case 10:
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3433_;
goto v___jp_3398_;
}
default: 
{
lean_object* v___x_3434_; 
v___x_3434_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3399_ = v___x_3422_;
v___y_3400_ = v___x_3421_;
v___y_3401_ = v___x_3420_;
v___y_3402_ = v___x_3434_;
goto v___jp_3398_;
}
}
}
}
}
v___jp_3308_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3307_);
lean_ctor_set(v___x_3310_, 1, v___y_3309_);
v___x_3311_ = l_Lean_Json_mkObj(v___x_3310_);
lean_dec_ref_known(v___x_3310_, 2);
v___x_3312_ = l_Lean_IO_FS_Stream_writeJson(v_h_3304_, v___x_3311_);
return v___x_3312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage___boxed(lean_object* v_h_3452_, lean_object* v_m_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3452_, v_m_3453_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg(lean_object* v_inst_3456_, lean_object* v_h_3457_, lean_object* v_r_3458_){
_start:
{
lean_object* v_id_3460_; lean_object* v_method_3461_; lean_object* v_param_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3482_; 
v_id_3460_ = lean_ctor_get(v_r_3458_, 0);
v_method_3461_ = lean_ctor_get(v_r_3458_, 1);
v_param_3462_ = lean_ctor_get(v_r_3458_, 2);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_r_3458_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3464_ = v_r_3458_;
v_isShared_3465_ = v_isSharedCheck_3482_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_param_3462_);
lean_inc(v_method_3461_);
lean_inc(v_id_3460_);
lean_dec(v_r_3458_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3482_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___y_3467_; lean_object* v___x_3472_; 
v___x_3472_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3456_, v_param_3462_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v___x_3473_; 
lean_dec_ref_known(v___x_3472_, 1);
v___x_3473_ = lean_box(0);
v___y_3467_ = v___x_3473_;
goto v___jp_3466_;
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
v_a_3474_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3472_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3472_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
v___y_3467_ = v___x_3479_;
goto v___jp_3466_;
}
}
}
v___jp_3466_:
{
lean_object* v___x_3469_; 
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 2, v___y_3467_);
v___x_3469_ = v___x_3464_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_id_3460_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_method_3461_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v___y_3467_);
v___x_3469_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3457_, v___x_3469_);
return v___x_3470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg___boxed(lean_object* v_inst_3483_, lean_object* v_h_3484_, lean_object* v_r_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3483_, v_h_3484_, v_r_3485_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest(lean_object* v_00_u03b1_3488_, lean_object* v_inst_3489_, lean_object* v_h_3490_, lean_object* v_r_3491_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3489_, v_h_3490_, v_r_3491_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___boxed(lean_object* v_00_u03b1_3494_, lean_object* v_inst_3495_, lean_object* v_h_3496_, lean_object* v_r_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Lean_IO_FS_Stream_writeRequest(v_00_u03b1_3494_, v_inst_3495_, v_h_3496_, v_r_3497_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg(lean_object* v_inst_3500_, lean_object* v_h_3501_, lean_object* v_n_3502_){
_start:
{
lean_object* v_method_3504_; lean_object* v_param_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3525_; 
v_method_3504_ = lean_ctor_get(v_n_3502_, 0);
v_param_3505_ = lean_ctor_get(v_n_3502_, 1);
v_isSharedCheck_3525_ = !lean_is_exclusive(v_n_3502_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3507_ = v_n_3502_;
v_isShared_3508_ = v_isSharedCheck_3525_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_param_3505_);
lean_inc(v_method_3504_);
lean_dec(v_n_3502_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3525_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___y_3510_; lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3500_, v_param_3505_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v___x_3516_; 
lean_dec_ref_known(v___x_3515_, 1);
v___x_3516_ = lean_box(0);
v___y_3510_ = v___x_3516_;
goto v___jp_3509_;
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
v_a_3517_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3515_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3515_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
v___y_3510_ = v___x_3522_;
goto v___jp_3509_;
}
}
}
v___jp_3509_:
{
lean_object* v___x_3512_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set_tag(v___x_3507_, 1);
lean_ctor_set(v___x_3507_, 1, v___y_3510_);
v___x_3512_ = v___x_3507_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_method_3504_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v___y_3510_);
v___x_3512_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3501_, v___x_3512_);
return v___x_3513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg___boxed(lean_object* v_inst_3526_, lean_object* v_h_3527_, lean_object* v_n_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3526_, v_h_3527_, v_n_3528_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification(lean_object* v_00_u03b1_3531_, lean_object* v_inst_3532_, lean_object* v_h_3533_, lean_object* v_n_3534_){
_start:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3532_, v_h_3533_, v_n_3534_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___boxed(lean_object* v_00_u03b1_3537_, lean_object* v_inst_3538_, lean_object* v_h_3539_, lean_object* v_n_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lean_IO_FS_Stream_writeNotification(v_00_u03b1_3537_, v_inst_3538_, v_h_3539_, v_n_3540_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg(lean_object* v_inst_3543_, lean_object* v_h_3544_, lean_object* v_r_3545_){
_start:
{
lean_object* v_id_3547_; lean_object* v_result_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3557_; 
v_id_3547_ = lean_ctor_get(v_r_3545_, 0);
v_result_3548_ = lean_ctor_get(v_r_3545_, 1);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_r_3545_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3550_ = v_r_3545_;
v_isShared_3551_ = v_isSharedCheck_3557_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_result_3548_);
lean_inc(v_id_3547_);
lean_dec(v_r_3545_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3557_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3552_ = lean_apply_1(v_inst_3543_, v_result_3548_);
if (v_isShared_3551_ == 0)
{
lean_ctor_set_tag(v___x_3550_, 2);
lean_ctor_set(v___x_3550_, 1, v___x_3552_);
v___x_3554_ = v___x_3550_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_id_3547_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3544_, v___x_3554_);
return v___x_3555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg___boxed(lean_object* v_inst_3558_, lean_object* v_h_3559_, lean_object* v_r_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3558_, v_h_3559_, v_r_3560_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse(lean_object* v_00_u03b1_3563_, lean_object* v_inst_3564_, lean_object* v_h_3565_, lean_object* v_r_3566_){
_start:
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3564_, v_h_3565_, v_r_3566_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___boxed(lean_object* v_00_u03b1_3569_, lean_object* v_inst_3570_, lean_object* v_h_3571_, lean_object* v_r_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_IO_FS_Stream_writeResponse(v_00_u03b1_3569_, v_inst_3570_, v_h_3571_, v_r_3572_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError(lean_object* v_h_3575_, lean_object* v_e_3576_){
_start:
{
lean_object* v_id_3578_; uint8_t v_code_3579_; lean_object* v_message_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3589_; 
v_id_3578_ = lean_ctor_get(v_e_3576_, 0);
v_code_3579_ = lean_ctor_get_uint8(v_e_3576_, sizeof(void*)*3);
v_message_3580_ = lean_ctor_get(v_e_3576_, 1);
v_isSharedCheck_3589_ = !lean_is_exclusive(v_e_3576_);
if (v_isSharedCheck_3589_ == 0)
{
lean_object* v_unused_3590_; 
v_unused_3590_ = lean_ctor_get(v_e_3576_, 2);
lean_dec(v_unused_3590_);
v___x_3582_ = v_e_3576_;
v_isShared_3583_ = v_isSharedCheck_3589_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_message_3580_);
lean_inc(v_id_3578_);
lean_dec(v_e_3576_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3589_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3584_ = lean_box(0);
if (v_isShared_3583_ == 0)
{
lean_ctor_set_tag(v___x_3582_, 3);
lean_ctor_set(v___x_3582_, 2, v___x_3584_);
v___x_3586_ = v___x_3582_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_id_3578_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_message_3580_);
lean_ctor_set(v_reuseFailAlloc_3588_, 2, v___x_3584_);
lean_ctor_set_uint8(v_reuseFailAlloc_3588_, sizeof(void*)*3, v_code_3579_);
v___x_3586_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3575_, v___x_3586_);
return v___x_3587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError___boxed(lean_object* v_h_3591_, lean_object* v_e_3592_, lean_object* v_a_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_IO_FS_Stream_writeResponseError(v_h_3591_, v_e_3592_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* v_inst_3595_, lean_object* v_h_3596_, lean_object* v_e_3597_){
_start:
{
lean_object* v_id_3599_; uint8_t v_code_3600_; lean_object* v_message_3601_; lean_object* v_data_x3f_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3622_; 
v_id_3599_ = lean_ctor_get(v_e_3597_, 0);
v_code_3600_ = lean_ctor_get_uint8(v_e_3597_, sizeof(void*)*3);
v_message_3601_ = lean_ctor_get(v_e_3597_, 1);
v_data_x3f_3602_ = lean_ctor_get(v_e_3597_, 2);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_e_3597_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3604_ = v_e_3597_;
v_isShared_3605_ = v_isSharedCheck_3622_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_data_x3f_3602_);
lean_inc(v_message_3601_);
lean_inc(v_id_3599_);
lean_dec(v_e_3597_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3622_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___y_3607_; 
if (lean_obj_tag(v_data_x3f_3602_) == 0)
{
lean_object* v___x_3612_; 
lean_dec_ref(v_inst_3595_);
v___x_3612_ = lean_box(0);
v___y_3607_ = v___x_3612_;
goto v___jp_3606_;
}
else
{
lean_object* v_val_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3621_; 
v_val_3613_ = lean_ctor_get(v_data_x3f_3602_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_data_x3f_3602_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3615_ = v_data_x3f_3602_;
v_isShared_3616_ = v_isSharedCheck_3621_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_val_3613_);
lean_dec(v_data_x3f_3602_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3621_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; lean_object* v___x_3619_; 
v___x_3617_ = lean_apply_1(v_inst_3595_, v_val_3613_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 0, v___x_3617_);
v___x_3619_ = v___x_3615_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3617_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
v___y_3607_ = v___x_3619_;
goto v___jp_3606_;
}
}
}
v___jp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 3);
lean_ctor_set(v___x_3604_, 2, v___y_3607_);
v___x_3609_ = v___x_3604_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_id_3599_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_message_3601_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v___y_3607_);
lean_ctor_set_uint8(v_reuseFailAlloc_3611_, sizeof(void*)*3, v_code_3600_);
v___x_3609_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3596_, v___x_3609_);
return v___x_3610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object* v_inst_3623_, lean_object* v_h_3624_, lean_object* v_e_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3623_, v_h_3624_, v_e_3625_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData(lean_object* v_00_u03b1_3628_, lean_object* v_inst_3629_, lean_object* v_h_3630_, lean_object* v_e_3631_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3629_, v_h_3630_, v_e_3631_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object* v_00_u03b1_3634_, lean_object* v_inst_3635_, lean_object* v_h_3636_, lean_object* v_e_3637_, lean_object* v_a_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData(v_00_u03b1_3634_, v_inst_3635_, v_h_3636_, v_e_3637_);
return v_res_3639_;
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
