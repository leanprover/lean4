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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx(uint8_t v_x_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_toCtorIdx___boxed(lean_object* v_x_142_){
_start:
{
uint8_t v_x_4__boxed_143_; lean_object* v_res_144_; 
v_x_4__boxed_143_ = lean_unbox(v_x_142_);
v_res_144_ = l_Lean_JsonRpc_ErrorCode_toCtorIdx(v_x_4__boxed_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(lean_object* v_k_145_){
_start:
{
lean_inc(v_k_145_);
return v_k_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg___boxed(lean_object* v_k_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(v_k_146_);
lean_dec(v_k_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim(lean_object* v_motive_148_, lean_object* v_ctorIdx_149_, uint8_t v_t_150_, lean_object* v_h_151_, lean_object* v_k_152_){
_start:
{
lean_inc(v_k_152_);
return v_k_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___boxed(lean_object* v_motive_153_, lean_object* v_ctorIdx_154_, lean_object* v_t_155_, lean_object* v_h_156_, lean_object* v_k_157_){
_start:
{
uint8_t v_t_boxed_158_; lean_object* v_res_159_; 
v_t_boxed_158_ = lean_unbox(v_t_155_);
v_res_159_ = l_Lean_JsonRpc_ErrorCode_ctorElim(v_motive_153_, v_ctorIdx_154_, v_t_boxed_158_, v_h_156_, v_k_157_);
lean_dec(v_k_157_);
lean_dec(v_ctorIdx_154_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(lean_object* v_parseError_160_){
_start:
{
lean_inc(v_parseError_160_);
return v_parseError_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg___boxed(lean_object* v_parseError_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(v_parseError_161_);
lean_dec(v_parseError_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_object* v_motive_163_, uint8_t v_t_164_, lean_object* v_h_165_, lean_object* v_parseError_166_){
_start:
{
lean_inc(v_parseError_166_);
return v_parseError_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___boxed(lean_object* v_motive_167_, lean_object* v_t_168_, lean_object* v_h_169_, lean_object* v_parseError_170_){
_start:
{
uint8_t v_t_boxed_171_; lean_object* v_res_172_; 
v_t_boxed_171_ = lean_unbox(v_t_168_);
v_res_172_ = l_Lean_JsonRpc_ErrorCode_parseError_elim(v_motive_167_, v_t_boxed_171_, v_h_169_, v_parseError_170_);
lean_dec(v_parseError_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(lean_object* v_invalidRequest_173_){
_start:
{
lean_inc(v_invalidRequest_173_);
return v_invalidRequest_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg___boxed(lean_object* v_invalidRequest_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(v_invalidRequest_174_);
lean_dec(v_invalidRequest_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_object* v_motive_176_, uint8_t v_t_177_, lean_object* v_h_178_, lean_object* v_invalidRequest_179_){
_start:
{
lean_inc(v_invalidRequest_179_);
return v_invalidRequest_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___boxed(lean_object* v_motive_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_invalidRequest_183_){
_start:
{
uint8_t v_t_boxed_184_; lean_object* v_res_185_; 
v_t_boxed_184_ = lean_unbox(v_t_181_);
v_res_185_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(v_motive_180_, v_t_boxed_184_, v_h_182_, v_invalidRequest_183_);
lean_dec(v_invalidRequest_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(lean_object* v_methodNotFound_186_){
_start:
{
lean_inc(v_methodNotFound_186_);
return v_methodNotFound_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg___boxed(lean_object* v_methodNotFound_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(v_methodNotFound_187_);
lean_dec(v_methodNotFound_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(lean_object* v_motive_189_, uint8_t v_t_190_, lean_object* v_h_191_, lean_object* v_methodNotFound_192_){
_start:
{
lean_inc(v_methodNotFound_192_);
return v_methodNotFound_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___boxed(lean_object* v_motive_193_, lean_object* v_t_194_, lean_object* v_h_195_, lean_object* v_methodNotFound_196_){
_start:
{
uint8_t v_t_boxed_197_; lean_object* v_res_198_; 
v_t_boxed_197_ = lean_unbox(v_t_194_);
v_res_198_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(v_motive_193_, v_t_boxed_197_, v_h_195_, v_methodNotFound_196_);
lean_dec(v_methodNotFound_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(lean_object* v_invalidParams_199_){
_start:
{
lean_inc(v_invalidParams_199_);
return v_invalidParams_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg___boxed(lean_object* v_invalidParams_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(v_invalidParams_200_);
lean_dec(v_invalidParams_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_object* v_motive_202_, uint8_t v_t_203_, lean_object* v_h_204_, lean_object* v_invalidParams_205_){
_start:
{
lean_inc(v_invalidParams_205_);
return v_invalidParams_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___boxed(lean_object* v_motive_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_invalidParams_209_){
_start:
{
uint8_t v_t_boxed_210_; lean_object* v_res_211_; 
v_t_boxed_210_ = lean_unbox(v_t_207_);
v_res_211_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim(v_motive_206_, v_t_boxed_210_, v_h_208_, v_invalidParams_209_);
lean_dec(v_invalidParams_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(lean_object* v_internalError_212_){
_start:
{
lean_inc(v_internalError_212_);
return v_internalError_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg___boxed(lean_object* v_internalError_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(v_internalError_213_);
lean_dec(v_internalError_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_object* v_motive_215_, uint8_t v_t_216_, lean_object* v_h_217_, lean_object* v_internalError_218_){
_start:
{
lean_inc(v_internalError_218_);
return v_internalError_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___boxed(lean_object* v_motive_219_, lean_object* v_t_220_, lean_object* v_h_221_, lean_object* v_internalError_222_){
_start:
{
uint8_t v_t_boxed_223_; lean_object* v_res_224_; 
v_t_boxed_223_ = lean_unbox(v_t_220_);
v_res_224_ = l_Lean_JsonRpc_ErrorCode_internalError_elim(v_motive_219_, v_t_boxed_223_, v_h_221_, v_internalError_222_);
lean_dec(v_internalError_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(lean_object* v_serverNotInitialized_225_){
_start:
{
lean_inc(v_serverNotInitialized_225_);
return v_serverNotInitialized_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg___boxed(lean_object* v_serverNotInitialized_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(v_serverNotInitialized_226_);
lean_dec(v_serverNotInitialized_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_object* v_motive_228_, uint8_t v_t_229_, lean_object* v_h_230_, lean_object* v_serverNotInitialized_231_){
_start:
{
lean_inc(v_serverNotInitialized_231_);
return v_serverNotInitialized_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___boxed(lean_object* v_motive_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_serverNotInitialized_235_){
_start:
{
uint8_t v_t_boxed_236_; lean_object* v_res_237_; 
v_t_boxed_236_ = lean_unbox(v_t_233_);
v_res_237_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(v_motive_232_, v_t_boxed_236_, v_h_234_, v_serverNotInitialized_235_);
lean_dec(v_serverNotInitialized_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(lean_object* v_unknownErrorCode_238_){
_start:
{
lean_inc(v_unknownErrorCode_238_);
return v_unknownErrorCode_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg___boxed(lean_object* v_unknownErrorCode_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(v_unknownErrorCode_239_);
lean_dec(v_unknownErrorCode_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_object* v_motive_241_, uint8_t v_t_242_, lean_object* v_h_243_, lean_object* v_unknownErrorCode_244_){
_start:
{
lean_inc(v_unknownErrorCode_244_);
return v_unknownErrorCode_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___boxed(lean_object* v_motive_245_, lean_object* v_t_246_, lean_object* v_h_247_, lean_object* v_unknownErrorCode_248_){
_start:
{
uint8_t v_t_boxed_249_; lean_object* v_res_250_; 
v_t_boxed_249_ = lean_unbox(v_t_246_);
v_res_250_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(v_motive_245_, v_t_boxed_249_, v_h_247_, v_unknownErrorCode_248_);
lean_dec(v_unknownErrorCode_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(lean_object* v_contentModified_251_){
_start:
{
lean_inc(v_contentModified_251_);
return v_contentModified_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg___boxed(lean_object* v_contentModified_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim___redArg(v_contentModified_252_);
lean_dec(v_contentModified_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_object* v_motive_254_, uint8_t v_t_255_, lean_object* v_h_256_, lean_object* v_contentModified_257_){
_start:
{
lean_inc(v_contentModified_257_);
return v_contentModified_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim___boxed(lean_object* v_motive_258_, lean_object* v_t_259_, lean_object* v_h_260_, lean_object* v_contentModified_261_){
_start:
{
uint8_t v_t_boxed_262_; lean_object* v_res_263_; 
v_t_boxed_262_ = lean_unbox(v_t_259_);
v_res_263_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim(v_motive_258_, v_t_boxed_262_, v_h_260_, v_contentModified_261_);
lean_dec(v_contentModified_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(lean_object* v_requestCancelled_264_){
_start:
{
lean_inc(v_requestCancelled_264_);
return v_requestCancelled_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg___boxed(lean_object* v_requestCancelled_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___redArg(v_requestCancelled_265_);
lean_dec(v_requestCancelled_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_object* v_motive_267_, uint8_t v_t_268_, lean_object* v_h_269_, lean_object* v_requestCancelled_270_){
_start:
{
lean_inc(v_requestCancelled_270_);
return v_requestCancelled_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___boxed(lean_object* v_motive_271_, lean_object* v_t_272_, lean_object* v_h_273_, lean_object* v_requestCancelled_274_){
_start:
{
uint8_t v_t_boxed_275_; lean_object* v_res_276_; 
v_t_boxed_275_ = lean_unbox(v_t_272_);
v_res_276_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(v_motive_271_, v_t_boxed_275_, v_h_273_, v_requestCancelled_274_);
lean_dec(v_requestCancelled_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(lean_object* v_rpcNeedsReconnect_277_){
_start:
{
lean_inc(v_rpcNeedsReconnect_277_);
return v_rpcNeedsReconnect_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg___boxed(lean_object* v_rpcNeedsReconnect_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(v_rpcNeedsReconnect_278_);
lean_dec(v_rpcNeedsReconnect_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(lean_object* v_motive_280_, uint8_t v_t_281_, lean_object* v_h_282_, lean_object* v_rpcNeedsReconnect_283_){
_start:
{
lean_inc(v_rpcNeedsReconnect_283_);
return v_rpcNeedsReconnect_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___boxed(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_rpcNeedsReconnect_287_){
_start:
{
uint8_t v_t_boxed_288_; lean_object* v_res_289_; 
v_t_boxed_288_ = lean_unbox(v_t_285_);
v_res_289_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(v_motive_284_, v_t_boxed_288_, v_h_286_, v_rpcNeedsReconnect_287_);
lean_dec(v_rpcNeedsReconnect_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(lean_object* v_workerExited_290_){
_start:
{
lean_inc(v_workerExited_290_);
return v_workerExited_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg___boxed(lean_object* v_workerExited_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(v_workerExited_291_);
lean_dec(v_workerExited_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim(lean_object* v_motive_293_, uint8_t v_t_294_, lean_object* v_h_295_, lean_object* v_workerExited_296_){
_start:
{
lean_inc(v_workerExited_296_);
return v_workerExited_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___boxed(lean_object* v_motive_297_, lean_object* v_t_298_, lean_object* v_h_299_, lean_object* v_workerExited_300_){
_start:
{
uint8_t v_t_boxed_301_; lean_object* v_res_302_; 
v_t_boxed_301_ = lean_unbox(v_t_298_);
v_res_302_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim(v_motive_297_, v_t_boxed_301_, v_h_299_, v_workerExited_300_);
lean_dec(v_workerExited_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(lean_object* v_workerCrashed_303_){
_start:
{
lean_inc(v_workerCrashed_303_);
return v_workerCrashed_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg___boxed(lean_object* v_workerCrashed_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(v_workerCrashed_304_);
lean_dec(v_workerCrashed_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_object* v_motive_306_, uint8_t v_t_307_, lean_object* v_h_308_, lean_object* v_workerCrashed_309_){
_start:
{
lean_inc(v_workerCrashed_309_);
return v_workerCrashed_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___boxed(lean_object* v_motive_310_, lean_object* v_t_311_, lean_object* v_h_312_, lean_object* v_workerCrashed_313_){
_start:
{
uint8_t v_t_boxed_314_; lean_object* v_res_315_; 
v_t_boxed_314_ = lean_unbox(v_t_311_);
v_res_315_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(v_motive_310_, v_t_boxed_314_, v_h_312_, v_workerCrashed_313_);
lean_dec(v_workerCrashed_313_);
return v_res_315_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode_default(void){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode(void){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = 0;
return v___x_317_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqErrorCode_beq(uint8_t v_x_318_, uint8_t v_y_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_320_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_x_318_);
v___x_321_ = l_Lean_JsonRpc_ErrorCode_ctorIdx(v_y_319_);
v___x_322_ = lean_nat_dec_eq(v___x_320_, v___x_321_);
lean_dec(v___x_321_);
lean_dec(v___x_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode_beq___boxed(lean_object* v_x_323_, lean_object* v_y_324_){
_start:
{
uint8_t v_x_17__boxed_325_; uint8_t v_y_18__boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v_x_17__boxed_325_ = lean_unbox(v_x_323_);
v_y_18__boxed_326_ = lean_unbox(v_y_324_);
v_res_327_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_x_17__boxed_325_, v_y_18__boxed_326_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(32700u);
v___x_335_ = lean_nat_to_int(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2);
v___x_337_ = lean_int_neg(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(32600u);
v___x_339_ = lean_nat_to_int(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4);
v___x_341_ = lean_int_neg(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(32601u);
v___x_343_ = lean_nat_to_int(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6);
v___x_345_ = lean_int_neg(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(32602u);
v___x_347_ = lean_nat_to_int(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8);
v___x_349_ = lean_int_neg(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(32603u);
v___x_351_ = lean_nat_to_int(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10);
v___x_353_ = lean_int_neg(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(32002u);
v___x_355_ = lean_nat_to_int(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12);
v___x_357_ = lean_int_neg(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(32001u);
v___x_359_ = lean_nat_to_int(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14);
v___x_361_ = lean_int_neg(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_unsigned_to_nat(32801u);
v___x_363_ = lean_nat_to_int(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16);
v___x_365_ = lean_int_neg(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(32800u);
v___x_367_ = lean_nat_to_int(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18);
v___x_369_ = lean_int_neg(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_unsigned_to_nat(32900u);
v___x_371_ = lean_nat_to_int(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20);
v___x_373_ = lean_int_neg(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_unsigned_to_nat(32901u);
v___x_375_ = lean_nat_to_int(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22);
v___x_377_ = lean_int_neg(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_unsigned_to_nat(32902u);
v___x_379_ = lean_nat_to_int(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24);
v___x_381_ = lean_int_neg(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(lean_object* v_x_418_){
_start:
{
if (lean_obj_tag(v_x_418_) == 2)
{
lean_object* v_n_421_; lean_object* v_mantissa_422_; lean_object* v_exponent_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_n_421_ = lean_ctor_get(v_x_418_, 0);
v_mantissa_422_ = lean_ctor_get(v_n_421_, 0);
v_exponent_423_ = lean_ctor_get(v_n_421_, 1);
v___x_424_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_425_ = lean_int_dec_eq(v_mantissa_422_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_427_ = lean_int_dec_eq(v_mantissa_422_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_429_ = lean_int_dec_eq(v_mantissa_422_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_431_ = lean_int_dec_eq(v_mantissa_422_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_433_ = lean_int_dec_eq(v_mantissa_422_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_435_ = lean_int_dec_eq(v_mantissa_422_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_437_ = lean_int_dec_eq(v_mantissa_422_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_439_ = lean_int_dec_eq(v_mantissa_422_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_441_ = lean_int_dec_eq(v_mantissa_422_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_443_ = lean_int_dec_eq(v_mantissa_422_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_445_ = lean_int_dec_eq(v_mantissa_422_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_447_ = lean_int_dec_eq(v_mantissa_422_, v___x_446_);
if (v___x_447_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_nat_dec_eq(v_exponent_423_, v___x_448_);
if (v___x_449_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_450_; 
v___x_450_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_450_;
}
}
}
else
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_nat_dec_eq(v_exponent_423_, v___x_451_);
if (v___x_452_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_453_; 
v___x_453_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_453_;
}
}
}
else
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_nat_dec_eq(v_exponent_423_, v___x_454_);
if (v___x_455_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_456_;
}
}
}
else
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_nat_dec_eq(v_exponent_423_, v___x_457_);
if (v___x_458_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_459_;
}
}
}
else
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_nat_dec_eq(v_exponent_423_, v___x_460_);
if (v___x_461_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_462_;
}
}
}
else
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_nat_dec_eq(v_exponent_423_, v___x_463_);
if (v___x_464_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_465_; 
v___x_465_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_465_;
}
}
}
else
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_nat_dec_eq(v_exponent_423_, v___x_466_);
if (v___x_467_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_468_; 
v___x_468_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_468_;
}
}
}
else
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_nat_dec_eq(v_exponent_423_, v___x_469_);
if (v___x_470_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_471_;
}
}
}
else
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_nat_dec_eq(v_exponent_423_, v___x_472_);
if (v___x_473_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_474_;
}
}
}
else
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_nat_dec_eq(v_exponent_423_, v___x_475_);
if (v___x_476_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_477_;
}
}
}
else
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = lean_nat_dec_eq(v_exponent_423_, v___x_478_);
if (v___x_479_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_480_;
}
}
}
else
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = lean_nat_dec_eq(v_exponent_423_, v___x_481_);
if (v___x_482_ == 0)
{
goto v___jp_419_;
}
else
{
lean_object* v___x_483_; 
v___x_483_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_483_;
}
}
}
else
{
goto v___jp_419_;
}
v___jp_419_:
{
lean_object* v___x_420_; 
v___x_420_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed(lean_object* v_x_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(v_x_484_);
lean_dec(v_x_484_);
return v_res_485_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_489_ = l_Lean_JsonNumber_fromInt(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0);
v___x_491_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_493_ = l_Lean_JsonNumber_fromInt(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2);
v___x_495_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_497_ = l_Lean_JsonNumber_fromInt(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4);
v___x_499_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_501_ = l_Lean_JsonNumber_fromInt(v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6);
v___x_503_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_505_ = l_Lean_JsonNumber_fromInt(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8);
v___x_507_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_509_ = l_Lean_JsonNumber_fromInt(v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10);
v___x_511_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_513_ = l_Lean_JsonNumber_fromInt(v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12);
v___x_515_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_517_ = l_Lean_JsonNumber_fromInt(v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14);
v___x_519_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_521_ = l_Lean_JsonNumber_fromInt(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16);
v___x_523_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_525_ = l_Lean_JsonNumber_fromInt(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18);
v___x_527_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_529_ = l_Lean_JsonNumber_fromInt(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20);
v___x_531_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_533_ = l_Lean_JsonNumber_fromInt(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22);
v___x_535_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t v_x_536_){
_start:
{
switch(v_x_536_)
{
case 0:
{
lean_object* v___x_537_; 
v___x_537_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
return v___x_537_;
}
case 1:
{
lean_object* v___x_538_; 
v___x_538_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
return v___x_538_;
}
case 2:
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
return v___x_539_;
}
case 3:
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
return v___x_540_;
}
case 4:
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
return v___x_541_;
}
case 5:
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
return v___x_542_;
}
case 6:
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
return v___x_543_;
}
case 7:
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
return v___x_544_;
}
case 8:
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
return v___x_545_;
}
case 9:
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
return v___x_546_;
}
case 10:
{
lean_object* v___x_547_; 
v___x_547_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
return v___x_547_;
}
default: 
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object* v_x_549_){
_start:
{
uint8_t v_x_474__boxed_550_; lean_object* v_res_551_; 
v_x_474__boxed_550_ = lean_unbox(v_x_549_);
v_res_551_ = l_Lean_JsonRpc_instToJsonErrorCode___lam__0(v_x_474__boxed_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx(lean_object* v_x_554_){
_start:
{
switch(lean_obj_tag(v_x_554_))
{
case 0:
{
lean_object* v___x_555_; 
v___x_555_ = lean_unsigned_to_nat(0u);
return v___x_555_;
}
case 1:
{
lean_object* v___x_556_; 
v___x_556_ = lean_unsigned_to_nat(1u);
return v___x_556_;
}
case 2:
{
lean_object* v___x_557_; 
v___x_557_ = lean_unsigned_to_nat(2u);
return v___x_557_;
}
default: 
{
lean_object* v___x_558_; 
v___x_558_ = lean_unsigned_to_nat(3u);
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___boxed(lean_object* v_x_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_JsonRpc_Message_ctorIdx(v_x_559_);
lean_dec_ref(v_x_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___redArg(lean_object* v_t_561_, lean_object* v_k_562_){
_start:
{
switch(lean_obj_tag(v_t_561_))
{
case 0:
{
lean_object* v_id_563_; lean_object* v_method_564_; lean_object* v_params_x3f_565_; lean_object* v___x_566_; 
v_id_563_ = lean_ctor_get(v_t_561_, 0);
lean_inc(v_id_563_);
v_method_564_ = lean_ctor_get(v_t_561_, 1);
lean_inc_ref(v_method_564_);
v_params_x3f_565_ = lean_ctor_get(v_t_561_, 2);
lean_inc(v_params_x3f_565_);
lean_dec_ref_known(v_t_561_, 3);
v___x_566_ = lean_apply_3(v_k_562_, v_id_563_, v_method_564_, v_params_x3f_565_);
return v___x_566_;
}
case 1:
{
lean_object* v_method_567_; lean_object* v_params_x3f_568_; lean_object* v___x_569_; 
v_method_567_ = lean_ctor_get(v_t_561_, 0);
lean_inc_ref(v_method_567_);
v_params_x3f_568_ = lean_ctor_get(v_t_561_, 1);
lean_inc(v_params_x3f_568_);
lean_dec_ref_known(v_t_561_, 2);
v___x_569_ = lean_apply_2(v_k_562_, v_method_567_, v_params_x3f_568_);
return v___x_569_;
}
case 2:
{
lean_object* v_id_570_; lean_object* v_result_571_; lean_object* v___x_572_; 
v_id_570_ = lean_ctor_get(v_t_561_, 0);
lean_inc(v_id_570_);
v_result_571_ = lean_ctor_get(v_t_561_, 1);
lean_inc(v_result_571_);
lean_dec_ref_known(v_t_561_, 2);
v___x_572_ = lean_apply_2(v_k_562_, v_id_570_, v_result_571_);
return v___x_572_;
}
default: 
{
lean_object* v_id_573_; uint8_t v_code_574_; lean_object* v_message_575_; lean_object* v_data_x3f_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_id_573_ = lean_ctor_get(v_t_561_, 0);
lean_inc(v_id_573_);
v_code_574_ = lean_ctor_get_uint8(v_t_561_, sizeof(void*)*3);
v_message_575_ = lean_ctor_get(v_t_561_, 1);
lean_inc_ref(v_message_575_);
v_data_x3f_576_ = lean_ctor_get(v_t_561_, 2);
lean_inc(v_data_x3f_576_);
lean_dec_ref_known(v_t_561_, 3);
v___x_577_ = lean_box(v_code_574_);
v___x_578_ = lean_apply_4(v_k_562_, v_id_573_, v___x_577_, v_message_575_, v_data_x3f_576_);
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim(lean_object* v_motive_579_, lean_object* v_ctorIdx_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_k_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_581_, v_k_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorElim___boxed(lean_object* v_motive_585_, lean_object* v_ctorIdx_586_, lean_object* v_t_587_, lean_object* v_h_588_, lean_object* v_k_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_JsonRpc_Message_ctorElim(v_motive_585_, v_ctorIdx_586_, v_t_587_, v_h_588_, v_k_589_);
lean_dec(v_ctorIdx_586_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim___redArg(lean_object* v_t_591_, lean_object* v_request_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_591_, v_request_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_request_elim(lean_object* v_motive_594_, lean_object* v_t_595_, lean_object* v_h_596_, lean_object* v_request_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_595_, v_request_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim___redArg(lean_object* v_t_599_, lean_object* v_notification_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_599_, v_notification_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_notification_elim(lean_object* v_motive_602_, lean_object* v_t_603_, lean_object* v_h_604_, lean_object* v_notification_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_603_, v_notification_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim___redArg(lean_object* v_t_607_, lean_object* v_response_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_607_, v_response_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_response_elim(lean_object* v_motive_610_, lean_object* v_t_611_, lean_object* v_h_612_, lean_object* v_response_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_611_, v_response_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim___redArg(lean_object* v_t_615_, lean_object* v_responseError_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_615_, v_responseError_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_responseError_elim(lean_object* v_motive_618_, lean_object* v_t_619_, lean_object* v_h_620_, lean_object* v_responseError_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_JsonRpc_Message_ctorElim___redArg(v_t_619_, v_responseError_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default___redArg(lean_object* v_inst_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_630_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default));
v___x_631_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
lean_ctor_set(v___x_632_, 2, v_inst_629_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest_default(lean_object* v_00_u03b1_633_, lean_object* v_inst_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest___redArg(lean_object* v_inst_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedRequest(lean_object* v_a_638_, lean_object* v_inst_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_JsonRpc_instInhabitedRequest_default___redArg(v_inst_639_);
return v___x_640_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq___redArg(lean_object* v_inst_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
lean_object* v_id_644_; lean_object* v_method_645_; lean_object* v_param_646_; lean_object* v_id_647_; lean_object* v_method_648_; lean_object* v_param_649_; uint8_t v___x_650_; 
v_id_644_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_id_644_);
v_method_645_ = lean_ctor_get(v_x_642_, 1);
lean_inc_ref(v_method_645_);
v_param_646_ = lean_ctor_get(v_x_642_, 2);
lean_inc(v_param_646_);
lean_dec_ref(v_x_642_);
v_id_647_ = lean_ctor_get(v_x_643_, 0);
lean_inc(v_id_647_);
v_method_648_ = lean_ctor_get(v_x_643_, 1);
lean_inc_ref(v_method_648_);
v_param_649_ = lean_ctor_get(v_x_643_, 2);
lean_inc(v_param_649_);
lean_dec_ref(v_x_643_);
v___x_650_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_644_, v_id_647_);
lean_dec(v_id_647_);
lean_dec(v_id_644_);
if (v___x_650_ == 0)
{
lean_dec(v_param_649_);
lean_dec_ref(v_method_648_);
lean_dec(v_param_646_);
lean_dec_ref(v_method_645_);
lean_dec_ref(v_inst_641_);
return v___x_650_;
}
else
{
uint8_t v___x_651_; 
v___x_651_ = lean_string_dec_eq(v_method_645_, v_method_648_);
lean_dec_ref(v_method_648_);
lean_dec_ref(v_method_645_);
if (v___x_651_ == 0)
{
lean_dec(v_param_649_);
lean_dec(v_param_646_);
lean_dec_ref(v_inst_641_);
return v___x_651_;
}
else
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = lean_apply_2(v_inst_641_, v_param_646_, v_param_649_);
v___x_653_ = lean_unbox(v___x_652_);
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___redArg___boxed(lean_object* v_inst_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
uint8_t v_res_657_; lean_object* v_r_658_; 
v_res_657_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_654_, v_x_655_, v_x_656_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqRequest_beq(lean_object* v_00_u03b1_659_, lean_object* v_inst_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
uint8_t v___x_663_; 
v___x_663_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_660_, v_x_661_, v_x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___boxed(lean_object* v_00_u03b1_664_, lean_object* v_inst_665_, lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
uint8_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = l_Lean_JsonRpc_instBEqRequest_beq(v_00_u03b1_664_, v_inst_665_, v_x_666_, v_x_667_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object* v_inst_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_671_, 0, lean_box(0));
lean_closure_set(v___x_671_, 1, v_inst_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object* v_00_u03b1_672_, lean_object* v_inst_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_674_, 0, lean_box(0));
lean_closure_set(v___x_674_, 1, v_inst_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object* v_inst_675_, lean_object* v_r_676_){
_start:
{
lean_object* v_id_677_; lean_object* v_method_678_; lean_object* v_param_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_699_; 
v_id_677_ = lean_ctor_get(v_r_676_, 0);
v_method_678_ = lean_ctor_get(v_r_676_, 1);
v_param_679_ = lean_ctor_get(v_r_676_, 2);
v_isSharedCheck_699_ = !lean_is_exclusive(v_r_676_);
if (v_isSharedCheck_699_ == 0)
{
v___x_681_ = v_r_676_;
v_isShared_682_ = v_isSharedCheck_699_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_param_679_);
lean_inc(v_method_678_);
lean_inc(v_id_677_);
lean_dec(v_r_676_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_699_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_675_, v_param_679_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v___x_684_; lean_object* v___x_686_; 
lean_dec_ref_known(v___x_683_, 1);
v___x_684_ = lean_box(0);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 2, v___x_684_);
v___x_686_ = v___x_681_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_id_677_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_method_678_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_698_; 
v_a_688_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_698_ == 0)
{
v___x_690_ = v___x_683_;
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_683_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_697_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 2, v___x_693_);
v___x_695_ = v___x_681_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_id_677_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_method_678_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object* v_inst_700_){
_start:
{
lean_object* v___f_701_; 
v___f_701_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_701_, 0, v_inst_700_);
return v___f_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object* v_00_u03b1_702_, lean_object* v_inst_703_){
_start:
{
lean_object* v___f_704_; 
v___f_704_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_704_, 0, v_inst_703_);
return v___f_704_;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object* v_x_705_){
_start:
{
if (lean_obj_tag(v_x_705_) == 0)
{
lean_object* v___x_706_; 
v___x_706_ = lean_box(0);
return v___x_706_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_708_; 
v_val_707_ = lean_ctor_get(v_x_705_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v_x_705_, 1);
v___x_708_ = l_Lean_Json_Structured_toJson(v_val_707_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ofMessage_x3f(lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_709_) == 0)
{
lean_object* v_id_710_; lean_object* v_method_711_; lean_object* v_params_x3f_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_721_; 
v_id_710_ = lean_ctor_get(v_x_709_, 0);
v_method_711_ = lean_ctor_get(v_x_709_, 1);
v_params_x3f_712_ = lean_ctor_get(v_x_709_, 2);
v_isSharedCheck_721_ = !lean_is_exclusive(v_x_709_);
if (v_isSharedCheck_721_ == 0)
{
v___x_714_ = v_x_709_;
v_isShared_715_ = v_isSharedCheck_721_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_params_x3f_712_);
lean_inc(v_method_711_);
lean_inc(v_id_710_);
lean_dec(v_x_709_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_721_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_712_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 2, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_id_710_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_method_711_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v___x_716_);
v___x_718_ = v_reuseFailAlloc_720_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; 
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
}
else
{
lean_object* v___x_722_; 
lean_dec_ref(v_x_709_);
v___x_722_ = lean_box(0);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default___redArg(lean_object* v_inst_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v_inst_723_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default(lean_object* v_00_u03b1_726_, lean_object* v_inst_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___redArg(lean_object* v_inst_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object* v_a_731_, lean_object* v_inst_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_732_);
return v___x_733_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq___redArg(lean_object* v_inst_734_, lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
lean_object* v_method_737_; lean_object* v_param_738_; lean_object* v_method_739_; lean_object* v_param_740_; uint8_t v___x_741_; 
v_method_737_ = lean_ctor_get(v_x_735_, 0);
lean_inc_ref(v_method_737_);
v_param_738_ = lean_ctor_get(v_x_735_, 1);
lean_inc(v_param_738_);
lean_dec_ref(v_x_735_);
v_method_739_ = lean_ctor_get(v_x_736_, 0);
lean_inc_ref(v_method_739_);
v_param_740_ = lean_ctor_get(v_x_736_, 1);
lean_inc(v_param_740_);
lean_dec_ref(v_x_736_);
v___x_741_ = lean_string_dec_eq(v_method_737_, v_method_739_);
lean_dec_ref(v_method_739_);
lean_dec_ref(v_method_737_);
if (v___x_741_ == 0)
{
lean_dec(v_param_740_);
lean_dec(v_param_738_);
lean_dec_ref(v_inst_734_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_apply_2(v_inst_734_, v_param_738_, v_param_740_);
v___x_743_ = lean_unbox(v___x_742_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___redArg___boxed(lean_object* v_inst_744_, lean_object* v_x_745_, lean_object* v_x_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_744_, v_x_745_, v_x_746_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqNotification_beq(lean_object* v_00_u03b1_749_, lean_object* v_inst_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
uint8_t v___x_753_; 
v___x_753_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_750_, v_x_751_, v_x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___boxed(lean_object* v_00_u03b1_754_, lean_object* v_inst_755_, lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l_Lean_JsonRpc_instBEqNotification_beq(v_00_u03b1_754_, v_inst_755_, v_x_756_, v_x_757_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification___redArg(lean_object* v_inst_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(v___x_761_, 0, lean_box(0));
lean_closure_set(v___x_761_, 1, v_inst_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification(lean_object* v_00_u03b1_762_, lean_object* v_inst_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqNotification_beq___boxed), 4, 2);
lean_closure_set(v___x_764_, 0, lean_box(0));
lean_closure_set(v___x_764_, 1, v_inst_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0(lean_object* v_inst_765_, lean_object* v_r_766_){
_start:
{
lean_object* v_method_767_; lean_object* v_param_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_788_; 
v_method_767_ = lean_ctor_get(v_r_766_, 0);
v_param_768_ = lean_ctor_get(v_r_766_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v_r_766_);
if (v_isSharedCheck_788_ == 0)
{
v___x_770_ = v_r_766_;
v_isShared_771_ = v_isSharedCheck_788_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_param_768_);
lean_inc(v_method_767_);
lean_dec(v_r_766_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_788_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_765_, v_param_768_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec_ref_known(v___x_772_, 1);
v___x_773_ = lean_box(0);
if (v_isShared_771_ == 0)
{
lean_ctor_set_tag(v___x_770_, 1);
lean_ctor_set(v___x_770_, 1, v___x_773_);
v___x_775_ = v___x_770_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_method_767_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_787_; 
v_a_777_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_787_ == 0)
{
v___x_779_ = v___x_772_;
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_772_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_786_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set_tag(v___x_770_, 1);
lean_ctor_set(v___x_770_, 1, v___x_782_);
v___x_784_ = v___x_770_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_method_767_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg(lean_object* v_inst_789_){
_start:
{
lean_object* v___f_790_; 
v___f_790_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_790_, 0, v_inst_789_);
return v___f_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson(lean_object* v_00_u03b1_791_, lean_object* v_inst_792_){
_start:
{
lean_object* v___f_793_; 
v___f_793_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutNotificationMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_793_, 0, v_inst_792_);
return v___f_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Notification_ofMessage_x3f(lean_object* v_x_794_){
_start:
{
if (lean_obj_tag(v_x_794_) == 1)
{
lean_object* v_method_795_; lean_object* v_params_x3f_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_805_; 
v_method_795_ = lean_ctor_get(v_x_794_, 0);
v_params_x3f_796_ = lean_ctor_get(v_x_794_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_805_ == 0)
{
v___x_798_ = v_x_794_;
v_isShared_799_ = v_isSharedCheck_805_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_params_x3f_796_);
lean_inc(v_method_795_);
lean_dec(v_x_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_805_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = l_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_796_);
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 0);
lean_ctor_set(v___x_798_, 1, v___x_800_);
v___x_802_ = v___x_798_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_method_795_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v___x_800_);
v___x_802_ = v_reuseFailAlloc_804_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; 
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
}
else
{
lean_object* v___x_806_; 
lean_dec_ref(v_x_794_);
v___x_806_ = lean_box(0);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default___redArg(lean_object* v_inst_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default));
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v_inst_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse_default(lean_object* v_00_u03b1_810_, lean_object* v_inst_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse___redArg(lean_object* v_inst_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponse(lean_object* v_a_815_, lean_object* v_inst_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_JsonRpc_instInhabitedResponse_default___redArg(v_inst_816_);
return v___x_817_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq___redArg(lean_object* v_inst_818_, lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
lean_object* v_id_821_; lean_object* v_result_822_; lean_object* v_id_823_; lean_object* v_result_824_; uint8_t v___x_825_; 
v_id_821_ = lean_ctor_get(v_x_819_, 0);
lean_inc(v_id_821_);
v_result_822_ = lean_ctor_get(v_x_819_, 1);
lean_inc(v_result_822_);
lean_dec_ref(v_x_819_);
v_id_823_ = lean_ctor_get(v_x_820_, 0);
lean_inc(v_id_823_);
v_result_824_ = lean_ctor_get(v_x_820_, 1);
lean_inc(v_result_824_);
lean_dec_ref(v_x_820_);
v___x_825_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_821_, v_id_823_);
lean_dec(v_id_823_);
lean_dec(v_id_821_);
if (v___x_825_ == 0)
{
lean_dec(v_result_824_);
lean_dec(v_result_822_);
lean_dec_ref(v_inst_818_);
return v___x_825_;
}
else
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = lean_apply_2(v_inst_818_, v_result_822_, v_result_824_);
v___x_827_ = lean_unbox(v___x_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___redArg___boxed(lean_object* v_inst_828_, lean_object* v_x_829_, lean_object* v_x_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_828_, v_x_829_, v_x_830_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponse_beq(lean_object* v_00_u03b1_833_, lean_object* v_inst_834_, lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_834_, v_x_835_, v_x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___boxed(lean_object* v_00_u03b1_838_, lean_object* v_inst_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Lean_JsonRpc_instBEqResponse_beq(v_00_u03b1_838_, v_inst_839_, v_x_840_, v_x_841_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object* v_inst_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_845_, 0, lean_box(0));
lean_closure_set(v___x_845_, 1, v_inst_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object* v_00_u03b1_846_, lean_object* v_inst_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_848_, 0, lean_box(0));
lean_closure_set(v___x_848_, 1, v_inst_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(lean_object* v_inst_849_, lean_object* v_r_850_){
_start:
{
lean_object* v_id_851_; lean_object* v_result_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_860_; 
v_id_851_ = lean_ctor_get(v_r_850_, 0);
v_result_852_ = lean_ctor_get(v_r_850_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_r_850_);
if (v_isSharedCheck_860_ == 0)
{
v___x_854_ = v_r_850_;
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_result_852_);
lean_inc(v_id_851_);
lean_dec(v_r_850_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_apply_1(v_inst_849_, v_result_852_);
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 2);
lean_ctor_set(v___x_854_, 1, v___x_856_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_id_851_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object* v_inst_861_){
_start:
{
lean_object* v___f_862_; 
v___f_862_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_862_, 0, v_inst_861_);
return v___f_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object* v_00_u03b1_863_, lean_object* v_inst_864_){
_start:
{
lean_object* v___f_865_; 
v___f_865_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_865_, 0, v_inst_864_);
return v___f_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ofMessage_x3f(lean_object* v_x_866_){
_start:
{
if (lean_obj_tag(v_x_866_) == 2)
{
lean_object* v_id_867_; lean_object* v_result_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_876_; 
v_id_867_ = lean_ctor_get(v_x_866_, 0);
v_result_868_ = lean_ctor_get(v_x_866_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v_x_866_);
if (v_isSharedCheck_876_ == 0)
{
v___x_870_ = v_x_866_;
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_result_868_);
lean_inc(v_id_867_);
lean_dec(v_x_866_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 0);
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_id_867_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_result_868_);
v___x_873_ = v_reuseFailAlloc_875_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; 
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
}
}
else
{
lean_object* v___x_877_; 
lean_dec_ref(v_x_866_);
v___x_877_ = lean_box(0);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object* v_00_u03b1_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0));
return v___x_884_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__0(void){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_JsonRpc_instInhabitedResponseError_default(lean_box(0));
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object* v_a_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError___closed__0);
return v___x_887_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq___redArg(lean_object* v_inst_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
lean_object* v_id_891_; uint8_t v_code_892_; lean_object* v_message_893_; lean_object* v_data_x3f_894_; lean_object* v_id_895_; uint8_t v_code_896_; lean_object* v_message_897_; lean_object* v_data_x3f_898_; uint8_t v___x_899_; 
v_id_891_ = lean_ctor_get(v_x_889_, 0);
lean_inc(v_id_891_);
v_code_892_ = lean_ctor_get_uint8(v_x_889_, sizeof(void*)*3);
v_message_893_ = lean_ctor_get(v_x_889_, 1);
lean_inc_ref(v_message_893_);
v_data_x3f_894_ = lean_ctor_get(v_x_889_, 2);
lean_inc(v_data_x3f_894_);
lean_dec_ref(v_x_889_);
v_id_895_ = lean_ctor_get(v_x_890_, 0);
lean_inc(v_id_895_);
v_code_896_ = lean_ctor_get_uint8(v_x_890_, sizeof(void*)*3);
v_message_897_ = lean_ctor_get(v_x_890_, 1);
lean_inc_ref(v_message_897_);
v_data_x3f_898_ = lean_ctor_get(v_x_890_, 2);
lean_inc(v_data_x3f_898_);
lean_dec_ref(v_x_890_);
v___x_899_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_891_, v_id_895_);
lean_dec(v_id_895_);
lean_dec(v_id_891_);
if (v___x_899_ == 0)
{
lean_dec(v_data_x3f_898_);
lean_dec_ref(v_message_897_);
lean_dec(v_data_x3f_894_);
lean_dec_ref(v_message_893_);
lean_dec_ref(v_inst_888_);
return v___x_899_;
}
else
{
uint8_t v___x_900_; 
v___x_900_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_code_892_, v_code_896_);
if (v___x_900_ == 0)
{
lean_dec(v_data_x3f_898_);
lean_dec_ref(v_message_897_);
lean_dec(v_data_x3f_894_);
lean_dec_ref(v_message_893_);
lean_dec_ref(v_inst_888_);
return v___x_900_;
}
else
{
uint8_t v___x_901_; 
v___x_901_ = lean_string_dec_eq(v_message_893_, v_message_897_);
lean_dec_ref(v_message_897_);
lean_dec_ref(v_message_893_);
if (v___x_901_ == 0)
{
lean_dec(v_data_x3f_898_);
lean_dec(v_data_x3f_894_);
lean_dec_ref(v_inst_888_);
return v___x_901_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = l_Option_instBEq_beq___redArg(v_inst_888_, v_data_x3f_894_, v_data_x3f_898_);
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(lean_object* v_inst_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
uint8_t v_res_906_; lean_object* v_r_907_; 
v_res_906_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_903_, v_x_904_, v_x_905_);
v_r_907_ = lean_box(v_res_906_);
return v_r_907_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object* v_00_u03b1_908_, lean_object* v_inst_909_, lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_909_, v_x_910_, v_x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___boxed(lean_object* v_00_u03b1_913_, lean_object* v_inst_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
uint8_t v_res_917_; lean_object* v_r_918_; 
v_res_917_ = l_Lean_JsonRpc_instBEqResponseError_beq(v_00_u03b1_913_, v_inst_914_, v_x_915_, v_x_916_);
v_r_918_ = lean_box(v_res_917_);
return v_r_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object* v_inst_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_920_, 0, lean_box(0));
lean_closure_set(v___x_920_, 1, v_inst_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object* v_00_u03b1_921_, lean_object* v_inst_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_923_, 0, lean_box(0));
lean_closure_set(v___x_923_, 1, v_inst_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object* v_inst_924_, lean_object* v_r_925_){
_start:
{
lean_object* v_data_x3f_926_; 
v_data_x3f_926_ = lean_ctor_get(v_r_925_, 2);
lean_inc(v_data_x3f_926_);
if (lean_obj_tag(v_data_x3f_926_) == 0)
{
lean_object* v_id_927_; uint8_t v_code_928_; lean_object* v_message_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_937_; 
lean_dec_ref(v_inst_924_);
v_id_927_ = lean_ctor_get(v_r_925_, 0);
v_code_928_ = lean_ctor_get_uint8(v_r_925_, sizeof(void*)*3);
v_message_929_ = lean_ctor_get(v_r_925_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_r_925_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_r_925_, 2);
lean_dec(v_unused_938_);
v___x_931_ = v_r_925_;
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_message_929_);
lean_inc(v_id_927_);
lean_dec(v_r_925_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = lean_box(0);
if (v_isShared_932_ == 0)
{
lean_ctor_set_tag(v___x_931_, 3);
lean_ctor_set(v___x_931_, 2, v___x_933_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_id_927_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_message_929_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v___x_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*3, v_code_928_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
else
{
lean_object* v_id_939_; uint8_t v_code_940_; lean_object* v_message_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_957_; 
v_id_939_ = lean_ctor_get(v_r_925_, 0);
v_code_940_ = lean_ctor_get_uint8(v_r_925_, sizeof(void*)*3);
v_message_941_ = lean_ctor_get(v_r_925_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v_r_925_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; 
v_unused_958_ = lean_ctor_get(v_r_925_, 2);
lean_dec(v_unused_958_);
v___x_943_ = v_r_925_;
v_isShared_944_ = v_isSharedCheck_957_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_message_941_);
lean_inc(v_id_939_);
lean_dec(v_r_925_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_957_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_val_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_956_; 
v_val_945_ = lean_ctor_get(v_data_x3f_926_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v_data_x3f_926_);
if (v_isSharedCheck_956_ == 0)
{
v___x_947_ = v_data_x3f_926_;
v_isShared_948_ = v_isSharedCheck_956_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_val_945_);
lean_dec(v_data_x3f_926_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_956_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_apply_1(v_inst_924_, v_val_945_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_949_);
v___x_951_ = v___x_947_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_955_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_953_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 3);
lean_ctor_set(v___x_943_, 2, v___x_951_);
v___x_953_ = v___x_943_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_id_939_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_message_941_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v___x_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3, v_code_940_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object* v_inst_959_){
_start:
{
lean_object* v___f_960_; 
v___f_960_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_960_, 0, v_inst_959_);
return v___f_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object* v_00_u03b1_961_, lean_object* v_inst_962_){
_start:
{
lean_object* v___f_963_; 
v___f_963_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_963_, 0, v_inst_962_);
return v___f_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object* v_r_964_){
_start:
{
lean_object* v_id_965_; uint8_t v_code_966_; lean_object* v_message_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_975_; 
v_id_965_ = lean_ctor_get(v_r_964_, 0);
v_code_966_ = lean_ctor_get_uint8(v_r_964_, sizeof(void*)*3);
v_message_967_ = lean_ctor_get(v_r_964_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_r_964_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v_r_964_, 2);
lean_dec(v_unused_976_);
v___x_969_ = v_r_964_;
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_message_967_);
lean_inc(v_id_965_);
lean_dec(v_r_964_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = lean_box(0);
if (v_isShared_970_ == 0)
{
lean_ctor_set_tag(v___x_969_, 3);
lean_ctor_set(v___x_969_, 2, v___x_971_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_id_965_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_message_967_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v___x_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_974_, sizeof(void*)*3, v_code_966_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ofMessage_x3f(lean_object* v_x_979_){
_start:
{
if (lean_obj_tag(v_x_979_) == 3)
{
lean_object* v_id_980_; uint8_t v_code_981_; lean_object* v_message_982_; lean_object* v_data_x3f_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_991_; 
v_id_980_ = lean_ctor_get(v_x_979_, 0);
v_code_981_ = lean_ctor_get_uint8(v_x_979_, sizeof(void*)*3);
v_message_982_ = lean_ctor_get(v_x_979_, 1);
v_data_x3f_983_ = lean_ctor_get(v_x_979_, 2);
v_isSharedCheck_991_ = !lean_is_exclusive(v_x_979_);
if (v_isSharedCheck_991_ == 0)
{
v___x_985_ = v_x_979_;
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_data_x3f_983_);
lean_inc(v_message_982_);
lean_inc(v_id_980_);
lean_dec(v_x_979_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_991_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 0);
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_id_980_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_message_982_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_data_x3f_983_);
lean_ctor_set_uint8(v_reuseFailAlloc_990_, sizeof(void*)*3, v_code_981_);
v___x_988_ = v_reuseFailAlloc_990_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
}
else
{
lean_object* v___x_992_; 
lean_dec_ref(v_x_979_);
v___x_992_ = lean_box(0);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object* v_s_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v_s_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object* v_n_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v_n_997_);
return v___x_998_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_RequestID_lt(lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
switch(lean_obj_tag(v_x_1001_))
{
case 0:
{
if (lean_obj_tag(v_x_1002_) == 0)
{
lean_object* v_s_1003_; lean_object* v_s_1004_; uint8_t v___x_1005_; 
v_s_1003_ = lean_ctor_get(v_x_1001_, 0);
lean_inc_ref(v_s_1003_);
lean_dec_ref_known(v_x_1001_, 1);
v_s_1004_ = lean_ctor_get(v_x_1002_, 0);
lean_inc_ref(v_s_1004_);
lean_dec_ref_known(v_x_1002_, 1);
v___x_1005_ = lean_string_dec_lt(v_s_1003_, v_s_1004_);
lean_dec_ref(v_s_1004_);
lean_dec_ref(v_s_1003_);
return v___x_1005_;
}
else
{
uint8_t v___x_1006_; 
lean_dec_ref_known(v_x_1001_, 1);
lean_dec(v_x_1002_);
v___x_1006_ = 0;
return v___x_1006_;
}
}
case 1:
{
switch(lean_obj_tag(v_x_1002_))
{
case 1:
{
lean_object* v_n_1007_; lean_object* v_n_1008_; uint8_t v___x_1009_; 
v_n_1007_ = lean_ctor_get(v_x_1001_, 0);
lean_inc_ref(v_n_1007_);
lean_dec_ref_known(v_x_1001_, 1);
v_n_1008_ = lean_ctor_get(v_x_1002_, 0);
lean_inc_ref(v_n_1008_);
lean_dec_ref_known(v_x_1002_, 1);
v___x_1009_ = l_Lean_JsonNumber_lt(v_n_1007_, v_n_1008_);
return v___x_1009_;
}
case 0:
{
uint8_t v___x_1010_; 
lean_dec_ref_known(v_x_1002_, 1);
lean_dec_ref_known(v_x_1001_, 1);
v___x_1010_ = 1;
return v___x_1010_;
}
default: 
{
uint8_t v___x_1011_; 
lean_dec_ref_known(v_x_1001_, 1);
lean_dec(v_x_1002_);
v___x_1011_ = 0;
return v___x_1011_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_1002_))
{
case 1:
{
uint8_t v___x_1012_; 
lean_dec_ref_known(v_x_1002_, 1);
v___x_1012_ = 1;
return v___x_1012_;
}
case 0:
{
uint8_t v___x_1013_; 
lean_dec_ref_known(v_x_1002_, 1);
v___x_1013_ = 1;
return v___x_1013_;
}
default: 
{
uint8_t v___x_1014_; 
lean_dec(v_x_1002_);
v___x_1014_ = 0;
return v___x_1014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_lt___boxed(lean_object* v_x_1015_, lean_object* v_x_1016_){
_start:
{
uint8_t v_res_1017_; lean_object* v_r_1018_; 
v_res_1017_ = l_Lean_JsonRpc_RequestID_lt(v_x_1015_, v_x_1016_);
v_r_1018_ = lean_box(v_res_1017_);
return v_r_1018_;
}
}
static lean_object* _init_l_Lean_JsonRpc_RequestID_ltProp(void){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_box(0);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instLTRequestID(void){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_box(0);
return v___x_1020_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object* v_a_1021_, lean_object* v_b_1022_){
_start:
{
uint8_t v___x_1023_; 
v___x_1023_ = l_Lean_JsonRpc_RequestID_lt(v_a_1021_, v_b_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object* v_a_1024_, lean_object* v_b_1025_){
_start:
{
uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_res_1026_ = l_Lean_JsonRpc_instDecidableLtRequestID(v_a_1024_, v_b_1025_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object* v_j_1031_){
_start:
{
switch(lean_obj_tag(v_j_1031_))
{
case 3:
{
lean_object* v_s_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
v_s_1032_ = lean_ctor_get(v_j_1031_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_j_1031_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1034_ = v_j_1031_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_s_1032_);
lean_dec(v_j_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 0);
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_s_1032_);
v___x_1037_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
}
}
case 2:
{
lean_object* v_n_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
v_n_1041_ = lean_ctor_get(v_j_1031_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_j_1031_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1043_ = v_j_1031_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_n_1041_);
lean_dec(v_j_1031_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 1);
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_n_1041_);
v___x_1046_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
default: 
{
lean_object* v___x_1050_; 
lean_dec(v_j_1031_);
v___x_1050_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object* v_rid_1053_){
_start:
{
switch(lean_obj_tag(v_rid_1053_))
{
case 0:
{
lean_object* v_s_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
v_s_1054_ = lean_ctor_get(v_rid_1053_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_rid_1053_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v_rid_1053_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_s_1054_);
lean_dec(v_rid_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set_tag(v___x_1056_, 3);
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_s_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
case 1:
{
lean_object* v_n_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_n_1062_ = lean_ctor_get(v_rid_1053_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_rid_1053_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v_rid_1053_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_n_1062_);
lean_dec(v_rid_1053_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 2);
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_n_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
default: 
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_box(0);
return v___x_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object* v___x_1088_, lean_object* v___x_1089_, lean_object* v_m_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___y_1093_; 
v___x_1091_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_1090_))
{
case 0:
{
lean_object* v_id_1096_; lean_object* v_method_1097_; lean_object* v_params_x3f_1098_; lean_object* v___x_1099_; lean_object* v___y_1101_; 
lean_dec_ref(v___x_1089_);
v_id_1096_ = lean_ctor_get(v_m_1090_, 0);
lean_inc(v_id_1096_);
v_method_1097_ = lean_ctor_get(v_m_1090_, 1);
lean_inc_ref(v_method_1097_);
v_params_x3f_1098_ = lean_ctor_get(v_m_1090_, 2);
lean_inc(v_params_x3f_1098_);
lean_dec_ref_known(v_m_1090_, 3);
v___x_1099_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1096_))
{
case 0:
{
lean_object* v_s_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
v_s_1112_ = lean_ctor_get(v_id_1096_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_id_1096_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v_id_1096_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_s_1112_);
lean_dec(v_id_1096_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 3);
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_s_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
v___y_1101_ = v___x_1117_;
goto v___jp_1100_;
}
}
}
case 1:
{
lean_object* v_n_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_n_1120_ = lean_ctor_get(v_id_1096_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_id_1096_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v_id_1096_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_n_1120_);
lean_dec(v_id_1096_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 2);
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_n_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
v___y_1101_ = v___x_1125_;
goto v___jp_1100_;
}
}
}
default: 
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_box(0);
v___y_1101_ = v___x_1128_;
goto v___jp_1100_;
}
}
v___jp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1099_);
lean_ctor_set(v___x_1102_, 1, v___y_1101_);
v___x_1103_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_method_1097_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1102_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1110_ = l_Lean_Json_opt___redArg(v___x_1088_, v___x_1109_, v_params_x3f_1098_);
v___x_1111_ = l_List_appendTR___redArg(v___x_1108_, v___x_1110_);
v___y_1093_ = v___x_1111_;
goto v___jp_1092_;
}
}
case 1:
{
lean_object* v_method_1129_; lean_object* v_params_x3f_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v___x_1089_);
v_method_1129_ = lean_ctor_get(v_m_1090_, 0);
v_params_x3f_1130_ = lean_ctor_get(v_m_1090_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_m_1090_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1132_ = v_m_1090_;
v_isShared_1133_ = v_isSharedCheck_1142_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_params_x3f_1130_);
lean_inc(v_method_1129_);
lean_dec(v_m_1090_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1142_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1134_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1135_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_method_1129_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 0);
lean_ctor_set(v___x_1132_, 1, v___x_1135_);
lean_ctor_set(v___x_1132_, 0, v___x_1134_);
v___x_1137_ = v___x_1132_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1139_ = l_Lean_Json_opt___redArg(v___x_1088_, v___x_1138_, v_params_x3f_1130_);
v___x_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1137_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___y_1093_ = v___x_1140_;
goto v___jp_1092_;
}
}
}
case 2:
{
lean_object* v_id_1143_; lean_object* v_result_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v___x_1089_);
lean_dec_ref(v___x_1088_);
v_id_1143_ = lean_ctor_get(v_m_1090_, 0);
v_result_1144_ = lean_ctor_get(v_m_1090_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_m_1090_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1146_ = v_m_1090_;
v_isShared_1147_ = v_isSharedCheck_1176_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_result_1144_);
lean_inc(v_id_1143_);
lean_dec(v_m_1090_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1176_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___y_1150_; 
v___x_1148_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1143_))
{
case 0:
{
lean_object* v_s_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_s_1159_ = lean_ctor_get(v_id_1143_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_id_1143_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v_id_1143_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_s_1159_);
lean_dec(v_id_1143_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set_tag(v___x_1161_, 3);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_s_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
v___y_1150_ = v___x_1164_;
goto v___jp_1149_;
}
}
}
case 1:
{
lean_object* v_n_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_n_1167_ = lean_ctor_get(v_id_1143_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_id_1143_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v_id_1143_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_n_1167_);
lean_dec(v_id_1143_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 2);
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_n_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
v___y_1150_ = v___x_1172_;
goto v___jp_1149_;
}
}
}
default: 
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_box(0);
v___y_1150_ = v___x_1175_;
goto v___jp_1149_;
}
}
v___jp_1149_:
{
lean_object* v___x_1152_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set_tag(v___x_1146_, 0);
lean_ctor_set(v___x_1146_, 1, v___y_1150_);
lean_ctor_set(v___x_1146_, 0, v___x_1148_);
v___x_1152_ = v___x_1146_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___y_1150_);
v___x_1152_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1153_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v_result_1144_);
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1152_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___y_1093_ = v___x_1157_;
goto v___jp_1092_;
}
}
}
}
default: 
{
lean_object* v_id_1177_; uint8_t v_code_1178_; lean_object* v_message_1179_; lean_object* v_data_x3f_1180_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___x_1200_; lean_object* v___y_1202_; 
lean_dec_ref(v___x_1088_);
v_id_1177_ = lean_ctor_get(v_m_1090_, 0);
lean_inc(v_id_1177_);
v_code_1178_ = lean_ctor_get_uint8(v_m_1090_, sizeof(void*)*3);
v_message_1179_ = lean_ctor_get(v_m_1090_, 1);
lean_inc_ref(v_message_1179_);
v_data_x3f_1180_ = lean_ctor_get(v_m_1090_, 2);
lean_inc(v_data_x3f_1180_);
lean_dec_ref_known(v_m_1090_, 3);
v___x_1200_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1177_))
{
case 0:
{
lean_object* v_s_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
v_s_1218_ = lean_ctor_get(v_id_1177_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_id_1177_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v_id_1177_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_s_1218_);
lean_dec(v_id_1177_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 3);
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_s_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
v___y_1202_ = v___x_1223_;
goto v___jp_1201_;
}
}
}
case 1:
{
lean_object* v_n_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_n_1226_ = lean_ctor_get(v_id_1177_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_id_1177_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v_id_1177_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_n_1226_);
lean_dec(v_id_1177_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set_tag(v___x_1228_, 2);
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_n_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
v___y_1202_ = v___x_1231_;
goto v___jp_1201_;
}
}
}
default: 
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_box(0);
v___y_1202_ = v___x_1234_;
goto v___jp_1201_;
}
}
v___jp_1181_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
lean_inc(v___y_1185_);
lean_inc_ref(v___y_1184_);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___y_1184_);
lean_ctor_set(v___x_1186_, 1, v___y_1185_);
v___x_1187_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1188_, 0, v_message_1179_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1186_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1194_ = l_Lean_Json_opt___redArg(v___x_1089_, v___x_1193_, v_data_x3f_1180_);
v___x_1195_ = l_List_appendTR___redArg(v___x_1192_, v___x_1194_);
v___x_1196_ = l_Lean_Json_mkObj(v___x_1195_);
lean_dec(v___x_1195_);
lean_inc_ref(v___y_1182_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___y_1182_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v___x_1190_);
v___x_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___y_1183_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___y_1093_ = v___x_1199_;
goto v___jp_1092_;
}
v___jp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1200_);
lean_ctor_set(v___x_1203_, 1, v___y_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1205_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_1178_)
{
case 0:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1206_;
goto v___jp_1181_;
}
case 1:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1207_;
goto v___jp_1181_;
}
case 2:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1208_;
goto v___jp_1181_;
}
case 3:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1209_;
goto v___jp_1181_;
}
case 4:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1210_;
goto v___jp_1181_;
}
case 5:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1211_;
goto v___jp_1181_;
}
case 6:
{
lean_object* v___x_1212_; 
v___x_1212_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1212_;
goto v___jp_1181_;
}
case 7:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1213_;
goto v___jp_1181_;
}
case 8:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1214_;
goto v___jp_1181_;
}
case 9:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1215_;
goto v___jp_1181_;
}
case 10:
{
lean_object* v___x_1216_; 
v___x_1216_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1216_;
goto v___jp_1181_;
}
default: 
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_1182_ = v___x_1204_;
v___y_1183_ = v___x_1203_;
v___y_1184_ = v___x_1205_;
v___y_1185_ = v___x_1217_;
goto v___jp_1181_;
}
}
}
}
}
v___jp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1091_);
lean_ctor_set(v___x_1094_, 1, v___y_1093_);
v___x_1095_ = l_Lean_Json_mkObj(v___x_1094_);
lean_dec_ref_known(v___x_1094_, 2);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object* v___f_1244_, lean_object* v___f_1245_, lean_object* v___x_1246_, lean_object* v___x_1247_, lean_object* v_j_1248_){
_start:
{
uint8_t v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1248_);
v___x_1264_ = l_Lean_Json_getObjVal_x3f(v_j_1248_, v___x_1263_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_j_1248_);
lean_dec_ref(v___x_1247_);
lean_dec_ref(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v___f_1244_);
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
else
{
lean_object* v_a_1273_; 
v_a_1273_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1264_, 1);
if (lean_obj_tag(v_a_1273_) == 3)
{
lean_object* v_s_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v_s_1274_ = lean_ctor_get(v_a_1273_, 0);
lean_inc_ref(v_s_1274_);
lean_dec_ref_known(v_a_1273_, 1);
v___x_1275_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1276_ = lean_string_dec_eq(v_s_1274_, v___x_1275_);
lean_dec_ref(v_s_1274_);
if (v___x_1276_ == 0)
{
lean_dec(v_j_1248_);
lean_dec_ref(v___x_1247_);
lean_dec_ref(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v___f_1244_);
goto v___jp_1249_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1248_);
v___x_1278_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1248_, v___f_1244_, v___x_1277_);
if (lean_obj_tag(v___x_1278_) == 0)
{
goto v___jp_1335_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_a_1362_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1362_);
v___x_1363_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1246_);
lean_inc(v_j_1248_);
v___x_1364_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1248_, v___x_1246_, v___x_1363_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_dec_ref_known(v___x_1364_, 1);
lean_dec(v_a_1362_);
goto v___jp_1335_;
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref_known(v___x_1278_, 1);
lean_dec_ref(v___x_1246_);
lean_dec_ref(v___f_1245_);
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1386_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1386_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___y_1370_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1376_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1248_, v___x_1247_, v___x_1375_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v___x_1377_; 
lean_dec_ref_known(v___x_1376_, 1);
v___x_1377_ = lean_box(0);
v___y_1370_ = v___x_1377_;
goto v___jp_1369_;
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
v_a_1378_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1376_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1376_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
v___y_1370_ = v___x_1383_;
goto v___jp_1369_;
}
}
}
v___jp_1369_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1371_, 0, v_a_1362_);
lean_ctor_set(v___x_1371_, 1, v_a_1365_);
lean_ctor_set(v___x_1371_, 2, v___y_1370_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1371_);
v___x_1373_ = v___x_1367_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
v___jp_1279_:
{
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_j_1248_);
lean_dec_ref(v___x_1246_);
lean_dec_ref(v___f_1245_);
v_a_1280_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1278_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1278_);
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
v_a_1288_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1289_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1290_ = l_Lean_Json_getObjVal_x3f(v_j_1248_, v___x_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_a_1288_);
lean_dec_ref(v___x_1246_);
lean_dec_ref(v___f_1245_);
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
lean_inc_n(v_a_1299_, 2);
lean_dec_ref_known(v___x_1290_, 1);
v___x_1300_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1301_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1299_, v___f_1245_, v___x_1300_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_a_1299_);
lean_dec(v_a_1288_);
lean_dec_ref(v___x_1246_);
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
v___x_1311_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1299_);
v___x_1312_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1299_, v___x_1246_, v___x_1311_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec(v_a_1310_);
lean_dec(v_a_1299_);
lean_dec(v_a_1288_);
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_a_1321_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1322_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1323_ = l_Lean_Json_getObjVal_x3f(v_a_1299_, v___x_1322_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
lean_dec_ref_known(v___x_1323_, 1);
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_unbox(v_a_1310_);
lean_dec(v_a_1310_);
v___y_1252_ = v___x_1325_;
v___y_1253_ = v_a_1288_;
v___y_1254_ = v_a_1321_;
v___y_1255_ = v___x_1324_;
goto v___jp_1251_;
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1334_; 
v_a_1326_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1328_ = v___x_1323_;
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1323_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_unbox(v_a_1310_);
lean_dec(v_a_1310_);
v___y_1252_ = v___x_1332_;
v___y_1253_ = v_a_1288_;
v___y_1254_ = v_a_1321_;
v___y_1255_ = v___x_1331_;
goto v___jp_1251_;
}
}
}
}
}
}
}
}
v___jp_1335_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1246_);
lean_inc(v_j_1248_);
v___x_1337_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1248_, v___x_1246_, v___x_1336_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_dec_ref_known(v___x_1337_, 1);
lean_dec_ref(v___x_1247_);
if (lean_obj_tag(v___x_1278_) == 0)
{
goto v___jp_1279_;
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_a_1338_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1338_);
v___x_1339_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1248_);
v___x_1340_ = l_Lean_Json_getObjVal_x3f(v_j_1248_, v___x_1339_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_dec_ref_known(v___x_1340_, 1);
lean_dec(v_a_1338_);
goto v___jp_1279_;
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref_known(v___x_1278_, 1);
lean_dec(v_j_1248_);
lean_dec_ref(v___x_1246_);
lean_dec_ref(v___f_1245_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1349_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_a_1338_);
lean_ctor_set(v___x_1345_, 1, v_a_1341_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1345_);
v___x_1347_ = v___x_1343_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
lean_dec_ref(v___x_1278_);
lean_dec_ref(v___x_1246_);
lean_dec_ref(v___f_1245_);
v_a_1350_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1337_, 1);
v___x_1351_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1352_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1248_, v___x_1247_, v___x_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v___x_1353_; 
lean_dec_ref_known(v___x_1352_, 1);
v___x_1353_ = lean_box(0);
v___y_1259_ = v_a_1350_;
v___y_1260_ = v___x_1353_;
goto v___jp_1258_;
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_a_1354_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1352_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1352_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
v___y_1259_ = v_a_1350_;
v___y_1260_ = v___x_1359_;
goto v___jp_1258_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1273_);
lean_dec(v_j_1248_);
lean_dec_ref(v___x_1247_);
lean_dec_ref(v___x_1246_);
lean_dec_ref(v___f_1245_);
lean_dec_ref(v___f_1244_);
goto v___jp_1249_;
}
}
v___jp_1249_:
{
lean_object* v___x_1250_; 
v___x_1250_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1));
return v___x_1250_;
}
v___jp_1251_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1256_, 0, v___y_1253_);
lean_ctor_set(v___x_1256_, 1, v___y_1254_);
lean_ctor_set(v___x_1256_, 2, v___y_1255_);
lean_ctor_set_uint8(v___x_1256_, sizeof(void*)*3, v___y_1252_);
v___x_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
return v___x_1257_;
}
v___jp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___y_1259_);
lean_ctor_set(v___x_1261_, 1, v___y_1260_);
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object* v___x_1400_, lean_object* v_inst_1401_, lean_object* v_j_1402_){
_start:
{
lean_object* v_method_1406_; lean_object* v_params_x3f_1407_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1402_);
v___x_1430_ = l_Lean_Json_getObjVal_x3f(v_j_1402_, v___x_1429_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec(v_j_1402_);
lean_dec_ref(v_inst_1401_);
lean_dec_ref(v___x_1400_);
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
else
{
lean_object* v_a_1439_; 
v_a_1439_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1430_, 1);
if (lean_obj_tag(v_a_1439_) == 3)
{
lean_object* v_s_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_s_1440_ = lean_ctor_get(v_a_1439_, 0);
lean_inc_ref(v_s_1440_);
lean_dec_ref_known(v_a_1439_, 1);
v___x_1441_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1442_ = lean_string_dec_eq(v_s_1440_, v___x_1441_);
lean_dec_ref(v_s_1440_);
if (v___x_1442_ == 0)
{
lean_dec(v_j_1402_);
lean_dec_ref(v_inst_1401_);
lean_dec_ref(v___x_1400_);
goto v___jp_1427_;
}
else
{
lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___f_1443_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___closed__0));
v___x_1444_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__0));
v___x_1445_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__1));
v___f_1446_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___closed__0));
v___x_1447_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1402_);
v___x_1448_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1402_, v___f_1443_, v___x_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
goto v___jp_1489_;
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1402_);
v___x_1507_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1402_, v___x_1444_, v___x_1506_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_dec_ref_known(v___x_1507_, 1);
goto v___jp_1489_;
}
else
{
lean_dec_ref_known(v___x_1507_, 1);
lean_dec_ref_known(v___x_1448_, 1);
lean_dec(v_j_1402_);
lean_dec_ref(v_inst_1401_);
lean_dec_ref(v___x_1400_);
goto v___jp_1403_;
}
}
v___jp_1449_:
{
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_j_1402_);
v_a_1450_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1448_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1448_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref_known(v___x_1448_, 1);
v___x_1458_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1459_ = l_Lean_Json_getObjVal_x3f(v_j_1402_, v___x_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
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
lean_object* v_a_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_a_1468_ = lean_ctor_get(v___x_1459_, 0);
lean_inc_n(v_a_1468_, 2);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1469_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1470_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1468_, v___f_1446_, v___x_1469_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_a_1468_);
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec_ref_known(v___x_1470_, 1);
v___x_1479_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1480_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1468_, v___x_1444_, v___x_1479_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_dec_ref_known(v___x_1480_, 1);
goto v___jp_1403_;
}
}
}
}
}
v___jp_1489_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1402_);
v___x_1491_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1402_, v___x_1444_, v___x_1490_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_dec_ref_known(v___x_1491_, 1);
lean_dec_ref(v_inst_1401_);
lean_dec_ref(v___x_1400_);
if (lean_obj_tag(v___x_1448_) == 0)
{
goto v___jp_1449_;
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1402_);
v___x_1493_ = l_Lean_Json_getObjVal_x3f(v_j_1402_, v___x_1492_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_dec_ref_known(v___x_1493_, 1);
goto v___jp_1449_;
}
else
{
lean_dec_ref_known(v___x_1493_, 1);
lean_dec_ref_known(v___x_1448_, 1);
lean_dec(v_j_1402_);
goto v___jp_1403_;
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec_ref(v___x_1448_);
v_a_1494_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1495_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1496_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1402_, v___x_1445_, v___x_1495_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v___x_1497_; 
lean_dec_ref_known(v___x_1496_, 1);
v___x_1497_ = lean_box(0);
v_method_1406_ = v_a_1494_;
v_params_x3f_1407_ = v___x_1497_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
v_a_1498_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1496_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1496_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
v_method_1406_ = v_a_1494_;
v_params_x3f_1407_ = v___x_1503_;
goto v___jp_1405_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1439_);
lean_dec(v_j_1402_);
lean_dec_ref(v_inst_1401_);
lean_dec_ref(v___x_1400_);
goto v___jp_1427_;
}
}
v___jp_1403_:
{
lean_object* v___x_1404_; 
v___x_1404_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1));
return v___x_1404_;
}
v___jp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = l_Option_toJson___redArg(v___x_1400_, v_params_x3f_1407_);
v___x_1409_ = lean_apply_1(v_inst_1401_, v___x_1408_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec_ref(v_method_1406_);
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1426_; 
v_a_1418_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1420_ = v___x_1409_;
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1409_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_method_1406_);
lean_ctor_set(v___x_1422_, 1, v_a_1418_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1422_);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
v___jp_1427_:
{
lean_object* v___x_1428_; 
v___x_1428_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2));
return v___x_1428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object* v_inst_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___f_1510_; 
v___x_1509_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___f_1510_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1510_, 0, v___x_1509_);
lean_closure_set(v___f_1510_, 1, v_inst_1508_);
return v___f_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object* v_00_u03b1_1511_, lean_object* v_inst_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_JsonRpc_instFromJsonNotification___redArg(v_inst_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx(lean_object* v_x_1514_){
_start:
{
switch(lean_obj_tag(v_x_1514_))
{
case 0:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_unsigned_to_nat(0u);
return v___x_1515_;
}
case 1:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_unsigned_to_nat(1u);
return v___x_1516_;
}
case 2:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_unsigned_to_nat(2u);
return v___x_1517_;
}
default: 
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_unsigned_to_nat(3u);
return v___x_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___boxed(lean_object* v_x_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_JsonRpc_MessageMetaData_ctorIdx(v_x_1519_);
lean_dec_ref(v_x_1519_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(lean_object* v_t_1521_, lean_object* v_k_1522_){
_start:
{
switch(lean_obj_tag(v_t_1521_))
{
case 0:
{
lean_object* v_id_1523_; lean_object* v_method_1524_; lean_object* v___x_1525_; 
v_id_1523_ = lean_ctor_get(v_t_1521_, 0);
lean_inc(v_id_1523_);
v_method_1524_ = lean_ctor_get(v_t_1521_, 1);
lean_inc_ref(v_method_1524_);
lean_dec_ref_known(v_t_1521_, 2);
v___x_1525_ = lean_apply_2(v_k_1522_, v_id_1523_, v_method_1524_);
return v___x_1525_;
}
case 1:
{
lean_object* v_method_1526_; lean_object* v___x_1527_; 
v_method_1526_ = lean_ctor_get(v_t_1521_, 0);
lean_inc_ref(v_method_1526_);
lean_dec_ref_known(v_t_1521_, 1);
v___x_1527_ = lean_apply_1(v_k_1522_, v_method_1526_);
return v___x_1527_;
}
case 2:
{
lean_object* v_id_1528_; lean_object* v___x_1529_; 
v_id_1528_ = lean_ctor_get(v_t_1521_, 0);
lean_inc(v_id_1528_);
lean_dec_ref_known(v_t_1521_, 1);
v___x_1529_ = lean_apply_1(v_k_1522_, v_id_1528_);
return v___x_1529_;
}
default: 
{
lean_object* v_id_1530_; uint8_t v_code_1531_; lean_object* v_message_1532_; lean_object* v_data_x3f_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_id_1530_ = lean_ctor_get(v_t_1521_, 0);
lean_inc(v_id_1530_);
v_code_1531_ = lean_ctor_get_uint8(v_t_1521_, sizeof(void*)*3);
v_message_1532_ = lean_ctor_get(v_t_1521_, 1);
lean_inc_ref(v_message_1532_);
v_data_x3f_1533_ = lean_ctor_get(v_t_1521_, 2);
lean_inc(v_data_x3f_1533_);
lean_dec_ref_known(v_t_1521_, 3);
v___x_1534_ = lean_box(v_code_1531_);
v___x_1535_ = lean_apply_4(v_k_1522_, v_id_1530_, v___x_1534_, v_message_1532_, v_data_x3f_1533_);
return v___x_1535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim(lean_object* v_motive_1536_, lean_object* v_ctorIdx_1537_, lean_object* v_t_1538_, lean_object* v_h_1539_, lean_object* v_k_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1538_, v_k_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(lean_object* v_motive_1542_, lean_object* v_ctorIdx_1543_, lean_object* v_t_1544_, lean_object* v_h_1545_, lean_object* v_k_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_JsonRpc_MessageMetaData_ctorElim(v_motive_1542_, v_ctorIdx_1543_, v_t_1544_, v_h_1545_, v_k_1546_);
lean_dec(v_ctorIdx_1543_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim___redArg(lean_object* v_t_1548_, lean_object* v_request_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1548_, v_request_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim(lean_object* v_motive_1551_, lean_object* v_t_1552_, lean_object* v_h_1553_, lean_object* v_request_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1552_, v_request_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(lean_object* v_t_1556_, lean_object* v_notification_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1556_, v_notification_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim(lean_object* v_motive_1559_, lean_object* v_t_1560_, lean_object* v_h_1561_, lean_object* v_notification_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1560_, v_notification_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(lean_object* v_t_1564_, lean_object* v_response_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1564_, v_response_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim(lean_object* v_motive_1567_, lean_object* v_t_1568_, lean_object* v_h_1569_, lean_object* v_response_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1568_, v_response_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim___redArg(lean_object* v_t_1572_, lean_object* v_responseError_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1572_, v_responseError_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim(lean_object* v_motive_1575_, lean_object* v_t_1576_, lean_object* v_h_1577_, lean_object* v_responseError_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1576_, v_responseError_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_metaData(lean_object* v_x_1585_){
_start:
{
switch(lean_obj_tag(v_x_1585_))
{
case 0:
{
lean_object* v_id_1586_; lean_object* v_method_1587_; lean_object* v___x_1588_; 
v_id_1586_ = lean_ctor_get(v_x_1585_, 0);
lean_inc(v_id_1586_);
v_method_1587_ = lean_ctor_get(v_x_1585_, 1);
lean_inc_ref(v_method_1587_);
lean_dec_ref_known(v_x_1585_, 3);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_id_1586_);
lean_ctor_set(v___x_1588_, 1, v_method_1587_);
return v___x_1588_;
}
case 1:
{
lean_object* v_method_1589_; lean_object* v___x_1590_; 
v_method_1589_ = lean_ctor_get(v_x_1585_, 0);
lean_inc_ref(v_method_1589_);
lean_dec_ref_known(v_x_1585_, 2);
v___x_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1590_, 0, v_method_1589_);
return v___x_1590_;
}
case 2:
{
lean_object* v_id_1591_; lean_object* v___x_1592_; 
v_id_1591_ = lean_ctor_get(v_x_1585_, 0);
lean_inc(v_id_1591_);
lean_dec_ref_known(v_x_1585_, 2);
v___x_1592_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1592_, 0, v_id_1591_);
return v___x_1592_;
}
default: 
{
lean_object* v_id_1593_; uint8_t v_code_1594_; lean_object* v_message_1595_; lean_object* v_data_x3f_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
v_id_1593_ = lean_ctor_get(v_x_1585_, 0);
v_code_1594_ = lean_ctor_get_uint8(v_x_1585_, sizeof(void*)*3);
v_message_1595_ = lean_ctor_get(v_x_1585_, 1);
v_data_x3f_1596_ = lean_ctor_get(v_x_1585_, 2);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_x_1585_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v_x_1585_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_data_x3f_1596_);
lean_inc(v_message_1595_);
lean_inc(v_id_1593_);
lean_dec(v_x_1585_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_id_1593_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_message_1595_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_data_x3f_1596_);
lean_ctor_set_uint8(v_reuseFailAlloc_1602_, sizeof(void*)*3, v_code_1594_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_toMessage(lean_object* v_x_1604_){
_start:
{
switch(lean_obj_tag(v_x_1604_))
{
case 0:
{
lean_object* v_id_1605_; lean_object* v_method_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_id_1605_ = lean_ctor_get(v_x_1604_, 0);
lean_inc(v_id_1605_);
v_method_1606_ = lean_ctor_get(v_x_1604_, 1);
lean_inc_ref(v_method_1606_);
lean_dec_ref_known(v_x_1604_, 2);
v___x_1607_ = lean_box(0);
v___x_1608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1608_, 0, v_id_1605_);
lean_ctor_set(v___x_1608_, 1, v_method_1606_);
lean_ctor_set(v___x_1608_, 2, v___x_1607_);
return v___x_1608_;
}
case 1:
{
lean_object* v_method_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v_method_1609_ = lean_ctor_get(v_x_1604_, 0);
lean_inc_ref(v_method_1609_);
lean_dec_ref_known(v_x_1604_, 1);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_method_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
return v___x_1611_;
}
case 2:
{
lean_object* v_id_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_id_1612_ = lean_ctor_get(v_x_1604_, 0);
lean_inc(v_id_1612_);
lean_dec_ref_known(v_x_1604_, 1);
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1614_, 0, v_id_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
return v___x_1614_;
}
default: 
{
lean_object* v_id_1615_; uint8_t v_code_1616_; lean_object* v_message_1617_; lean_object* v_data_x3f_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
v_id_1615_ = lean_ctor_get(v_x_1604_, 0);
v_code_1616_ = lean_ctor_get_uint8(v_x_1604_, sizeof(void*)*3);
v_message_1617_ = lean_ctor_get(v_x_1604_, 1);
v_data_x3f_1618_ = lean_ctor_get(v_x_1604_, 2);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_x_1604_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v_x_1604_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_data_x3f_1618_);
lean_inc(v_message_1617_);
lean_inc(v_id_1615_);
lean_dec(v_x_1604_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_id_1615_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_message_1617_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_data_x3f_1618_);
lean_ctor_set_uint8(v_reuseFailAlloc_1624_, sizeof(void*)*3, v_code_1616_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(lean_object* v_a_1629_){
_start:
{
lean_object* v_fst_1630_; lean_object* v_snd_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v_fst_1630_ = lean_ctor_get(v_a_1629_, 0);
v_snd_1631_ = lean_ctor_get(v_a_1629_, 1);
v___x_1632_ = lean_string_utf8_byte_size(v_fst_1630_);
v___x_1633_ = lean_nat_dec_eq(v_snd_1631_, v___x_1632_);
if (v___x_1633_ == 0)
{
uint32_t v___x_1634_; uint32_t v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = lean_string_utf8_get_fast(v_fst_1630_, v_snd_1631_);
v___x_1635_ = 34;
v___x_1636_ = lean_uint32_dec_eq(v___x_1634_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1));
v___x_1638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_a_1629_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
return v___x_1638_;
}
else
{
if (v___x_1633_ == 0)
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1648_; 
lean_inc(v_snd_1631_);
lean_inc(v_fst_1630_);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_a_1629_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; lean_object* v_unused_1650_; 
v_unused_1649_ = lean_ctor_get(v_a_1629_, 1);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_a_1629_, 0);
lean_dec(v_unused_1650_);
v___x_1640_ = v_a_1629_;
v_isShared_1641_ = v_isSharedCheck_1648_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v_a_1629_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1648_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = lean_string_utf8_next_fast(v_fst_1630_, v_snd_1631_);
lean_dec(v_snd_1631_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_fst_1630_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_1646_ = l_Lean_Json_Parser_strCore(v___x_1645_, v___x_1644_);
return v___x_1646_;
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1652_, 0, v_a_1629_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
return v___x_1652_;
}
}
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_a_1629_);
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
lean_object* v_snd_1672_; lean_object* v_snd_1673_; uint8_t v___x_1674_; 
v_snd_1672_ = lean_ctor_get(v_a_1655_, 1);
lean_inc(v_snd_1672_);
lean_dec_ref(v_a_1655_);
v_snd_1673_ = lean_ctor_get(v_pos_1667_, 1);
v___x_1674_ = lean_nat_dec_eq(v_snd_1672_, v_snd_1673_);
lean_dec(v_snd_1672_);
if (v___x_1674_ == 0)
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
lean_object* v_snd_1694_; uint8_t v___x_1695_; 
v_snd_1694_ = lean_ctor_get(v_pos_1689_, 1);
v___x_1695_ = lean_nat_dec_eq(v_snd_1673_, v_snd_1694_);
lean_dec(v_snd_1673_);
if (v___x_1695_ == 0)
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
lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v_fst_1861_; lean_object* v_snd_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v_fst_1861_ = lean_ctor_get(v_a_1835_, 0);
v_snd_1862_ = lean_ctor_get(v_a_1835_, 1);
v___x_1863_ = lean_string_utf8_byte_size(v_fst_1861_);
v___x_1864_ = lean_nat_dec_eq(v_snd_1862_, v___x_1863_);
if (v___x_1864_ == 0)
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
lean_object* v_fst_1877_; lean_object* v_snd_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v_fst_1877_ = lean_ctor_get(v_pos_1872_, 0);
v_snd_1878_ = lean_ctor_get(v_pos_1872_, 1);
v___x_1879_ = lean_string_utf8_byte_size(v_fst_1877_);
v___x_1880_ = lean_nat_dec_eq(v_snd_1878_, v___x_1879_);
if (v___x_1880_ == 0)
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
lean_object* v_fst_1970_; lean_object* v_snd_1971_; uint8_t v___y_1973_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v_fst_1970_ = lean_ctor_get(v_pos_1966_, 0);
v_snd_1971_ = lean_ctor_get(v_pos_1966_, 1);
v___x_2012_ = lean_string_utf8_byte_size(v_fst_1970_);
v___x_2013_ = lean_nat_dec_eq(v_snd_1971_, v___x_2012_);
if (v___x_2013_ == 0)
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
lean_object* v_fst_1989_; lean_object* v_snd_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v_fst_1989_ = lean_ctor_get(v_pos_1985_, 0);
v_snd_1990_ = lean_ctor_get(v_pos_1985_, 1);
v___x_1991_ = lean_string_utf8_byte_size(v_fst_1989_);
v___x_1992_ = lean_nat_dec_eq(v_snd_1990_, v___x_1991_);
if (v___x_1992_ == 0)
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
lean_object* v_fst_2036_; lean_object* v_snd_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v_fst_2036_ = lean_ctor_get(v_pos_2026_, 0);
v_snd_2037_ = lean_ctor_get(v_pos_2026_, 1);
v___x_2038_ = lean_string_utf8_byte_size(v_fst_2036_);
v___x_2039_ = lean_nat_dec_eq(v_snd_2037_, v___x_2038_);
if (v___x_2039_ == 0)
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
lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v_fst_2051_ = lean_ctor_get(v_pos_2047_, 0);
v_snd_2052_ = lean_ctor_get(v_pos_2047_, 1);
v___x_2053_ = lean_string_utf8_byte_size(v_fst_2051_);
v___x_2054_ = lean_nat_dec_eq(v_snd_2052_, v___x_2053_);
if (v___x_2054_ == 0)
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
lean_object* v_fst_2066_; lean_object* v_snd_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_fst_2066_ = lean_ctor_get(v_pos_2062_, 0);
v_snd_2067_ = lean_ctor_get(v_pos_2062_, 1);
v___x_2068_ = lean_string_utf8_byte_size(v_fst_2066_);
v___x_2069_ = lean_nat_dec_eq(v_snd_2067_, v___x_2068_);
if (v___x_2069_ == 0)
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
lean_object* v_fst_2099_; lean_object* v_snd_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
lean_dec(v_res_2078_);
lean_del_object(v___x_2064_);
v_fst_2099_ = lean_ctor_get(v_pos_2077_, 0);
v_snd_2100_ = lean_ctor_get(v_pos_2077_, 1);
v___x_2101_ = lean_string_utf8_byte_size(v_fst_2099_);
v___x_2102_ = lean_nat_dec_eq(v_snd_2100_, v___x_2101_);
if (v___x_2102_ == 0)
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx(uint8_t v_x_2228_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_JsonRpc_MessageDirection_ctorIdx(v_x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx___boxed(lean_object* v_x_2230_){
_start:
{
uint8_t v_x_4__boxed_2231_; lean_object* v_res_2232_; 
v_x_4__boxed_2231_ = lean_unbox(v_x_2230_);
v_res_2232_ = l_Lean_JsonRpc_MessageDirection_toCtorIdx(v_x_4__boxed_2231_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object* v_k_2233_){
_start:
{
lean_inc(v_k_2233_);
return v_k_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object* v_k_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(v_k_2234_);
lean_dec(v_k_2234_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object* v_motive_2236_, lean_object* v_ctorIdx_2237_, uint8_t v_t_2238_, lean_object* v_h_2239_, lean_object* v_k_2240_){
_start:
{
lean_inc(v_k_2240_);
return v_k_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object* v_motive_2241_, lean_object* v_ctorIdx_2242_, lean_object* v_t_2243_, lean_object* v_h_2244_, lean_object* v_k_2245_){
_start:
{
uint8_t v_t_boxed_2246_; lean_object* v_res_2247_; 
v_t_boxed_2246_ = lean_unbox(v_t_2243_);
v_res_2247_ = l_Lean_JsonRpc_MessageDirection_ctorElim(v_motive_2241_, v_ctorIdx_2242_, v_t_boxed_2246_, v_h_2244_, v_k_2245_);
lean_dec(v_k_2245_);
lean_dec(v_ctorIdx_2242_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object* v_clientToServer_2248_){
_start:
{
lean_inc(v_clientToServer_2248_);
return v_clientToServer_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object* v_clientToServer_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(v_clientToServer_2249_);
lean_dec(v_clientToServer_2249_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object* v_motive_2251_, uint8_t v_t_2252_, lean_object* v_h_2253_, lean_object* v_clientToServer_2254_){
_start:
{
lean_inc(v_clientToServer_2254_);
return v_clientToServer_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object* v_motive_2255_, lean_object* v_t_2256_, lean_object* v_h_2257_, lean_object* v_clientToServer_2258_){
_start:
{
uint8_t v_t_boxed_2259_; lean_object* v_res_2260_; 
v_t_boxed_2259_ = lean_unbox(v_t_2256_);
v_res_2260_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(v_motive_2255_, v_t_boxed_2259_, v_h_2257_, v_clientToServer_2258_);
lean_dec(v_clientToServer_2258_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object* v_serverToClient_2261_){
_start:
{
lean_inc(v_serverToClient_2261_);
return v_serverToClient_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object* v_serverToClient_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(v_serverToClient_2262_);
lean_dec(v_serverToClient_2262_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object* v_motive_2264_, uint8_t v_t_2265_, lean_object* v_h_2266_, lean_object* v_serverToClient_2267_){
_start:
{
lean_inc(v_serverToClient_2267_);
return v_serverToClient_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object* v_motive_2268_, lean_object* v_t_2269_, lean_object* v_h_2270_, lean_object* v_serverToClient_2271_){
_start:
{
uint8_t v_t_boxed_2272_; lean_object* v_res_2273_; 
v_t_boxed_2272_ = lean_unbox(v_t_2269_);
v_res_2273_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(v_motive_2268_, v_t_boxed_2272_, v_h_2270_, v_serverToClient_2271_);
lean_dec(v_serverToClient_2271_);
return v_res_2273_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default(void){
_start:
{
uint8_t v___x_2274_; 
v___x_2274_ = 0;
return v___x_2274_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection(void){
_start:
{
uint8_t v___x_2275_; 
v___x_2275_ = 0;
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object* v_json_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_Json_getTag_x3f(v_json_2290_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v___x_2292_; 
v___x_2292_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1));
return v___x_2292_;
}
else
{
lean_object* v_val_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_val_2293_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_val_2293_);
lean_dec_ref_known(v___x_2291_, 1);
v___x_2294_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2));
v___x_2295_ = lean_string_dec_eq(v_val_2293_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3));
v___x_2297_ = lean_string_dec_eq(v_val_2293_, v___x_2296_);
lean_dec(v_val_2293_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; 
v___x_2298_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5));
return v___x_2298_;
}
else
{
lean_object* v___x_2299_; 
v___x_2299_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6));
return v___x_2299_;
}
}
else
{
lean_object* v___x_2300_; 
lean_dec(v_val_2293_);
v___x_2300_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7));
return v___x_2300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t v_x_2307_){
_start:
{
if (v_x_2307_ == 0)
{
lean_object* v___x_2308_; 
v___x_2308_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0));
return v___x_2308_;
}
else
{
lean_object* v___x_2309_; 
v___x_2309_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1));
return v___x_2309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object* v_x_2310_){
_start:
{
uint8_t v_x_44__boxed_2311_; lean_object* v_res_2312_; 
v_x_44__boxed_2311_ = lean_unbox(v_x_2310_);
v_res_2312_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_x_44__boxed_2311_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx(uint8_t v_x_2315_){
_start:
{
switch(v_x_2315_)
{
case 0:
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_unsigned_to_nat(0u);
return v___x_2316_;
}
case 1:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_unsigned_to_nat(1u);
return v___x_2317_;
}
case 2:
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_unsigned_to_nat(2u);
return v___x_2318_;
}
default: 
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_unsigned_to_nat(3u);
return v___x_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___boxed(lean_object* v_x_2320_){
_start:
{
uint8_t v_x_boxed_2321_; lean_object* v_res_2322_; 
v_x_boxed_2321_ = lean_unbox(v_x_2320_);
v_res_2322_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_boxed_2321_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx(uint8_t v_x_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx___boxed(lean_object* v_x_2325_){
_start:
{
uint8_t v_x_4__boxed_2326_; lean_object* v_res_2327_; 
v_x_4__boxed_2326_ = lean_unbox(v_x_2325_);
v_res_2327_ = l_Lean_JsonRpc_MessageKind_toCtorIdx(v_x_4__boxed_2326_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object* v_k_2328_){
_start:
{
lean_inc(v_k_2328_);
return v_k_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object* v_k_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_JsonRpc_MessageKind_ctorElim___redArg(v_k_2329_);
lean_dec(v_k_2329_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object* v_motive_2331_, lean_object* v_ctorIdx_2332_, uint8_t v_t_2333_, lean_object* v_h_2334_, lean_object* v_k_2335_){
_start:
{
lean_inc(v_k_2335_);
return v_k_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object* v_motive_2336_, lean_object* v_ctorIdx_2337_, lean_object* v_t_2338_, lean_object* v_h_2339_, lean_object* v_k_2340_){
_start:
{
uint8_t v_t_boxed_2341_; lean_object* v_res_2342_; 
v_t_boxed_2341_ = lean_unbox(v_t_2338_);
v_res_2342_ = l_Lean_JsonRpc_MessageKind_ctorElim(v_motive_2336_, v_ctorIdx_2337_, v_t_boxed_2341_, v_h_2339_, v_k_2340_);
lean_dec(v_k_2340_);
lean_dec(v_ctorIdx_2337_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object* v_request_2343_){
_start:
{
lean_inc(v_request_2343_);
return v_request_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object* v_request_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_JsonRpc_MessageKind_request_elim___redArg(v_request_2344_);
lean_dec(v_request_2344_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object* v_motive_2346_, uint8_t v_t_2347_, lean_object* v_h_2348_, lean_object* v_request_2349_){
_start:
{
lean_inc(v_request_2349_);
return v_request_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object* v_motive_2350_, lean_object* v_t_2351_, lean_object* v_h_2352_, lean_object* v_request_2353_){
_start:
{
uint8_t v_t_boxed_2354_; lean_object* v_res_2355_; 
v_t_boxed_2354_ = lean_unbox(v_t_2351_);
v_res_2355_ = l_Lean_JsonRpc_MessageKind_request_elim(v_motive_2350_, v_t_boxed_2354_, v_h_2352_, v_request_2353_);
lean_dec(v_request_2353_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object* v_notification_2356_){
_start:
{
lean_inc(v_notification_2356_);
return v_notification_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object* v_notification_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_JsonRpc_MessageKind_notification_elim___redArg(v_notification_2357_);
lean_dec(v_notification_2357_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object* v_motive_2359_, uint8_t v_t_2360_, lean_object* v_h_2361_, lean_object* v_notification_2362_){
_start:
{
lean_inc(v_notification_2362_);
return v_notification_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object* v_motive_2363_, lean_object* v_t_2364_, lean_object* v_h_2365_, lean_object* v_notification_2366_){
_start:
{
uint8_t v_t_boxed_2367_; lean_object* v_res_2368_; 
v_t_boxed_2367_ = lean_unbox(v_t_2364_);
v_res_2368_ = l_Lean_JsonRpc_MessageKind_notification_elim(v_motive_2363_, v_t_boxed_2367_, v_h_2365_, v_notification_2366_);
lean_dec(v_notification_2366_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object* v_response_2369_){
_start:
{
lean_inc(v_response_2369_);
return v_response_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object* v_response_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_JsonRpc_MessageKind_response_elim___redArg(v_response_2370_);
lean_dec(v_response_2370_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object* v_motive_2372_, uint8_t v_t_2373_, lean_object* v_h_2374_, lean_object* v_response_2375_){
_start:
{
lean_inc(v_response_2375_);
return v_response_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object* v_motive_2376_, lean_object* v_t_2377_, lean_object* v_h_2378_, lean_object* v_response_2379_){
_start:
{
uint8_t v_t_boxed_2380_; lean_object* v_res_2381_; 
v_t_boxed_2380_ = lean_unbox(v_t_2377_);
v_res_2381_ = l_Lean_JsonRpc_MessageKind_response_elim(v_motive_2376_, v_t_boxed_2380_, v_h_2378_, v_response_2379_);
lean_dec(v_response_2379_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object* v_responseError_2382_){
_start:
{
lean_inc(v_responseError_2382_);
return v_responseError_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object* v_responseError_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(v_responseError_2383_);
lean_dec(v_responseError_2383_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object* v_motive_2385_, uint8_t v_t_2386_, lean_object* v_h_2387_, lean_object* v_responseError_2388_){
_start:
{
lean_inc(v_responseError_2388_);
return v_responseError_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object* v_motive_2389_, lean_object* v_t_2390_, lean_object* v_h_2391_, lean_object* v_responseError_2392_){
_start:
{
uint8_t v_t_boxed_2393_; lean_object* v_res_2394_; 
v_t_boxed_2393_ = lean_unbox(v_t_2390_);
v_res_2394_ = l_Lean_JsonRpc_MessageKind_responseError_elim(v_motive_2389_, v_t_boxed_2393_, v_h_2391_, v_responseError_2392_);
lean_dec(v_responseError_2392_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object* v_json_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_Json_getTag_x3f(v_json_2415_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v___x_2417_; 
v___x_2417_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0));
return v___x_2417_;
}
else
{
lean_object* v_val_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v_val_2418_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_val_2418_);
lean_dec_ref_known(v___x_2416_, 1);
v___x_2419_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1));
v___x_2420_ = lean_string_dec_eq(v_val_2418_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2));
v___x_2422_ = lean_string_dec_eq(v_val_2418_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3));
v___x_2424_ = lean_string_dec_eq(v_val_2418_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4));
v___x_2426_ = lean_string_dec_eq(v_val_2418_, v___x_2425_);
lean_dec(v_val_2418_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; 
v___x_2427_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5));
return v___x_2427_;
}
else
{
lean_object* v___x_2428_; 
v___x_2428_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6));
return v___x_2428_;
}
}
else
{
lean_object* v___x_2429_; 
lean_dec(v_val_2418_);
v___x_2429_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7));
return v___x_2429_;
}
}
else
{
lean_object* v___x_2430_; 
lean_dec(v_val_2418_);
v___x_2430_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8));
return v___x_2430_;
}
}
else
{
lean_object* v___x_2431_; 
lean_dec(v_val_2418_);
v___x_2431_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9));
return v___x_2431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t v_x_2442_){
_start:
{
switch(v_x_2442_)
{
case 0:
{
lean_object* v___x_2443_; 
v___x_2443_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0));
return v___x_2443_;
}
case 1:
{
lean_object* v___x_2444_; 
v___x_2444_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1));
return v___x_2444_;
}
case 2:
{
lean_object* v___x_2445_; 
v___x_2445_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2));
return v___x_2445_;
}
default: 
{
lean_object* v___x_2446_; 
v___x_2446_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3));
return v___x_2446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object* v_x_2447_){
_start:
{
uint8_t v_x_84__boxed_2448_; lean_object* v_res_2449_; 
v_x_84__boxed_2448_ = lean_unbox(v_x_2447_);
v_res_2449_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_x_84__boxed_2448_);
return v_res_2449_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object* v_x_2452_){
_start:
{
switch(lean_obj_tag(v_x_2452_))
{
case 0:
{
uint8_t v___x_2453_; 
v___x_2453_ = 0;
return v___x_2453_;
}
case 1:
{
uint8_t v___x_2454_; 
v___x_2454_ = 1;
return v___x_2454_;
}
case 2:
{
uint8_t v___x_2455_; 
v___x_2455_ = 2;
return v___x_2455_;
}
default: 
{
uint8_t v___x_2456_; 
v___x_2456_ = 3;
return v___x_2456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object* v_x_2457_){
_start:
{
uint8_t v_res_2458_; lean_object* v_r_2459_; 
v_res_2458_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_x_2457_);
lean_dec_ref(v_x_2457_);
v_r_2459_ = lean_box(v_res_2458_);
return v_r_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(lean_object* v_j_2460_, lean_object* v_k_2461_){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = l_Lean_Json_getObjValD(v_j_2460_, v_k_2461_);
v___x_2463_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0___boxed(lean_object* v_j_2464_, lean_object* v_k_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(v_j_2464_, v_k_2465_);
lean_dec_ref(v_k_2465_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object* v_h_2469_, lean_object* v_nBytes_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_IO_FS_Stream_readJson(v_h_2469_, v_nBytes_2470_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2592_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2592_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2592_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___y_2478_; lean_object* v___y_2479_; uint8_t v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v_a_2492_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_a_2473_);
v___x_2504_ = l_Lean_Json_getObjVal_x3f(v_a_2473_, v___x_2503_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; 
lean_del_object(v___x_2475_);
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v_a_2492_ = v_a_2505_;
goto v___jp_2491_;
}
else
{
lean_object* v_a_2506_; 
v_a_2506_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2504_, 1);
if (lean_obj_tag(v_a_2506_) == 3)
{
lean_object* v_s_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v_s_2507_ = lean_ctor_get(v_a_2506_, 0);
lean_inc_ref(v_s_2507_);
lean_dec_ref_known(v_a_2506_, 1);
v___x_2508_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_2509_ = lean_string_dec_eq(v_s_2507_, v___x_2508_);
lean_dec_ref(v_s_2507_);
if (v___x_2509_ == 0)
{
lean_del_object(v___x_2475_);
goto v___jp_2501_;
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_a_2473_);
v___x_2511_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_2473_, v___x_2510_);
if (lean_obj_tag(v___x_2511_) == 0)
{
goto v___jp_2540_;
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v_a_2567_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2567_);
v___x_2568_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2473_);
v___x_2569_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2473_, v___x_2568_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_dec_ref_known(v___x_2569_, 1);
lean_dec(v_a_2567_);
goto v___jp_2540_;
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2591_; 
lean_dec_ref_known(v___x_2511_, 1);
lean_del_object(v___x_2475_);
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2591_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2591_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___y_2575_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2581_ = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(v_a_2473_, v___x_2580_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v___x_2582_; 
lean_dec_ref_known(v___x_2581_, 1);
v___x_2582_ = lean_box(0);
v___y_2575_ = v___x_2582_;
goto v___jp_2574_;
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_a_2583_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2581_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2581_);
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
v___y_2575_ = v___x_2588_;
goto v___jp_2574_;
}
}
}
v___jp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2576_, 0, v_a_2567_);
lean_ctor_set(v___x_2576_, 1, v_a_2570_);
lean_ctor_set(v___x_2576_, 2, v___y_2575_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set_tag(v___x_2572_, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2576_);
v___x_2578_ = v___x_2572_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
v___jp_2512_:
{
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2513_; 
lean_del_object(v___x_2475_);
v_a_2513_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2511_, 1);
v_a_2492_ = v_a_2513_;
goto v___jp_2491_;
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_a_2514_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2511_, 1);
v___x_2515_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
lean_inc(v_a_2473_);
v___x_2516_ = l_Lean_Json_getObjVal_x3f(v_a_2473_, v___x_2515_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; 
lean_dec(v_a_2514_);
lean_del_object(v___x_2475_);
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v_a_2492_ = v_a_2517_;
goto v___jp_2491_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v_a_2518_ = lean_ctor_get(v___x_2516_, 0);
lean_inc_n(v_a_2518_, 2);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2519_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_2520_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_2518_, v___x_2519_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; 
lean_dec(v_a_2518_);
lean_dec(v_a_2514_);
lean_del_object(v___x_2475_);
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v_a_2492_ = v_a_2521_;
goto v___jp_2491_;
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_a_2522_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___x_2520_, 1);
v___x_2523_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_2518_);
v___x_2524_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2518_, v___x_2523_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; 
lean_dec(v_a_2522_);
lean_dec(v_a_2518_);
lean_dec(v_a_2514_);
lean_del_object(v___x_2475_);
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2524_, 1);
v_a_2492_ = v_a_2525_;
goto v___jp_2491_;
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_dec(v_a_2473_);
v_a_2526_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2524_, 1);
v___x_2527_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2528_ = l_Lean_Json_getObjVal_x3f(v_a_2518_, v___x_2527_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v___x_2529_; uint8_t v___x_2530_; 
lean_dec_ref_known(v___x_2528_, 1);
v___x_2529_ = lean_box(0);
v___x_2530_ = lean_unbox(v_a_2522_);
lean_dec(v_a_2522_);
v___y_2478_ = v_a_2514_;
v___y_2479_ = v_a_2526_;
v___y_2480_ = v___x_2530_;
v___y_2481_ = v___x_2529_;
goto v___jp_2477_;
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2539_; 
v_a_2531_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2533_ = v___x_2528_;
v_isShared_2534_ = v_isSharedCheck_2539_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2528_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2539_;
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
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
uint8_t v___x_2537_; 
v___x_2537_ = lean_unbox(v_a_2522_);
lean_dec(v_a_2522_);
v___y_2478_ = v_a_2514_;
v___y_2479_ = v_a_2526_;
v___y_2480_ = v___x_2537_;
v___y_2481_ = v___x_2536_;
goto v___jp_2477_;
}
}
}
}
}
}
}
}
v___jp_2540_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2473_);
v___x_2542_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2473_, v___x_2541_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_dec_ref_known(v___x_2542_, 1);
if (lean_obj_tag(v___x_2511_) == 0)
{
goto v___jp_2512_;
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v_a_2543_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2543_);
v___x_2544_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_2473_);
v___x_2545_ = l_Lean_Json_getObjVal_x3f(v_a_2473_, v___x_2544_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_dec_ref_known(v___x_2545_, 1);
lean_dec(v_a_2543_);
goto v___jp_2512_;
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2554_; 
lean_dec_ref_known(v___x_2511_, 1);
lean_del_object(v___x_2475_);
lean_dec(v_a_2473_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2554_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2554_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; lean_object* v___x_2552_; 
v___x_2550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2550_, 0, v_a_2543_);
lean_ctor_set(v___x_2550_, 1, v_a_2546_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set_tag(v___x_2548_, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2550_);
v___x_2552_ = v___x_2548_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec_ref(v___x_2511_);
lean_del_object(v___x_2475_);
v_a_2555_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v___x_2542_, 1);
v___x_2556_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2557_ = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(v_a_2473_, v___x_2556_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2558_; 
lean_dec_ref_known(v___x_2557_, 1);
v___x_2558_ = lean_box(0);
v___y_2487_ = v_a_2555_;
v___y_2488_ = v___x_2558_;
goto v___jp_2486_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v_a_2559_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2557_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2557_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
v___y_2487_ = v_a_2555_;
v___y_2488_ = v___x_2564_;
goto v___jp_2486_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2506_);
lean_del_object(v___x_2475_);
goto v___jp_2501_;
}
}
v___jp_2477_:
{
lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2482_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2482_, 0, v___y_2478_);
lean_ctor_set(v___x_2482_, 1, v___y_2479_);
lean_ctor_set(v___x_2482_, 2, v___y_2481_);
lean_ctor_set_uint8(v___x_2482_, sizeof(void*)*3, v___y_2480_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2482_);
v___x_2484_ = v___x_2475_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
v___jp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___y_2487_);
lean_ctor_set(v___x_2489_, 1, v___y_2488_);
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
return v___x_2490_;
}
v___jp_2491_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2493_ = ((lean_object*)(l_IO_FS_Stream_readMessage___closed__0));
v___x_2494_ = l_Lean_Json_compress(v_a_2473_);
v___x_2495_ = lean_string_append(v___x_2493_, v___x_2494_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = ((lean_object*)(l_IO_FS_Stream_readMessage___closed__1));
v___x_2497_ = lean_string_append(v___x_2495_, v___x_2496_);
v___x_2498_ = lean_string_append(v___x_2497_, v_a_2492_);
lean_dec_ref(v_a_2492_);
v___x_2499_ = lean_mk_io_user_error(v___x_2498_);
v___x_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
return v___x_2500_;
}
v___jp_2501_:
{
lean_object* v___x_2502_; 
v___x_2502_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_2492_ = v___x_2502_;
goto v___jp_2491_;
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
v_a_2593_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2472_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2472_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object* v_h_2601_, lean_object* v_nBytes_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_IO_FS_Stream_readMessage(v_h_2601_, v_nBytes_2602_);
lean_dec(v_nBytes_2602_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object* v_h_2612_, lean_object* v_nBytes_2613_, lean_object* v_expectedMethod_2614_, lean_object* v_inst_2615_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_IO_FS_Stream_readMessage(v_h_2612_, v_nBytes_2613_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2805_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2805_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2805_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
if (lean_obj_tag(v_a_2618_) == 0)
{
lean_object* v_id_2622_; lean_object* v_method_2623_; lean_object* v_params_x3f_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2664_; 
v_id_2622_ = lean_ctor_get(v_a_2618_, 0);
v_method_2623_ = lean_ctor_get(v_a_2618_, 1);
v_params_x3f_2624_ = lean_ctor_get(v_a_2618_, 2);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_a_2618_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2626_ = v_a_2618_;
v_isShared_2627_ = v_isSharedCheck_2664_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_params_x3f_2624_);
lean_inc(v_method_2623_);
lean_inc(v_id_2622_);
lean_dec(v_a_2618_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2664_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
uint8_t v___x_2628_; 
v___x_2628_ = lean_string_dec_eq(v_method_2623_, v_expectedMethod_2614_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
lean_del_object(v___x_2626_);
lean_dec(v_params_x3f_2624_);
lean_dec(v_id_2622_);
lean_dec_ref(v_inst_2615_);
v___x_2629_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2630_ = lean_string_append(v___x_2629_, v_expectedMethod_2614_);
lean_dec_ref(v_expectedMethod_2614_);
v___x_2631_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2632_ = lean_string_append(v___x_2630_, v___x_2631_);
v___x_2633_ = lean_string_append(v___x_2632_, v_method_2623_);
lean_dec_ref(v_method_2623_);
v___x_2634_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2635_ = lean_string_append(v___x_2633_, v___x_2634_);
v___x_2636_ = lean_mk_io_user_error(v___x_2635_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set_tag(v___x_2620_, 1);
lean_ctor_set(v___x_2620_, 0, v___x_2636_);
v___x_2638_ = v___x_2620_;
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
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_dec_ref(v_method_2623_);
v___x_2640_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2641_ = l_Option_toJson___redArg(v___x_2640_, v_params_x3f_2624_);
lean_inc(v___x_2641_);
v___x_2642_ = lean_apply_1(v_inst_2615_, v___x_2641_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
lean_del_object(v___x_2626_);
lean_dec(v_id_2622_);
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v___x_2644_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2645_ = l_Lean_Json_compress(v___x_2641_);
v___x_2646_ = lean_string_append(v___x_2644_, v___x_2645_);
lean_dec_ref(v___x_2645_);
v___x_2647_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2648_ = lean_string_append(v___x_2646_, v___x_2647_);
v___x_2649_ = lean_string_append(v___x_2648_, v_expectedMethod_2614_);
lean_dec_ref(v_expectedMethod_2614_);
v___x_2650_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2651_ = lean_string_append(v___x_2649_, v___x_2650_);
v___x_2652_ = lean_string_append(v___x_2651_, v_a_2643_);
lean_dec(v_a_2643_);
v___x_2653_ = lean_mk_io_user_error(v___x_2652_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set_tag(v___x_2620_, 1);
lean_ctor_set(v___x_2620_, 0, v___x_2653_);
v___x_2655_ = v___x_2620_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; 
lean_dec(v___x_2641_);
v_a_2657_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2642_, 1);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 2, v_a_2657_);
lean_ctor_set(v___x_2626_, 1, v_expectedMethod_2614_);
v___x_2659_ = v___x_2626_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_id_2622_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_expectedMethod_2614_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_a_2657_);
v___x_2659_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2661_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2659_);
v___x_2661_ = v___x_2620_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___y_2669_; 
lean_dec_ref(v_inst_2615_);
lean_dec_ref(v_expectedMethod_2614_);
v___x_2665_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__6));
v___x_2666_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2667_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2618_))
{
case 0:
{
lean_object* v_id_2680_; lean_object* v_method_2681_; lean_object* v_params_x3f_2682_; lean_object* v___x_2683_; lean_object* v___y_2685_; 
v_id_2680_ = lean_ctor_get(v_a_2618_, 0);
lean_inc(v_id_2680_);
v_method_2681_ = lean_ctor_get(v_a_2618_, 1);
lean_inc_ref(v_method_2681_);
v_params_x3f_2682_ = lean_ctor_get(v_a_2618_, 2);
lean_inc(v_params_x3f_2682_);
lean_dec_ref_known(v_a_2618_, 3);
v___x_2683_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2680_) == 0)
{
lean_object* v_s_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
v_s_2696_ = lean_ctor_get(v_id_2680_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_id_2680_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v_id_2680_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_s_2696_);
lean_dec(v_id_2680_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 3);
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_s_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
v___y_2685_ = v___x_2701_;
goto v___jp_2684_;
}
}
}
else
{
lean_object* v_n_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
v_n_2704_ = lean_ctor_get(v_id_2680_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_id_2680_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v_id_2680_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_n_2704_);
lean_dec(v_id_2680_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
lean_ctor_set_tag(v___x_2706_, 2);
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_n_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
v___y_2685_ = v___x_2709_;
goto v___jp_2684_;
}
}
}
v___jp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2683_);
lean_ctor_set(v___x_2686_, 1, v___y_2685_);
v___x_2687_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_method_2681_);
v___x_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = lean_box(0);
v___x_2691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2689_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2686_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2694_ = l_Lean_Json_opt___redArg(v___x_2666_, v___x_2693_, v_params_x3f_2682_);
v___x_2695_ = l_List_appendTR___redArg(v___x_2692_, v___x_2694_);
v___y_2669_ = v___x_2695_;
goto v___jp_2668_;
}
}
case 1:
{
lean_object* v_method_2712_; lean_object* v_params_x3f_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_method_2712_ = lean_ctor_get(v_a_2618_, 0);
lean_inc_ref(v_method_2712_);
v_params_x3f_2713_ = lean_ctor_get(v_a_2618_, 1);
lean_inc(v_params_x3f_2713_);
lean_dec_ref_known(v_a_2618_, 2);
v___x_2714_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2715_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2715_, 0, v_method_2712_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2718_ = l_Lean_Json_opt___redArg(v___x_2666_, v___x_2717_, v_params_x3f_2713_);
v___x_2719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2716_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___y_2669_ = v___x_2719_;
goto v___jp_2668_;
}
case 2:
{
lean_object* v_id_2720_; lean_object* v_result_2721_; lean_object* v___x_2722_; lean_object* v___y_2724_; 
v_id_2720_ = lean_ctor_get(v_a_2618_, 0);
lean_inc(v_id_2720_);
v_result_2721_ = lean_ctor_get(v_a_2618_, 1);
lean_inc(v_result_2721_);
lean_dec_ref_known(v_a_2618_, 2);
v___x_2722_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2720_) == 0)
{
lean_object* v_s_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
v_s_2731_ = lean_ctor_get(v_id_2720_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_id_2720_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v_id_2720_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_s_2731_);
lean_dec(v_id_2720_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
lean_ctor_set_tag(v___x_2733_, 3);
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_s_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
v___y_2724_ = v___x_2736_;
goto v___jp_2723_;
}
}
}
else
{
lean_object* v_n_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
v_n_2739_ = lean_ctor_get(v_id_2720_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_id_2720_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v_id_2720_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_n_2739_);
lean_dec(v_id_2720_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set_tag(v___x_2741_, 2);
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_n_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
v___y_2724_ = v___x_2744_;
goto v___jp_2723_;
}
}
}
v___jp_2723_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2722_);
lean_ctor_set(v___x_2725_, 1, v___y_2724_);
v___x_2726_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
lean_ctor_set(v___x_2727_, 1, v_result_2721_);
v___x_2728_ = lean_box(0);
v___x_2729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2727_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2725_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___y_2669_ = v___x_2730_;
goto v___jp_2668_;
}
}
default: 
{
lean_object* v_id_2747_; uint8_t v_code_2748_; lean_object* v_message_2749_; lean_object* v_data_x3f_2750_; lean_object* v___x_2751_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___x_2771_; lean_object* v___y_2773_; 
v_id_2747_ = lean_ctor_get(v_a_2618_, 0);
lean_inc(v_id_2747_);
v_code_2748_ = lean_ctor_get_uint8(v_a_2618_, sizeof(void*)*3);
v_message_2749_ = lean_ctor_get(v_a_2618_, 1);
lean_inc_ref(v_message_2749_);
v_data_x3f_2750_ = lean_ctor_get(v_a_2618_, 2);
lean_inc(v_data_x3f_2750_);
lean_dec_ref_known(v_a_2618_, 3);
v___x_2751_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2771_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2747_) == 0)
{
lean_object* v_s_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
v_s_2789_ = lean_ctor_get(v_id_2747_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_id_2747_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v_id_2747_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_s_2789_);
lean_dec(v_id_2747_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 3);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_s_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
v___y_2773_ = v___x_2794_;
goto v___jp_2772_;
}
}
}
else
{
lean_object* v_n_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2804_; 
v_n_2797_ = lean_ctor_get(v_id_2747_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_id_2747_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2799_ = v_id_2747_;
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_n_2797_);
lean_dec(v_id_2747_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2804_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2802_; 
if (v_isShared_2800_ == 0)
{
lean_ctor_set_tag(v___x_2799_, 2);
v___x_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_n_2797_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
v___y_2773_ = v___x_2802_;
goto v___jp_2772_;
}
}
}
v___jp_2752_:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_inc(v___y_2756_);
lean_inc_ref(v___y_2753_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___y_2753_);
lean_ctor_set(v___x_2757_, 1, v___y_2756_);
v___x_2758_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2759_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2759_, 0, v_message_2749_);
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = lean_box(0);
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2757_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2765_ = l_Lean_Json_opt___redArg(v___x_2751_, v___x_2764_, v_data_x3f_2750_);
v___x_2766_ = l_List_appendTR___redArg(v___x_2763_, v___x_2765_);
v___x_2767_ = l_Lean_Json_mkObj(v___x_2766_);
lean_dec(v___x_2766_);
lean_inc_ref(v___y_2755_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___y_2755_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
lean_ctor_set(v___x_2769_, 1, v___x_2761_);
v___x_2770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___y_2754_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___y_2669_ = v___x_2770_;
goto v___jp_2668_;
}
v___jp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2771_);
lean_ctor_set(v___x_2774_, 1, v___y_2773_);
v___x_2775_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2776_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2748_)
{
case 0:
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2777_;
goto v___jp_2752_;
}
case 1:
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2778_;
goto v___jp_2752_;
}
case 2:
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2779_;
goto v___jp_2752_;
}
case 3:
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2780_;
goto v___jp_2752_;
}
case 4:
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2781_;
goto v___jp_2752_;
}
case 5:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2782_;
goto v___jp_2752_;
}
case 6:
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2783_;
goto v___jp_2752_;
}
case 7:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2784_;
goto v___jp_2752_;
}
case 8:
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2785_;
goto v___jp_2752_;
}
case 9:
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2786_;
goto v___jp_2752_;
}
case 10:
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2787_;
goto v___jp_2752_;
}
default: 
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2753_ = v___x_2776_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2775_;
v___y_2756_ = v___x_2788_;
goto v___jp_2752_;
}
}
}
}
}
v___jp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2667_);
lean_ctor_set(v___x_2670_, 1, v___y_2669_);
v___x_2671_ = l_Lean_Json_mkObj(v___x_2670_);
lean_dec_ref_known(v___x_2670_, 2);
v___x_2672_ = l_Lean_Json_compress(v___x_2671_);
v___x_2673_ = lean_string_append(v___x_2665_, v___x_2672_);
lean_dec_ref(v___x_2672_);
v___x_2674_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2675_ = lean_string_append(v___x_2673_, v___x_2674_);
v___x_2676_ = lean_mk_io_user_error(v___x_2675_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set_tag(v___x_2620_, 1);
lean_ctor_set(v___x_2620_, 0, v___x_2676_);
v___x_2678_ = v___x_2620_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec_ref(v_inst_2615_);
lean_dec_ref(v_expectedMethod_2614_);
v_a_2806_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2617_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2617_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* v_h_2814_, lean_object* v_nBytes_2815_, lean_object* v_expectedMethod_2816_, lean_object* v_inst_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_IO_FS_Stream_readRequestAs___redArg(v_h_2814_, v_nBytes_2815_, v_expectedMethod_2816_, v_inst_2817_);
lean_dec(v_nBytes_2815_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object* v_h_2820_, lean_object* v_nBytes_2821_, lean_object* v_expectedMethod_2822_, lean_object* v_00_u03b1_2823_, lean_object* v_inst_2824_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_IO_FS_Stream_readRequestAs___redArg(v_h_2820_, v_nBytes_2821_, v_expectedMethod_2822_, v_inst_2824_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object* v_h_2827_, lean_object* v_nBytes_2828_, lean_object* v_expectedMethod_2829_, lean_object* v_00_u03b1_2830_, lean_object* v_inst_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_IO_FS_Stream_readRequestAs(v_h_2827_, v_nBytes_2828_, v_expectedMethod_2829_, v_00_u03b1_2830_, v_inst_2831_);
lean_dec(v_nBytes_2828_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object* v_h_2835_, lean_object* v_nBytes_2836_, lean_object* v_expectedMethod_2837_, lean_object* v_inst_2838_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_IO_FS_Stream_readMessage(v_h_2835_, v_nBytes_2836_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_3027_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_3027_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_3027_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
if (lean_obj_tag(v_a_2841_) == 1)
{
lean_object* v_method_2845_; lean_object* v_params_x3f_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2886_; 
v_method_2845_ = lean_ctor_get(v_a_2841_, 0);
v_params_x3f_2846_ = lean_ctor_get(v_a_2841_, 1);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_a_2841_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2848_ = v_a_2841_;
v_isShared_2849_ = v_isSharedCheck_2886_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_params_x3f_2846_);
lean_inc(v_method_2845_);
lean_dec(v_a_2841_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2886_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
uint8_t v___x_2850_; 
v___x_2850_ = lean_string_dec_eq(v_method_2845_, v_expectedMethod_2837_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
lean_del_object(v___x_2848_);
lean_dec(v_params_x3f_2846_);
lean_dec_ref(v_inst_2838_);
v___x_2851_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2852_ = lean_string_append(v___x_2851_, v_expectedMethod_2837_);
lean_dec_ref(v_expectedMethod_2837_);
v___x_2853_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2854_ = lean_string_append(v___x_2852_, v___x_2853_);
v___x_2855_ = lean_string_append(v___x_2854_, v_method_2845_);
lean_dec_ref(v_method_2845_);
v___x_2856_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2857_ = lean_string_append(v___x_2855_, v___x_2856_);
v___x_2858_ = lean_mk_io_user_error(v___x_2857_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set_tag(v___x_2843_, 1);
lean_ctor_set(v___x_2843_, 0, v___x_2858_);
v___x_2860_ = v___x_2843_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec_ref(v_method_2845_);
v___x_2862_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2863_ = l_Option_toJson___redArg(v___x_2862_, v_params_x3f_2846_);
lean_inc(v___x_2863_);
v___x_2864_ = lean_apply_1(v_inst_2838_, v___x_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
lean_del_object(v___x_2848_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2867_ = l_Lean_Json_compress(v___x_2863_);
v___x_2868_ = lean_string_append(v___x_2866_, v___x_2867_);
lean_dec_ref(v___x_2867_);
v___x_2869_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2870_ = lean_string_append(v___x_2868_, v___x_2869_);
v___x_2871_ = lean_string_append(v___x_2870_, v_expectedMethod_2837_);
lean_dec_ref(v_expectedMethod_2837_);
v___x_2872_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2873_ = lean_string_append(v___x_2871_, v___x_2872_);
v___x_2874_ = lean_string_append(v___x_2873_, v_a_2865_);
lean_dec(v_a_2865_);
v___x_2875_ = lean_mk_io_user_error(v___x_2874_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set_tag(v___x_2843_, 1);
lean_ctor_set(v___x_2843_, 0, v___x_2875_);
v___x_2877_ = v___x_2843_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; 
lean_dec(v___x_2863_);
v_a_2879_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2864_, 1);
if (v_isShared_2849_ == 0)
{
lean_ctor_set_tag(v___x_2848_, 0);
lean_ctor_set(v___x_2848_, 1, v_a_2879_);
lean_ctor_set(v___x_2848_, 0, v_expectedMethod_2837_);
v___x_2881_ = v___x_2848_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_expectedMethod_2837_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_a_2879_);
v___x_2881_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2883_; 
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2881_);
v___x_2883_ = v___x_2843_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___y_2891_; 
lean_dec_ref(v_inst_2838_);
lean_dec_ref(v_expectedMethod_2837_);
v___x_2887_ = ((lean_object*)(l_IO_FS_Stream_readNotificationAs___redArg___closed__0));
v___x_2888_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2889_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2841_))
{
case 0:
{
lean_object* v_id_2902_; lean_object* v_method_2903_; lean_object* v_params_x3f_2904_; lean_object* v___x_2905_; lean_object* v___y_2907_; 
v_id_2902_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_id_2902_);
v_method_2903_ = lean_ctor_get(v_a_2841_, 1);
lean_inc_ref(v_method_2903_);
v_params_x3f_2904_ = lean_ctor_get(v_a_2841_, 2);
lean_inc(v_params_x3f_2904_);
lean_dec_ref_known(v_a_2841_, 3);
v___x_2905_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2902_) == 0)
{
lean_object* v_s_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
v_s_2918_ = lean_ctor_get(v_id_2902_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v_id_2902_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v_id_2902_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_s_2918_);
lean_dec(v_id_2902_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
lean_ctor_set_tag(v___x_2920_, 3);
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_s_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
v___y_2907_ = v___x_2923_;
goto v___jp_2906_;
}
}
}
else
{
lean_object* v_n_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
v_n_2926_ = lean_ctor_get(v_id_2902_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_id_2902_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v_id_2902_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_n_2926_);
lean_dec(v_id_2902_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
lean_ctor_set_tag(v___x_2928_, 2);
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_n_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
v___y_2907_ = v___x_2931_;
goto v___jp_2906_;
}
}
}
v___jp_2906_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2905_);
lean_ctor_set(v___x_2908_, 1, v___y_2907_);
v___x_2909_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2910_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2910_, 0, v_method_2903_);
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2911_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2908_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2916_ = l_Lean_Json_opt___redArg(v___x_2888_, v___x_2915_, v_params_x3f_2904_);
v___x_2917_ = l_List_appendTR___redArg(v___x_2914_, v___x_2916_);
v___y_2891_ = v___x_2917_;
goto v___jp_2890_;
}
}
case 1:
{
lean_object* v_method_2934_; lean_object* v_params_x3f_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_method_2934_ = lean_ctor_get(v_a_2841_, 0);
lean_inc_ref(v_method_2934_);
v_params_x3f_2935_ = lean_ctor_get(v_a_2841_, 1);
lean_inc(v_params_x3f_2935_);
lean_dec_ref_known(v_a_2841_, 2);
v___x_2936_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_method_2934_);
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2940_ = l_Lean_Json_opt___redArg(v___x_2888_, v___x_2939_, v_params_x3f_2935_);
v___x_2941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2938_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
v___y_2891_ = v___x_2941_;
goto v___jp_2890_;
}
case 2:
{
lean_object* v_id_2942_; lean_object* v_result_2943_; lean_object* v___x_2944_; lean_object* v___y_2946_; 
v_id_2942_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_id_2942_);
v_result_2943_ = lean_ctor_get(v_a_2841_, 1);
lean_inc(v_result_2943_);
lean_dec_ref_known(v_a_2841_, 2);
v___x_2944_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2942_) == 0)
{
lean_object* v_s_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
v_s_2953_ = lean_ctor_get(v_id_2942_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_id_2942_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v_id_2942_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_s_2953_);
lean_dec(v_id_2942_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set_tag(v___x_2955_, 3);
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_s_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
v___y_2946_ = v___x_2958_;
goto v___jp_2945_;
}
}
}
else
{
lean_object* v_n_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
v_n_2961_ = lean_ctor_get(v_id_2942_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_id_2942_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v_id_2942_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_n_2961_);
lean_dec(v_id_2942_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 2);
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_n_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
v___y_2946_ = v___x_2966_;
goto v___jp_2945_;
}
}
}
v___jp_2945_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2944_);
lean_ctor_set(v___x_2947_, 1, v___y_2946_);
v___x_2948_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v_result_2943_);
v___x_2950_ = lean_box(0);
v___x_2951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2949_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___x_2952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2947_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___y_2891_ = v___x_2952_;
goto v___jp_2890_;
}
}
default: 
{
lean_object* v_id_2969_; uint8_t v_code_2970_; lean_object* v_message_2971_; lean_object* v_data_x3f_2972_; lean_object* v___x_2973_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___x_2993_; lean_object* v___y_2995_; 
v_id_2969_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_id_2969_);
v_code_2970_ = lean_ctor_get_uint8(v_a_2841_, sizeof(void*)*3);
v_message_2971_ = lean_ctor_get(v_a_2841_, 1);
lean_inc_ref(v_message_2971_);
v_data_x3f_2972_ = lean_ctor_get(v_a_2841_, 2);
lean_inc(v_data_x3f_2972_);
lean_dec_ref_known(v_a_2841_, 3);
v___x_2973_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2993_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2969_) == 0)
{
lean_object* v_s_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
v_s_3011_ = lean_ctor_get(v_id_2969_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_id_2969_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v_id_2969_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_s_3011_);
lean_dec(v_id_2969_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set_tag(v___x_3013_, 3);
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_s_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
v___y_2995_ = v___x_3016_;
goto v___jp_2994_;
}
}
}
else
{
lean_object* v_n_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
v_n_3019_ = lean_ctor_get(v_id_2969_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_id_2969_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v_id_2969_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_n_3019_);
lean_dec(v_id_2969_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set_tag(v___x_3021_, 2);
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_n_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
v___y_2995_ = v___x_3024_;
goto v___jp_2994_;
}
}
}
v___jp_2974_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_inc(v___y_2978_);
lean_inc_ref(v___y_2977_);
v___x_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___y_2977_);
lean_ctor_set(v___x_2979_, 1, v___y_2978_);
v___x_2980_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2981_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_message_2971_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2980_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = lean_box(0);
v___x_2984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2979_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2987_ = l_Lean_Json_opt___redArg(v___x_2973_, v___x_2986_, v_data_x3f_2972_);
v___x_2988_ = l_List_appendTR___redArg(v___x_2985_, v___x_2987_);
v___x_2989_ = l_Lean_Json_mkObj(v___x_2988_);
lean_dec(v___x_2988_);
lean_inc_ref(v___y_2976_);
v___x_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___y_2976_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
lean_ctor_set(v___x_2991_, 1, v___x_2983_);
v___x_2992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___y_2975_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___y_2891_ = v___x_2992_;
goto v___jp_2890_;
}
v___jp_2994_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2993_);
lean_ctor_set(v___x_2996_, 1, v___y_2995_);
v___x_2997_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2998_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2970_)
{
case 0:
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_2999_;
goto v___jp_2974_;
}
case 1:
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_3000_;
goto v___jp_2974_;
}
case 2:
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_3001_;
goto v___jp_2974_;
}
case 3:
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_3002_;
goto v___jp_2974_;
}
case 4:
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_3003_;
goto v___jp_2974_;
}
case 5:
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_3004_;
goto v___jp_2974_;
}
case 6:
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_3005_;
goto v___jp_2974_;
}
case 7:
{
lean_object* v___x_3006_; 
v___x_3006_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_3006_;
goto v___jp_2974_;
}
case 8:
{
lean_object* v___x_3007_; 
v___x_3007_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_3007_;
goto v___jp_2974_;
}
case 9:
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_3008_;
goto v___jp_2974_;
}
case 10:
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_3009_;
goto v___jp_2974_;
}
default: 
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
v___y_2978_ = v___x_3010_;
goto v___jp_2974_;
}
}
}
}
}
v___jp_2890_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2889_);
lean_ctor_set(v___x_2892_, 1, v___y_2891_);
v___x_2893_ = l_Lean_Json_mkObj(v___x_2892_);
lean_dec_ref_known(v___x_2892_, 2);
v___x_2894_ = l_Lean_Json_compress(v___x_2893_);
v___x_2895_ = lean_string_append(v___x_2887_, v___x_2894_);
lean_dec_ref(v___x_2894_);
v___x_2896_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2897_ = lean_string_append(v___x_2895_, v___x_2896_);
v___x_2898_ = lean_mk_io_user_error(v___x_2897_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set_tag(v___x_2843_, 1);
lean_ctor_set(v___x_2843_, 0, v___x_2898_);
v___x_2900_ = v___x_2843_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec_ref(v_inst_2838_);
lean_dec_ref(v_expectedMethod_2837_);
v_a_3028_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_2840_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_2840_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* v_h_3036_, lean_object* v_nBytes_3037_, lean_object* v_expectedMethod_3038_, lean_object* v_inst_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_IO_FS_Stream_readNotificationAs___redArg(v_h_3036_, v_nBytes_3037_, v_expectedMethod_3038_, v_inst_3039_);
lean_dec(v_nBytes_3037_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object* v_h_3042_, lean_object* v_nBytes_3043_, lean_object* v_expectedMethod_3044_, lean_object* v_00_u03b1_3045_, lean_object* v_inst_3046_){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_IO_FS_Stream_readNotificationAs___redArg(v_h_3042_, v_nBytes_3043_, v_expectedMethod_3044_, v_inst_3046_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object* v_h_3049_, lean_object* v_nBytes_3050_, lean_object* v_expectedMethod_3051_, lean_object* v_00_u03b1_3052_, lean_object* v_inst_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_IO_FS_Stream_readNotificationAs(v_h_3049_, v_nBytes_3050_, v_expectedMethod_3051_, v_00_u03b1_3052_, v_inst_3053_);
lean_dec(v_nBytes_3050_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object* v_h_3060_, lean_object* v_nBytes_3061_, lean_object* v_expectedID_3062_, lean_object* v_inst_3063_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_IO_FS_Stream_readMessage(v_h_3060_, v_nBytes_3061_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3269_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3068_ = v___x_3065_;
v_isShared_3069_ = v_isSharedCheck_3269_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3269_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___y_3071_; lean_object* v___y_3072_; 
if (lean_obj_tag(v_a_3066_) == 2)
{
lean_object* v_id_3078_; lean_object* v_result_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3130_; 
v_id_3078_ = lean_ctor_get(v_a_3066_, 0);
v_result_3079_ = lean_ctor_get(v_a_3066_, 1);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_a_3066_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3081_ = v_a_3066_;
v_isShared_3082_ = v_isSharedCheck_3130_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_result_3079_);
lean_inc(v_id_3078_);
lean_dec(v_a_3066_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3130_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
uint8_t v___x_3083_; 
v___x_3083_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3078_, v_expectedID_3062_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; lean_object* v___y_3086_; 
lean_del_object(v___x_3081_);
lean_dec(v_result_3079_);
lean_dec_ref(v_inst_3063_);
v___x_3084_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__0));
switch(lean_obj_tag(v_expectedID_3062_))
{
case 0:
{
lean_object* v_s_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_s_3096_ = lean_ctor_get(v_expectedID_3062_, 0);
lean_inc_ref(v_s_3096_);
lean_dec_ref_known(v_expectedID_3062_, 1);
v___x_3097_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3098_ = lean_string_append(v___x_3097_, v_s_3096_);
lean_dec_ref(v_s_3096_);
v___x_3099_ = lean_string_append(v___x_3098_, v___x_3097_);
v___y_3086_ = v___x_3099_;
goto v___jp_3085_;
}
case 1:
{
lean_object* v_n_3100_; lean_object* v___x_3101_; 
v_n_3100_ = lean_ctor_get(v_expectedID_3062_, 0);
lean_inc_ref(v_n_3100_);
lean_dec_ref_known(v_expectedID_3062_, 1);
v___x_3101_ = l_Lean_JsonNumber_toString(v_n_3100_);
v___y_3086_ = v___x_3101_;
goto v___jp_3085_;
}
default: 
{
lean_object* v___x_3102_; 
v___x_3102_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___y_3086_ = v___x_3102_;
goto v___jp_3085_;
}
}
v___jp_3085_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3087_ = lean_string_append(v___x_3084_, v___y_3086_);
lean_dec_ref(v___y_3086_);
v___x_3088_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__1));
v___x_3089_ = lean_string_append(v___x_3087_, v___x_3088_);
if (lean_obj_tag(v_id_3078_) == 0)
{
lean_object* v_s_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v_s_3090_ = lean_ctor_get(v_id_3078_, 0);
lean_inc_ref(v_s_3090_);
lean_dec_ref_known(v_id_3078_, 1);
v___x_3091_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3092_ = lean_string_append(v___x_3091_, v_s_3090_);
lean_dec_ref(v_s_3090_);
v___x_3093_ = lean_string_append(v___x_3092_, v___x_3091_);
v___y_3071_ = v___x_3089_;
v___y_3072_ = v___x_3093_;
goto v___jp_3070_;
}
else
{
lean_object* v_n_3094_; lean_object* v___x_3095_; 
v_n_3094_ = lean_ctor_get(v_id_3078_, 0);
lean_inc_ref(v_n_3094_);
lean_dec_ref_known(v_id_3078_, 1);
v___x_3095_ = l_Lean_JsonNumber_toString(v_n_3094_);
v___y_3071_ = v___x_3089_;
v___y_3072_ = v___x_3095_;
goto v___jp_3070_;
}
}
}
else
{
lean_object* v___x_3103_; 
lean_dec(v_id_3078_);
lean_del_object(v___x_3068_);
lean_inc(v_result_3079_);
v___x_3103_ = lean_apply_1(v_inst_3063_, v_result_3079_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3118_; 
lean_del_object(v___x_3081_);
lean_dec(v_expectedID_3062_);
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3118_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3118_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3108_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__2));
v___x_3109_ = l_Lean_Json_compress(v_result_3079_);
v___x_3110_ = lean_string_append(v___x_3108_, v___x_3109_);
lean_dec_ref(v___x_3109_);
v___x_3111_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_3112_ = lean_string_append(v___x_3110_, v___x_3111_);
v___x_3113_ = lean_string_append(v___x_3112_, v_a_3104_);
lean_dec(v_a_3104_);
v___x_3114_ = lean_mk_io_user_error(v___x_3113_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 1);
lean_ctor_set(v___x_3106_, 0, v___x_3114_);
v___x_3116_ = v___x_3106_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v_result_3079_);
v_a_3119_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3121_ = v___x_3103_;
v_isShared_3122_ = v_isSharedCheck_3129_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3103_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3129_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3082_ == 0)
{
lean_ctor_set_tag(v___x_3081_, 0);
lean_ctor_set(v___x_3081_, 1, v_a_3119_);
lean_ctor_set(v___x_3081_, 0, v_expectedID_3062_);
v___x_3124_ = v___x_3081_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_expectedID_3062_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3126_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set_tag(v___x_3121_, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3124_);
v___x_3126_ = v___x_3121_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___y_3135_; 
lean_del_object(v___x_3068_);
lean_dec_ref(v_inst_3063_);
lean_dec(v_expectedID_3062_);
v___x_3131_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__3));
v___x_3132_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_3133_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_3066_))
{
case 0:
{
lean_object* v_id_3144_; lean_object* v_method_3145_; lean_object* v_params_x3f_3146_; lean_object* v___x_3147_; lean_object* v___y_3149_; 
v_id_3144_ = lean_ctor_get(v_a_3066_, 0);
lean_inc(v_id_3144_);
v_method_3145_ = lean_ctor_get(v_a_3066_, 1);
lean_inc_ref(v_method_3145_);
v_params_x3f_3146_ = lean_ctor_get(v_a_3066_, 2);
lean_inc(v_params_x3f_3146_);
lean_dec_ref_known(v_a_3066_, 3);
v___x_3147_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3144_) == 0)
{
lean_object* v_s_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_s_3160_ = lean_ctor_get(v_id_3144_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_id_3144_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v_id_3144_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_s_3160_);
lean_dec(v_id_3144_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set_tag(v___x_3162_, 3);
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_s_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
v___y_3149_ = v___x_3165_;
goto v___jp_3148_;
}
}
}
else
{
lean_object* v_n_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
v_n_3168_ = lean_ctor_get(v_id_3144_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_id_3144_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v_id_3144_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_n_3168_);
lean_dec(v_id_3144_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set_tag(v___x_3170_, 2);
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_n_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
v___y_3149_ = v___x_3173_;
goto v___jp_3148_;
}
}
}
v___jp_3148_:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3147_);
lean_ctor_set(v___x_3150_, 1, v___y_3149_);
v___x_3151_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3152_, 0, v_method_3145_);
v___x_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3151_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = lean_box(0);
v___x_3155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3153_);
lean_ctor_set(v___x_3155_, 1, v___x_3154_);
v___x_3156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3150_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3158_ = l_Lean_Json_opt___redArg(v___x_3132_, v___x_3157_, v_params_x3f_3146_);
v___x_3159_ = l_List_appendTR___redArg(v___x_3156_, v___x_3158_);
v___y_3135_ = v___x_3159_;
goto v___jp_3134_;
}
}
case 1:
{
lean_object* v_method_3176_; lean_object* v_params_x3f_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_method_3176_ = lean_ctor_get(v_a_3066_, 0);
lean_inc_ref(v_method_3176_);
v_params_x3f_3177_ = lean_ctor_get(v_a_3066_, 1);
lean_inc(v_params_x3f_3177_);
lean_dec_ref_known(v_a_3066_, 2);
v___x_3178_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3179_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3179_, 0, v_method_3176_);
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3178_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3182_ = l_Lean_Json_opt___redArg(v___x_3132_, v___x_3181_, v_params_x3f_3177_);
v___x_3183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3180_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___y_3135_ = v___x_3183_;
goto v___jp_3134_;
}
case 2:
{
lean_object* v_id_3184_; lean_object* v_result_3185_; lean_object* v___x_3186_; lean_object* v___y_3188_; 
v_id_3184_ = lean_ctor_get(v_a_3066_, 0);
lean_inc(v_id_3184_);
v_result_3185_ = lean_ctor_get(v_a_3066_, 1);
lean_inc(v_result_3185_);
lean_dec_ref_known(v_a_3066_, 2);
v___x_3186_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3184_) == 0)
{
lean_object* v_s_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
v_s_3195_ = lean_ctor_get(v_id_3184_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_id_3184_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v_id_3184_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_s_3195_);
lean_dec(v_id_3184_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set_tag(v___x_3197_, 3);
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_s_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
v___y_3188_ = v___x_3200_;
goto v___jp_3187_;
}
}
}
else
{
lean_object* v_n_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
v_n_3203_ = lean_ctor_get(v_id_3184_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_id_3184_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v_id_3184_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_n_3203_);
lean_dec(v_id_3184_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
lean_ctor_set_tag(v___x_3205_, 2);
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_n_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
v___y_3188_ = v___x_3208_;
goto v___jp_3187_;
}
}
}
v___jp_3187_:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3186_);
lean_ctor_set(v___x_3189_, 1, v___y_3188_);
v___x_3190_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v_result_3185_);
v___x_3192_ = lean_box(0);
v___x_3193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3191_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3189_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
v___y_3135_ = v___x_3194_;
goto v___jp_3134_;
}
}
default: 
{
lean_object* v_id_3211_; uint8_t v_code_3212_; lean_object* v_message_3213_; lean_object* v_data_x3f_3214_; lean_object* v___x_3215_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___x_3235_; lean_object* v___y_3237_; 
v_id_3211_ = lean_ctor_get(v_a_3066_, 0);
lean_inc(v_id_3211_);
v_code_3212_ = lean_ctor_get_uint8(v_a_3066_, sizeof(void*)*3);
v_message_3213_ = lean_ctor_get(v_a_3066_, 1);
lean_inc_ref(v_message_3213_);
v_data_x3f_3214_ = lean_ctor_get(v_a_3066_, 2);
lean_inc(v_data_x3f_3214_);
lean_dec_ref_known(v_a_3066_, 3);
v___x_3215_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_3235_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3211_) == 0)
{
lean_object* v_s_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
v_s_3253_ = lean_ctor_get(v_id_3211_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_id_3211_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v_id_3211_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_s_3253_);
lean_dec(v_id_3211_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
lean_ctor_set_tag(v___x_3255_, 3);
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_s_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
v___y_3237_ = v___x_3258_;
goto v___jp_3236_;
}
}
}
else
{
lean_object* v_n_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
v_n_3261_ = lean_ctor_get(v_id_3211_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_id_3211_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v_id_3211_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_n_3261_);
lean_dec(v_id_3211_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
lean_ctor_set_tag(v___x_3263_, 2);
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_n_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
v___y_3237_ = v___x_3266_;
goto v___jp_3236_;
}
}
}
v___jp_3216_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3218_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___y_3218_);
lean_ctor_set(v___x_3221_, 1, v___y_3220_);
v___x_3222_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3223_, 0, v_message_3213_);
v___x_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3222_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = lean_box(0);
v___x_3226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3224_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3221_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
v___x_3228_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3229_ = l_Lean_Json_opt___redArg(v___x_3215_, v___x_3228_, v_data_x3f_3214_);
v___x_3230_ = l_List_appendTR___redArg(v___x_3227_, v___x_3229_);
v___x_3231_ = l_Lean_Json_mkObj(v___x_3230_);
lean_dec(v___x_3230_);
lean_inc_ref(v___y_3217_);
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___y_3217_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
lean_ctor_set(v___x_3233_, 1, v___x_3225_);
v___x_3234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___y_3219_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___y_3135_ = v___x_3234_;
goto v___jp_3134_;
}
v___jp_3236_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3235_);
lean_ctor_set(v___x_3238_, 1, v___y_3237_);
v___x_3239_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3240_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3212_)
{
case 0:
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3241_;
goto v___jp_3216_;
}
case 1:
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3242_;
goto v___jp_3216_;
}
case 2:
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3243_;
goto v___jp_3216_;
}
case 3:
{
lean_object* v___x_3244_; 
v___x_3244_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3244_;
goto v___jp_3216_;
}
case 4:
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3245_;
goto v___jp_3216_;
}
case 5:
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3246_;
goto v___jp_3216_;
}
case 6:
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3247_;
goto v___jp_3216_;
}
case 7:
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3248_;
goto v___jp_3216_;
}
case 8:
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3249_;
goto v___jp_3216_;
}
case 9:
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3250_;
goto v___jp_3216_;
}
case 10:
{
lean_object* v___x_3251_; 
v___x_3251_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3251_;
goto v___jp_3216_;
}
default: 
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3240_;
v___y_3219_ = v___x_3238_;
v___y_3220_ = v___x_3252_;
goto v___jp_3216_;
}
}
}
}
}
v___jp_3134_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3133_);
lean_ctor_set(v___x_3136_, 1, v___y_3135_);
v___x_3137_ = l_Lean_Json_mkObj(v___x_3136_);
lean_dec_ref_known(v___x_3136_, 2);
v___x_3138_ = l_Lean_Json_compress(v___x_3137_);
v___x_3139_ = lean_string_append(v___x_3131_, v___x_3138_);
lean_dec_ref(v___x_3138_);
v___x_3140_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_3141_ = lean_string_append(v___x_3139_, v___x_3140_);
v___x_3142_ = lean_mk_io_user_error(v___x_3141_);
v___x_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
return v___x_3143_;
}
}
v___jp_3070_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3076_; 
v___x_3073_ = lean_string_append(v___y_3071_, v___y_3072_);
lean_dec_ref(v___y_3072_);
v___x_3074_ = lean_mk_io_user_error(v___x_3073_);
if (v_isShared_3069_ == 0)
{
lean_ctor_set_tag(v___x_3068_, 1);
lean_ctor_set(v___x_3068_, 0, v___x_3074_);
v___x_3076_ = v___x_3068_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v_inst_3063_);
lean_dec(v_expectedID_3062_);
v_a_3270_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3065_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3065_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* v_h_3278_, lean_object* v_nBytes_3279_, lean_object* v_expectedID_3280_, lean_object* v_inst_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_IO_FS_Stream_readResponseAs___redArg(v_h_3278_, v_nBytes_3279_, v_expectedID_3280_, v_inst_3281_);
lean_dec(v_nBytes_3279_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object* v_h_3284_, lean_object* v_nBytes_3285_, lean_object* v_expectedID_3286_, lean_object* v_00_u03b1_3287_, lean_object* v_inst_3288_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_IO_FS_Stream_readResponseAs___redArg(v_h_3284_, v_nBytes_3285_, v_expectedID_3286_, v_inst_3288_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object* v_h_3291_, lean_object* v_nBytes_3292_, lean_object* v_expectedID_3293_, lean_object* v_00_u03b1_3294_, lean_object* v_inst_3295_, lean_object* v_a_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_IO_FS_Stream_readResponseAs(v_h_3291_, v_nBytes_3292_, v_expectedID_3293_, v_00_u03b1_3294_, v_inst_3295_);
lean_dec(v_nBytes_3292_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(lean_object* v_k_3298_, lean_object* v_x_3299_){
_start:
{
if (lean_obj_tag(v_x_3299_) == 0)
{
lean_object* v___x_3300_; 
lean_dec_ref(v_k_3298_);
v___x_3300_ = lean_box(0);
return v___x_3300_;
}
else
{
lean_object* v_val_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v_val_3301_ = lean_ctor_get(v_x_3299_, 0);
lean_inc(v_val_3301_);
lean_dec_ref_known(v_x_3299_, 1);
v___x_3302_ = l_Lean_Json_Structured_toJson(v_val_3301_);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v_k_3298_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(lean_object* v_k_3306_, lean_object* v_x_3307_){
_start:
{
if (lean_obj_tag(v_x_3307_) == 0)
{
lean_object* v___x_3308_; 
lean_dec_ref(v_k_3306_);
v___x_3308_ = lean_box(0);
return v___x_3308_;
}
else
{
lean_object* v_val_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_val_3309_ = lean_ctor_get(v_x_3307_, 0);
lean_inc(v_val_3309_);
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v_k_3306_);
lean_ctor_set(v___x_3310_, 1, v_val_3309_);
v___x_3311_ = lean_box(0);
v___x_3312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
return v___x_3312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* v_k_3313_, lean_object* v_x_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(v_k_3313_, v_x_3314_);
lean_dec(v_x_3314_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object* v_h_3316_, lean_object* v_m_3317_){
_start:
{
lean_object* v___x_3319_; lean_object* v___y_3321_; 
v___x_3319_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_3317_))
{
case 0:
{
lean_object* v_id_3325_; lean_object* v_method_3326_; lean_object* v_params_x3f_3327_; lean_object* v___x_3328_; lean_object* v___y_3330_; 
v_id_3325_ = lean_ctor_get(v_m_3317_, 0);
lean_inc(v_id_3325_);
v_method_3326_ = lean_ctor_get(v_m_3317_, 1);
lean_inc_ref(v_method_3326_);
v_params_x3f_3327_ = lean_ctor_get(v_m_3317_, 2);
lean_inc(v_params_x3f_3327_);
lean_dec_ref_known(v_m_3317_, 3);
v___x_3328_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3325_))
{
case 0:
{
lean_object* v_s_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
v_s_3341_ = lean_ctor_get(v_id_3325_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v_id_3325_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v_id_3325_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_s_3341_);
lean_dec(v_id_3325_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set_tag(v___x_3343_, 3);
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_s_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
v___y_3330_ = v___x_3346_;
goto v___jp_3329_;
}
}
}
case 1:
{
lean_object* v_n_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
v_n_3349_ = lean_ctor_get(v_id_3325_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_id_3325_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v_id_3325_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_n_3349_);
lean_dec(v_id_3325_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set_tag(v___x_3351_, 2);
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_n_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
v___y_3330_ = v___x_3354_;
goto v___jp_3329_;
}
}
}
default: 
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_box(0);
v___y_3330_ = v___x_3357_;
goto v___jp_3329_;
}
}
v___jp_3329_:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3328_);
lean_ctor_set(v___x_3331_, 1, v___y_3330_);
v___x_3332_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3333_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3333_, 0, v_method_3326_);
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = lean_box(0);
v___x_3336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3331_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3339_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(v___x_3338_, v_params_x3f_3327_);
v___x_3340_ = l_List_appendTR___redArg(v___x_3337_, v___x_3339_);
v___y_3321_ = v___x_3340_;
goto v___jp_3320_;
}
}
case 1:
{
lean_object* v_method_3358_; lean_object* v_params_x3f_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3371_; 
v_method_3358_ = lean_ctor_get(v_m_3317_, 0);
v_params_x3f_3359_ = lean_ctor_get(v_m_3317_, 1);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_m_3317_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3361_ = v_m_3317_;
v_isShared_3362_ = v_isSharedCheck_3371_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_params_x3f_3359_);
lean_inc(v_method_3358_);
lean_dec(v_m_3317_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3371_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3363_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3364_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3364_, 0, v_method_3358_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set_tag(v___x_3361_, 0);
lean_ctor_set(v___x_3361_, 1, v___x_3364_);
lean_ctor_set(v___x_3361_, 0, v___x_3363_);
v___x_3366_ = v___x_3361_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3367_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3368_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(v___x_3367_, v_params_x3f_3359_);
v___x_3369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3366_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___y_3321_ = v___x_3369_;
goto v___jp_3320_;
}
}
}
case 2:
{
lean_object* v_id_3372_; lean_object* v_result_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3405_; 
v_id_3372_ = lean_ctor_get(v_m_3317_, 0);
v_result_3373_ = lean_ctor_get(v_m_3317_, 1);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_m_3317_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3375_ = v_m_3317_;
v_isShared_3376_ = v_isSharedCheck_3405_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_result_3373_);
lean_inc(v_id_3372_);
lean_dec(v_m_3317_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3405_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___y_3379_; 
v___x_3377_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3372_))
{
case 0:
{
lean_object* v_s_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
v_s_3388_ = lean_ctor_get(v_id_3372_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v_id_3372_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v_id_3372_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_s_3388_);
lean_dec(v_id_3372_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
lean_ctor_set_tag(v___x_3390_, 3);
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_s_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
v___y_3379_ = v___x_3393_;
goto v___jp_3378_;
}
}
}
case 1:
{
lean_object* v_n_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
v_n_3396_ = lean_ctor_get(v_id_3372_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_id_3372_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v_id_3372_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_n_3396_);
lean_dec(v_id_3372_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
lean_ctor_set_tag(v___x_3398_, 2);
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_n_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
v___y_3379_ = v___x_3401_;
goto v___jp_3378_;
}
}
}
default: 
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_box(0);
v___y_3379_ = v___x_3404_;
goto v___jp_3378_;
}
}
v___jp_3378_:
{
lean_object* v___x_3381_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 0);
lean_ctor_set(v___x_3375_, 1, v___y_3379_);
lean_ctor_set(v___x_3375_, 0, v___x_3377_);
v___x_3381_ = v___x_3375_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___y_3379_);
v___x_3381_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3382_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
lean_ctor_set(v___x_3383_, 1, v_result_3373_);
v___x_3384_ = lean_box(0);
v___x_3385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3381_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___y_3321_ = v___x_3386_;
goto v___jp_3320_;
}
}
}
}
default: 
{
lean_object* v_id_3406_; uint8_t v_code_3407_; lean_object* v_message_3408_; lean_object* v_data_x3f_3409_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___x_3429_; lean_object* v___y_3431_; 
v_id_3406_ = lean_ctor_get(v_m_3317_, 0);
lean_inc(v_id_3406_);
v_code_3407_ = lean_ctor_get_uint8(v_m_3317_, sizeof(void*)*3);
v_message_3408_ = lean_ctor_get(v_m_3317_, 1);
lean_inc_ref(v_message_3408_);
v_data_x3f_3409_ = lean_ctor_get(v_m_3317_, 2);
lean_inc(v_data_x3f_3409_);
lean_dec_ref_known(v_m_3317_, 3);
v___x_3429_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3406_))
{
case 0:
{
lean_object* v_s_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
v_s_3447_ = lean_ctor_get(v_id_3406_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_id_3406_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v_id_3406_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_s_3447_);
lean_dec(v_id_3406_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
lean_ctor_set_tag(v___x_3449_, 3);
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_s_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
v___y_3431_ = v___x_3452_;
goto v___jp_3430_;
}
}
}
case 1:
{
lean_object* v_n_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
v_n_3455_ = lean_ctor_get(v_id_3406_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_id_3406_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v_id_3406_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_n_3455_);
lean_dec(v_id_3406_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
lean_ctor_set_tag(v___x_3457_, 2);
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_n_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
v___y_3431_ = v___x_3460_;
goto v___jp_3430_;
}
}
}
default: 
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_box(0);
v___y_3431_ = v___x_3463_;
goto v___jp_3430_;
}
}
v___jp_3410_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
lean_inc(v___y_3414_);
lean_inc_ref(v___y_3413_);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___y_3413_);
lean_ctor_set(v___x_3415_, 1, v___y_3414_);
v___x_3416_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3417_, 0, v_message_3408_);
v___x_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = lean_box(0);
v___x_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3415_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3423_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(v___x_3422_, v_data_x3f_3409_);
lean_dec(v_data_x3f_3409_);
v___x_3424_ = l_List_appendTR___redArg(v___x_3421_, v___x_3423_);
v___x_3425_ = l_Lean_Json_mkObj(v___x_3424_);
lean_dec(v___x_3424_);
lean_inc_ref(v___y_3412_);
v___x_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___y_3412_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v___x_3419_);
v___x_3428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___y_3411_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___y_3321_ = v___x_3428_;
goto v___jp_3320_;
}
v___jp_3430_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3429_);
lean_ctor_set(v___x_3432_, 1, v___y_3431_);
v___x_3433_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3434_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3407_)
{
case 0:
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3435_;
goto v___jp_3410_;
}
case 1:
{
lean_object* v___x_3436_; 
v___x_3436_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3436_;
goto v___jp_3410_;
}
case 2:
{
lean_object* v___x_3437_; 
v___x_3437_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3437_;
goto v___jp_3410_;
}
case 3:
{
lean_object* v___x_3438_; 
v___x_3438_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3438_;
goto v___jp_3410_;
}
case 4:
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3439_;
goto v___jp_3410_;
}
case 5:
{
lean_object* v___x_3440_; 
v___x_3440_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3440_;
goto v___jp_3410_;
}
case 6:
{
lean_object* v___x_3441_; 
v___x_3441_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3441_;
goto v___jp_3410_;
}
case 7:
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3442_;
goto v___jp_3410_;
}
case 8:
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3443_;
goto v___jp_3410_;
}
case 9:
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3444_;
goto v___jp_3410_;
}
case 10:
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3445_;
goto v___jp_3410_;
}
default: 
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
v___y_3414_ = v___x_3446_;
goto v___jp_3410_;
}
}
}
}
}
v___jp_3320_:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3319_);
lean_ctor_set(v___x_3322_, 1, v___y_3321_);
v___x_3323_ = l_Lean_Json_mkObj(v___x_3322_);
lean_dec_ref_known(v___x_3322_, 2);
v___x_3324_ = l_IO_FS_Stream_writeJson(v_h_3316_, v___x_3323_);
return v___x_3324_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object* v_h_3464_, lean_object* v_m_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_IO_FS_Stream_writeMessage(v_h_3464_, v_m_3465_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg(lean_object* v_inst_3468_, lean_object* v_h_3469_, lean_object* v_r_3470_){
_start:
{
lean_object* v_id_3472_; lean_object* v_method_3473_; lean_object* v_param_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3494_; 
v_id_3472_ = lean_ctor_get(v_r_3470_, 0);
v_method_3473_ = lean_ctor_get(v_r_3470_, 1);
v_param_3474_ = lean_ctor_get(v_r_3470_, 2);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_r_3470_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3476_ = v_r_3470_;
v_isShared_3477_ = v_isSharedCheck_3494_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_param_3474_);
lean_inc(v_method_3473_);
lean_inc(v_id_3472_);
lean_dec(v_r_3470_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3494_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___y_3479_; lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3468_, v_param_3474_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v___x_3485_; 
lean_dec_ref_known(v___x_3484_, 1);
v___x_3485_ = lean_box(0);
v___y_3479_ = v___x_3485_;
goto v___jp_3478_;
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
v_a_3486_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3484_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3484_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
v___y_3479_ = v___x_3491_;
goto v___jp_3478_;
}
}
}
v___jp_3478_:
{
lean_object* v___x_3481_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 2, v___y_3479_);
v___x_3481_ = v___x_3476_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_id_3472_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_method_3473_);
lean_ctor_set(v_reuseFailAlloc_3483_, 2, v___y_3479_);
v___x_3481_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
lean_object* v___x_3482_; 
v___x_3482_ = l_IO_FS_Stream_writeMessage(v_h_3469_, v___x_3481_);
return v___x_3482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg___boxed(lean_object* v_inst_3495_, lean_object* v_h_3496_, lean_object* v_r_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_IO_FS_Stream_writeRequest___redArg(v_inst_3495_, v_h_3496_, v_r_3497_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object* v_00_u03b1_3500_, lean_object* v_inst_3501_, lean_object* v_h_3502_, lean_object* v_r_3503_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_IO_FS_Stream_writeRequest___redArg(v_inst_3501_, v_h_3502_, v_r_3503_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___boxed(lean_object* v_00_u03b1_3506_, lean_object* v_inst_3507_, lean_object* v_h_3508_, lean_object* v_r_3509_, lean_object* v_a_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_IO_FS_Stream_writeRequest(v_00_u03b1_3506_, v_inst_3507_, v_h_3508_, v_r_3509_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg(lean_object* v_inst_3512_, lean_object* v_h_3513_, lean_object* v_n_3514_){
_start:
{
lean_object* v_method_3516_; lean_object* v_param_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3537_; 
v_method_3516_ = lean_ctor_get(v_n_3514_, 0);
v_param_3517_ = lean_ctor_get(v_n_3514_, 1);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_n_3514_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3519_ = v_n_3514_;
v_isShared_3520_ = v_isSharedCheck_3537_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_param_3517_);
lean_inc(v_method_3516_);
lean_dec(v_n_3514_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3537_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___y_3522_; lean_object* v___x_3527_; 
v___x_3527_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3512_, v_param_3517_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v___x_3528_; 
lean_dec_ref_known(v___x_3527_, 1);
v___x_3528_ = lean_box(0);
v___y_3522_ = v___x_3528_;
goto v___jp_3521_;
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
v_a_3529_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3527_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3527_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
v___y_3522_ = v___x_3534_;
goto v___jp_3521_;
}
}
}
v___jp_3521_:
{
lean_object* v___x_3524_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set_tag(v___x_3519_, 1);
lean_ctor_set(v___x_3519_, 1, v___y_3522_);
v___x_3524_ = v___x_3519_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_method_3516_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v___y_3522_);
v___x_3524_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_IO_FS_Stream_writeMessage(v_h_3513_, v___x_3524_);
return v___x_3525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg___boxed(lean_object* v_inst_3538_, lean_object* v_h_3539_, lean_object* v_n_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_IO_FS_Stream_writeNotification___redArg(v_inst_3538_, v_h_3539_, v_n_3540_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object* v_00_u03b1_3543_, lean_object* v_inst_3544_, lean_object* v_h_3545_, lean_object* v_n_3546_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_IO_FS_Stream_writeNotification___redArg(v_inst_3544_, v_h_3545_, v_n_3546_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___boxed(lean_object* v_00_u03b1_3549_, lean_object* v_inst_3550_, lean_object* v_h_3551_, lean_object* v_n_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_IO_FS_Stream_writeNotification(v_00_u03b1_3549_, v_inst_3550_, v_h_3551_, v_n_3552_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg(lean_object* v_inst_3555_, lean_object* v_h_3556_, lean_object* v_r_3557_){
_start:
{
lean_object* v_id_3559_; lean_object* v_result_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3569_; 
v_id_3559_ = lean_ctor_get(v_r_3557_, 0);
v_result_3560_ = lean_ctor_get(v_r_3557_, 1);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_r_3557_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3562_ = v_r_3557_;
v_isShared_3563_ = v_isSharedCheck_3569_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_result_3560_);
lean_inc(v_id_3559_);
lean_dec(v_r_3557_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3569_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3564_ = lean_apply_1(v_inst_3555_, v_result_3560_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set_tag(v___x_3562_, 2);
lean_ctor_set(v___x_3562_, 1, v___x_3564_);
v___x_3566_ = v___x_3562_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_id_3559_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3567_; 
v___x_3567_ = l_IO_FS_Stream_writeMessage(v_h_3556_, v___x_3566_);
return v___x_3567_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg___boxed(lean_object* v_inst_3570_, lean_object* v_h_3571_, lean_object* v_r_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_IO_FS_Stream_writeResponse___redArg(v_inst_3570_, v_h_3571_, v_r_3572_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object* v_00_u03b1_3575_, lean_object* v_inst_3576_, lean_object* v_h_3577_, lean_object* v_r_3578_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_IO_FS_Stream_writeResponse___redArg(v_inst_3576_, v_h_3577_, v_r_3578_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___boxed(lean_object* v_00_u03b1_3581_, lean_object* v_inst_3582_, lean_object* v_h_3583_, lean_object* v_r_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_IO_FS_Stream_writeResponse(v_00_u03b1_3581_, v_inst_3582_, v_h_3583_, v_r_3584_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object* v_h_3587_, lean_object* v_e_3588_){
_start:
{
lean_object* v_id_3590_; uint8_t v_code_3591_; lean_object* v_message_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3601_; 
v_id_3590_ = lean_ctor_get(v_e_3588_, 0);
v_code_3591_ = lean_ctor_get_uint8(v_e_3588_, sizeof(void*)*3);
v_message_3592_ = lean_ctor_get(v_e_3588_, 1);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_e_3588_);
if (v_isSharedCheck_3601_ == 0)
{
lean_object* v_unused_3602_; 
v_unused_3602_ = lean_ctor_get(v_e_3588_, 2);
lean_dec(v_unused_3602_);
v___x_3594_ = v_e_3588_;
v_isShared_3595_ = v_isSharedCheck_3601_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_message_3592_);
lean_inc(v_id_3590_);
lean_dec(v_e_3588_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3601_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3596_; lean_object* v___x_3598_; 
v___x_3596_ = lean_box(0);
if (v_isShared_3595_ == 0)
{
lean_ctor_set_tag(v___x_3594_, 3);
lean_ctor_set(v___x_3594_, 2, v___x_3596_);
v___x_3598_ = v___x_3594_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_id_3590_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_message_3592_);
lean_ctor_set(v_reuseFailAlloc_3600_, 2, v___x_3596_);
lean_ctor_set_uint8(v_reuseFailAlloc_3600_, sizeof(void*)*3, v_code_3591_);
v___x_3598_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3599_; 
v___x_3599_ = l_IO_FS_Stream_writeMessage(v_h_3587_, v___x_3598_);
return v___x_3599_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object* v_h_3603_, lean_object* v_e_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_IO_FS_Stream_writeResponseError(v_h_3603_, v_e_3604_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* v_inst_3607_, lean_object* v_h_3608_, lean_object* v_e_3609_){
_start:
{
lean_object* v_id_3611_; uint8_t v_code_3612_; lean_object* v_message_3613_; lean_object* v_data_x3f_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3634_; 
v_id_3611_ = lean_ctor_get(v_e_3609_, 0);
v_code_3612_ = lean_ctor_get_uint8(v_e_3609_, sizeof(void*)*3);
v_message_3613_ = lean_ctor_get(v_e_3609_, 1);
v_data_x3f_3614_ = lean_ctor_get(v_e_3609_, 2);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_e_3609_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3616_ = v_e_3609_;
v_isShared_3617_ = v_isSharedCheck_3634_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_data_x3f_3614_);
lean_inc(v_message_3613_);
lean_inc(v_id_3611_);
lean_dec(v_e_3609_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3634_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___y_3619_; 
if (lean_obj_tag(v_data_x3f_3614_) == 0)
{
lean_object* v___x_3624_; 
lean_dec_ref(v_inst_3607_);
v___x_3624_ = lean_box(0);
v___y_3619_ = v___x_3624_;
goto v___jp_3618_;
}
else
{
lean_object* v_val_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3633_; 
v_val_3625_ = lean_ctor_get(v_data_x3f_3614_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_data_x3f_3614_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3627_ = v_data_x3f_3614_;
v_isShared_3628_ = v_isSharedCheck_3633_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_val_3625_);
lean_dec(v_data_x3f_3614_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3633_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3629_ = lean_apply_1(v_inst_3607_, v_val_3625_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v___x_3629_);
v___x_3631_ = v___x_3627_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
v___y_3619_ = v___x_3631_;
goto v___jp_3618_;
}
}
}
v___jp_3618_:
{
lean_object* v___x_3621_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set_tag(v___x_3616_, 3);
lean_ctor_set(v___x_3616_, 2, v___y_3619_);
v___x_3621_ = v___x_3616_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_id_3611_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_message_3613_);
lean_ctor_set(v_reuseFailAlloc_3623_, 2, v___y_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3623_, sizeof(void*)*3, v_code_3612_);
v___x_3621_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_IO_FS_Stream_writeMessage(v_h_3608_, v___x_3621_);
return v___x_3622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object* v_inst_3635_, lean_object* v_h_3636_, lean_object* v_e_3637_, lean_object* v_a_3638_){
_start:
{
lean_object* v_res_3639_; 
v_res_3639_ = l_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3635_, v_h_3636_, v_e_3637_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object* v_00_u03b1_3640_, lean_object* v_inst_3641_, lean_object* v_h_3642_, lean_object* v_e_3643_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3641_, v_h_3642_, v_e_3643_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object* v_00_u03b1_3646_, lean_object* v_inst_3647_, lean_object* v_h_3648_, lean_object* v_e_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_IO_FS_Stream_writeResponseErrorWithData(v_00_u03b1_3646_, v_inst_3647_, v_h_3648_, v_e_3649_);
return v_res_3651_;
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
