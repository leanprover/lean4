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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Option_toJson___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IO_FS_Stream_readJson(lean_object*, lean_object*);
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
lean_object* l_Lean_IO_FS_Stream_writeJson(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object* v_x_705_){
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
v___x_716_ = l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_712_);
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
v___x_800_ = l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_796_);
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
v___x_1408_ = l_Lean_Option_toJson___redArg(v___x_1400_, v_params_x3f_1407_);
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
uint32_t v___x_1634_; uint32_t v___x_1635_; uint8_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1634_ = lean_string_utf8_get_fast(v_fst_1630_, v_snd_1631_);
v___x_1635_ = 34;
v___x_1636_ = lean_uint32_dec_eq(v___x_1634_, v___x_1635_);
v___x_1637_ = lean_bool_not(v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1647_; 
lean_inc(v_snd_1631_);
lean_inc(v_fst_1630_);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_a_1629_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; lean_object* v_unused_1649_; 
v_unused_1648_ = lean_ctor_get(v_a_1629_, 1);
lean_dec(v_unused_1648_);
v_unused_1649_ = lean_ctor_get(v_a_1629_, 0);
lean_dec(v_unused_1649_);
v___x_1639_ = v_a_1629_;
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
else
{
lean_dec(v_a_1629_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = lean_string_utf8_next_fast(v_fst_1630_, v_snd_1631_);
lean_dec(v_snd_1631_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 1, v___x_1641_);
v___x_1643_ = v___x_1639_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_fst_1630_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_1645_ = l_Lean_Json_Parser_strCore(v___x_1644_, v___x_1643_);
return v___x_1645_;
}
}
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1));
v___x_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1651_, 0, v_a_1629_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
return v___x_1651_;
}
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_box(0);
v___x_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1653_, 0, v_a_1629_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1655_; 
lean_inc_ref(v_a_1654_);
v___x_1655_ = l_Lean_Json_Parser_num(v_a_1654_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_pos_1656_; lean_object* v_res_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v_a_1654_);
v_pos_1656_ = lean_ctor_get(v___x_1655_, 0);
v_res_1657_ = lean_ctor_get(v___x_1655_, 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1659_ = v___x_1655_;
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_res_1657_);
lean_inc(v_pos_1656_);
lean_dec(v___x_1655_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_res_1657_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_pos_1656_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
lean_object* v_pos_1666_; lean_object* v_err_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1720_; 
v_pos_1666_ = lean_ctor_get(v___x_1655_, 0);
v_err_1667_ = lean_ctor_get(v___x_1655_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1669_ = v___x_1655_;
v_isShared_1670_ = v_isSharedCheck_1720_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_err_1667_);
lean_inc(v_pos_1666_);
lean_dec(v___x_1655_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1720_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v_snd_1671_; lean_object* v_snd_1672_; uint8_t v___x_1673_; 
v_snd_1671_ = lean_ctor_get(v_a_1654_, 1);
lean_inc(v_snd_1671_);
lean_dec_ref(v_a_1654_);
v_snd_1672_ = lean_ctor_get(v_pos_1666_, 1);
v___x_1673_ = lean_nat_dec_eq(v_snd_1671_, v_snd_1672_);
lean_dec(v_snd_1671_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1675_; 
if (v_isShared_1670_ == 0)
{
v___x_1675_ = v___x_1669_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_pos_1666_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_err_1667_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
else
{
lean_object* v___x_1677_; 
lean_inc(v_snd_1672_);
lean_del_object(v___x_1669_);
lean_dec(v_err_1667_);
v___x_1677_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v_pos_1666_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_pos_1678_; lean_object* v_res_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1687_; 
lean_dec(v_snd_1672_);
v_pos_1678_ = lean_ctor_get(v___x_1677_, 0);
v_res_1679_ = lean_ctor_get(v___x_1677_, 1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1681_ = v___x_1677_;
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_res_1679_);
lean_inc(v_pos_1678_);
lean_dec(v___x_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_res_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___x_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_pos_1678_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
else
{
lean_object* v_pos_1688_; lean_object* v_err_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1719_; 
v_pos_1688_ = lean_ctor_get(v___x_1677_, 0);
v_err_1689_ = lean_ctor_get(v___x_1677_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1691_ = v___x_1677_;
v_isShared_1692_ = v_isSharedCheck_1719_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_err_1689_);
lean_inc(v_pos_1688_);
lean_dec(v___x_1677_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1719_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v_snd_1693_; uint8_t v___x_1694_; 
v_snd_1693_ = lean_ctor_get(v_pos_1688_, 1);
v___x_1694_ = lean_nat_dec_eq(v_snd_1672_, v_snd_1693_);
lean_dec(v_snd_1672_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1696_; 
if (v_isShared_1692_ == 0)
{
v___x_1696_ = v___x_1691_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_pos_1688_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_err_1689_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_del_object(v___x_1691_);
lean_dec(v_err_1689_);
v___x_1698_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___x_1699_ = l_Std_Internal_Parsec_String_pstring(v___x_1698_, v_pos_1688_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_pos_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1708_; 
v_pos_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v___x_1699_, 1);
lean_dec(v_unused_1709_);
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_pos_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = lean_box(2);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v___x_1704_);
v___x_1706_ = v___x_1702_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_pos_1700_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
else
{
lean_object* v_pos_1710_; lean_object* v_err_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v_pos_1710_ = lean_ctor_get(v___x_1699_, 0);
v_err_1711_ = lean_ctor_get(v___x_1699_, 1);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1699_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_err_1711_);
lean_inc(v_pos_1710_);
lean_dec(v___x_1699_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_pos_1710_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_err_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object* v_j_1721_, lean_object* v_k_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Json_getObjValD(v_j_1721_, v_k_1722_);
switch(lean_obj_tag(v___x_1723_))
{
case 3:
{
lean_object* v_s_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1732_; 
v_s_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1732_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_s_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1732_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set_tag(v___x_1726_, 0);
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_s_1724_);
v___x_1729_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
}
case 2:
{
lean_object* v_n_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1741_; 
v_n_1733_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1735_ = v___x_1723_;
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_n_1733_);
lean_dec(v___x_1723_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1741_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 1);
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_n_1733_);
v___x_1738_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
}
}
default: 
{
lean_object* v___x_1742_; 
lean_dec(v___x_1723_);
v___x_1742_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object* v_j_1743_, lean_object* v_k_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_j_1743_, v_k_1744_);
lean_dec_ref(v_k_1744_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object* v_j_1746_, lean_object* v_k_1747_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Json_getObjValD(v_j_1746_, v_k_1747_);
if (lean_obj_tag(v___x_1750_) == 2)
{
lean_object* v_n_1751_; lean_object* v_mantissa_1752_; lean_object* v_exponent_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v_n_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc_ref(v_n_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v_mantissa_1752_ = lean_ctor_get(v_n_1751_, 0);
lean_inc(v_mantissa_1752_);
v_exponent_1753_ = lean_ctor_get(v_n_1751_, 1);
lean_inc(v_exponent_1753_);
lean_dec_ref(v_n_1751_);
v___x_1754_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_1755_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_1757_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_1759_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_1761_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_1763_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_1765_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_1767_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_1769_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_1771_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_1773_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_1775_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_1777_ = lean_int_dec_eq(v_mantissa_1752_, v___x_1776_);
lean_dec(v_mantissa_1752_);
if (v___x_1777_ == 0)
{
lean_dec(v_exponent_1753_);
goto v___jp_1748_;
}
else
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1778_);
lean_dec(v_exponent_1753_);
if (v___x_1779_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_1780_;
}
}
}
else
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
lean_dec(v_mantissa_1752_);
v___x_1781_ = lean_unsigned_to_nat(0u);
v___x_1782_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1781_);
lean_dec(v_exponent_1753_);
if (v___x_1782_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_1783_;
}
}
}
else
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
lean_dec(v_mantissa_1752_);
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1784_);
lean_dec(v_exponent_1753_);
if (v___x_1785_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1786_; 
v___x_1786_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_1786_;
}
}
}
else
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
lean_dec(v_mantissa_1752_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1787_);
lean_dec(v_exponent_1753_);
if (v___x_1788_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_1789_;
}
}
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
lean_dec(v_mantissa_1752_);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1790_);
lean_dec(v_exponent_1753_);
if (v___x_1791_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1792_; 
v___x_1792_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_1792_;
}
}
}
else
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
lean_dec(v_mantissa_1752_);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1793_);
lean_dec(v_exponent_1753_);
if (v___x_1794_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1795_; 
v___x_1795_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_1795_;
}
}
}
else
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
lean_dec(v_mantissa_1752_);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1796_);
lean_dec(v_exponent_1753_);
if (v___x_1797_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_1798_;
}
}
}
else
{
lean_object* v___x_1799_; uint8_t v___x_1800_; 
lean_dec(v_mantissa_1752_);
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1799_);
lean_dec(v_exponent_1753_);
if (v___x_1800_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_1801_;
}
}
}
else
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
lean_dec(v_mantissa_1752_);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1802_);
lean_dec(v_exponent_1753_);
if (v___x_1803_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1804_; 
v___x_1804_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_1804_;
}
}
}
else
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
lean_dec(v_mantissa_1752_);
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1806_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1805_);
lean_dec(v_exponent_1753_);
if (v___x_1806_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_1807_;
}
}
}
else
{
lean_object* v___x_1808_; uint8_t v___x_1809_; 
lean_dec(v_mantissa_1752_);
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1809_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1808_);
lean_dec(v_exponent_1753_);
if (v___x_1809_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1810_; 
v___x_1810_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_1810_;
}
}
}
else
{
lean_object* v___x_1811_; uint8_t v___x_1812_; 
lean_dec(v_mantissa_1752_);
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = lean_nat_dec_eq(v_exponent_1753_, v___x_1811_);
lean_dec(v_exponent_1753_);
if (v___x_1812_ == 0)
{
goto v___jp_1748_;
}
else
{
lean_object* v___x_1813_; 
v___x_1813_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_1813_;
}
}
}
else
{
lean_dec(v___x_1750_);
goto v___jp_1748_;
}
v___jp_1748_:
{
lean_object* v___x_1749_; 
v___x_1749_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object* v_j_1814_, lean_object* v_k_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_j_1814_, v_k_1815_);
lean_dec_ref(v_k_1815_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object* v_j_1817_, lean_object* v_k_1818_){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = l_Lean_Json_getObjValD(v_j_1817_, v_k_1818_);
v___x_1820_ = l_Lean_Json_getStr_x3f(v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object* v_j_1821_, lean_object* v_k_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_j_1821_, v_k_1822_);
lean_dec_ref(v_k_1822_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object* v_input_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v_fst_1860_; lean_object* v_snd_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_fst_1860_ = lean_ctor_get(v_a_1834_, 0);
v_snd_1861_ = lean_ctor_get(v_a_1834_, 1);
v___x_1862_ = lean_string_utf8_byte_size(v_fst_1860_);
v___x_1863_ = lean_nat_dec_eq(v_snd_1861_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_2213_; 
lean_inc(v_snd_1861_);
lean_inc(v_fst_1860_);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_a_1834_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; lean_object* v_unused_2215_; 
v_unused_2214_ = lean_ctor_get(v_a_1834_, 1);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_a_1834_, 0);
lean_dec(v_unused_2215_);
v___x_1865_ = v_a_1834_;
v_isShared_1866_ = v_isSharedCheck_2213_;
goto v_resetjp_1864_;
}
else
{
lean_dec(v_a_1834_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_2213_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = lean_string_utf8_next_fast(v_fst_1860_, v_snd_1861_);
lean_dec(v_snd_1861_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 1, v___x_1867_);
v___x_1869_ = v___x_1865_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_fst_1860_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_2212_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; 
v___x_1870_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1869_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_pos_1871_; lean_object* v_res_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_2202_; 
v_pos_1871_ = lean_ctor_get(v___x_1870_, 0);
v_res_1872_ = lean_ctor_get(v___x_1870_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_1874_ = v___x_1870_;
v_isShared_1875_ = v_isSharedCheck_2202_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_res_1872_);
lean_inc(v_pos_1871_);
lean_dec(v___x_1870_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_2202_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_fst_1876_; lean_object* v_snd_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v_fst_1876_ = lean_ctor_get(v_pos_1871_, 0);
v_snd_1877_ = lean_ctor_get(v_pos_1871_, 1);
v___x_1878_ = lean_string_utf8_byte_size(v_fst_1876_);
v___x_1879_ = lean_nat_dec_eq(v_snd_1877_, v___x_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_2195_; 
lean_inc(v_snd_1877_);
lean_inc(v_fst_1876_);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_pos_1871_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; lean_object* v_unused_2197_; 
v_unused_2196_ = lean_ctor_get(v_pos_1871_, 1);
lean_dec(v_unused_2196_);
v_unused_2197_ = lean_ctor_get(v_pos_1871_, 0);
lean_dec(v_unused_2197_);
v___x_1881_ = v_pos_1871_;
v_isShared_1882_ = v_isSharedCheck_2195_;
goto v_resetjp_1880_;
}
else
{
lean_dec(v_pos_1871_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_2195_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = lean_string_utf8_next_fast(v_fst_1876_, v_snd_1877_);
lean_dec(v_snd_1877_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 1, v___x_1883_);
v___x_1885_ = v___x_1881_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_fst_1876_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_2194_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v_id_1887_; uint8_t v_code_1888_; lean_object* v_message_1889_; lean_object* v_data_x3f_1890_; lean_object* v_a_1899_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v___x_1904_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
v___x_1905_ = lean_string_dec_eq(v_res_1872_, v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
v___x_1907_ = lean_string_dec_eq(v_res_1872_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1908_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1909_ = lean_string_dec_eq(v_res_1872_, v___x_1908_);
lean_dec(v_res_1872_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_del_object(v___x_1874_);
lean_dec_ref(v_input_1833_);
v___x_1910_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3));
v___x_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1885_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
return v___x_1911_;
}
else
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_Json_parse(v_input_1833_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1921_; 
lean_del_object(v___x_1874_);
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1921_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1921_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set_tag(v___x_1915_, 1);
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1885_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
return v___x_1919_;
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1923_; 
v_a_1922_ = lean_ctor_get(v___x_1912_, 0);
lean_inc_n(v_a_1922_, 2);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1923_ = l_Lean_Json_getObjVal_x3f(v_a_1922_, v___x_1906_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; 
lean_dec(v_a_1922_);
lean_del_object(v___x_1874_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v_a_1899_ = v_a_1924_;
goto v___jp_1898_;
}
else
{
lean_object* v_a_1925_; 
v_a_1925_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1923_, 1);
if (lean_obj_tag(v_a_1925_) == 3)
{
lean_object* v_s_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v_s_1926_ = lean_ctor_get(v_a_1925_, 0);
lean_inc_ref(v_s_1926_);
lean_dec_ref_known(v_a_1925_, 1);
v___x_1927_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1928_ = lean_string_dec_eq(v_s_1926_, v___x_1927_);
lean_dec_ref(v_s_1926_);
if (v___x_1928_ == 0)
{
lean_dec(v_a_1922_);
lean_del_object(v___x_1874_);
goto v___jp_1902_;
}
else
{
lean_object* v___x_1929_; 
lean_inc(v_a_1922_);
v___x_1929_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_1922_, v___x_1904_);
if (lean_obj_tag(v___x_1929_) == 0)
{
goto v___jp_1957_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1922_);
v___x_1963_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1922_, v___x_1962_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_dec_ref_known(v___x_1963_, 1);
goto v___jp_1957_;
}
else
{
lean_dec_ref_known(v___x_1963_, 1);
lean_dec_ref_known(v___x_1929_, 1);
lean_dec(v_a_1922_);
lean_del_object(v___x_1874_);
goto v___jp_1895_;
}
}
v___jp_1930_:
{
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1931_; 
lean_dec(v_a_1922_);
lean_del_object(v___x_1874_);
v_a_1931_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1929_, 1);
v_a_1899_ = v_a_1931_;
goto v___jp_1898_;
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1933_; 
v_a_1932_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1933_ = l_Lean_Json_getObjVal_x3f(v_a_1922_, v___x_1908_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; 
lean_dec(v_a_1932_);
lean_del_object(v___x_1874_);
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v_a_1899_ = v_a_1934_;
goto v___jp_1898_;
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_a_1935_ = lean_ctor_get(v___x_1933_, 0);
lean_inc_n(v_a_1935_, 2);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1936_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1937_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_1935_, v___x_1936_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; 
lean_dec(v_a_1935_);
lean_dec(v_a_1932_);
lean_del_object(v___x_1874_);
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v_a_1899_ = v_a_1938_;
goto v___jp_1898_;
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_a_1939_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1940_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1935_);
v___x_1941_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1935_, v___x_1940_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; 
lean_dec(v_a_1939_);
lean_dec(v_a_1935_);
lean_dec(v_a_1932_);
lean_del_object(v___x_1874_);
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v_a_1899_ = v_a_1942_;
goto v___jp_1898_;
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_a_1943_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1941_, 1);
v___x_1944_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1945_ = l_Lean_Json_getObjVal_x3f(v_a_1935_, v___x_1944_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v___x_1946_; uint8_t v___x_1947_; 
lean_dec_ref_known(v___x_1945_, 1);
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_unbox(v_a_1939_);
lean_dec(v_a_1939_);
v_id_1887_ = v_a_1932_;
v_code_1888_ = v___x_1947_;
v_message_1889_ = v_a_1943_;
v_data_x3f_1890_ = v___x_1946_;
goto v___jp_1886_;
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
v_a_1948_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1950_ = v___x_1945_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1945_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_unbox(v_a_1939_);
lean_dec(v_a_1939_);
v_id_1887_ = v_a_1932_;
v_code_1888_ = v___x_1954_;
v_message_1889_ = v_a_1943_;
v_data_x3f_1890_ = v___x_1953_;
goto v___jp_1886_;
}
}
}
}
}
}
}
}
v___jp_1957_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1922_);
v___x_1959_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1922_, v___x_1958_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_dec_ref_known(v___x_1959_, 1);
if (lean_obj_tag(v___x_1929_) == 0)
{
goto v___jp_1930_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_1922_);
v___x_1961_ = l_Lean_Json_getObjVal_x3f(v_a_1922_, v___x_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_dec_ref_known(v___x_1961_, 1);
goto v___jp_1930_;
}
else
{
lean_dec_ref_known(v___x_1961_, 1);
lean_dec_ref_known(v___x_1929_, 1);
lean_dec(v_a_1922_);
lean_del_object(v___x_1874_);
goto v___jp_1895_;
}
}
}
else
{
lean_dec_ref_known(v___x_1959_, 1);
lean_dec_ref(v___x_1929_);
lean_dec(v_a_1922_);
lean_del_object(v___x_1874_);
goto v___jp_1895_;
}
}
}
}
else
{
lean_dec(v_a_1925_);
lean_dec(v_a_1922_);
lean_del_object(v___x_1874_);
goto v___jp_1902_;
}
}
}
}
}
else
{
lean_object* v___x_1964_; 
lean_del_object(v___x_1874_);
lean_dec(v_res_1872_);
lean_dec_ref(v_input_1833_);
v___x_1964_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1885_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_pos_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2013_; 
v_pos_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; 
v_unused_2014_ = lean_ctor_get(v___x_1964_, 1);
lean_dec(v_unused_2014_);
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_2013_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_pos_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2013_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_fst_1969_; lean_object* v_snd_1970_; uint8_t v___y_1972_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_fst_1969_ = lean_ctor_get(v_pos_1965_, 0);
v_snd_1970_ = lean_ctor_get(v_pos_1965_, 1);
v___x_2011_ = lean_string_utf8_byte_size(v_fst_1969_);
v___x_2012_ = lean_nat_dec_eq(v_snd_1970_, v___x_2011_);
if (v___x_2012_ == 0)
{
v___y_1972_ = v___x_1907_;
goto v___jp_1971_;
}
else
{
v___y_1972_ = v___x_1905_;
goto v___jp_1971_;
}
v___jp_1971_:
{
if (v___y_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1973_ = lean_box(0);
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 1);
lean_ctor_set(v___x_1967_, 1, v___x_1973_);
v___x_1975_ = v___x_1967_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_pos_1965_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1973_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
else
{
lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2008_; 
lean_inc(v_snd_1970_);
lean_inc(v_fst_1969_);
lean_del_object(v___x_1967_);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_pos_1965_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; lean_object* v_unused_2010_; 
v_unused_2009_ = lean_ctor_get(v_pos_1965_, 1);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_pos_1965_, 0);
lean_dec(v_unused_2010_);
v___x_1978_ = v_pos_1965_;
v_isShared_1979_ = v_isSharedCheck_2008_;
goto v_resetjp_1977_;
}
else
{
lean_dec(v_pos_1965_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2008_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1980_ = lean_string_utf8_next_fast(v_fst_1969_, v_snd_1970_);
lean_dec(v_snd_1970_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 1, v___x_1980_);
v___x_1982_ = v___x_1978_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_fst_1969_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_2007_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; 
v___x_1983_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_pos_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1996_; 
v_pos_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v___x_1983_, 1);
lean_dec(v_unused_1997_);
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1996_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_pos_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1996_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v_fst_1988_; lean_object* v_snd_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_fst_1988_ = lean_ctor_get(v_pos_1984_, 0);
v_snd_1989_ = lean_ctor_get(v_pos_1984_, 1);
v___x_1990_ = lean_string_utf8_byte_size(v_fst_1988_);
v___x_1991_ = lean_nat_dec_eq(v_snd_1989_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_inc(v_snd_1989_);
lean_inc(v_fst_1988_);
lean_del_object(v___x_1986_);
lean_dec(v_pos_1984_);
v___y_1836_ = v_fst_1988_;
v___y_1837_ = v_snd_1989_;
goto v___jp_1835_;
}
else
{
if (v___x_1905_ == 0)
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_box(0);
if (v_isShared_1987_ == 0)
{
lean_ctor_set_tag(v___x_1986_, 1);
lean_ctor_set(v___x_1986_, 1, v___x_1992_);
v___x_1994_ = v___x_1986_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_pos_1984_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
else
{
lean_inc(v_snd_1989_);
lean_inc(v_fst_1988_);
lean_del_object(v___x_1986_);
lean_dec(v_pos_1984_);
v___y_1836_ = v_fst_1988_;
v___y_1837_ = v_snd_1989_;
goto v___jp_1835_;
}
}
}
}
else
{
lean_object* v_pos_1998_; lean_object* v_err_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
v_pos_1998_ = lean_ctor_get(v___x_1983_, 0);
v_err_1999_ = lean_ctor_get(v___x_1983_, 1);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1983_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_err_1999_);
lean_inc(v_pos_1998_);
lean_dec(v___x_1983_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_pos_1998_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_err_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
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
lean_object* v_pos_2015_; lean_object* v_err_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v_pos_2015_ = lean_ctor_get(v___x_1964_, 0);
v_err_2016_ = lean_ctor_get(v___x_1964_, 1);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1964_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_err_2016_);
lean_inc(v_pos_2015_);
lean_dec(v___x_1964_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_pos_2015_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_err_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
else
{
lean_object* v___x_2024_; 
lean_del_object(v___x_1874_);
lean_dec(v_res_1872_);
lean_dec_ref(v_input_1833_);
v___x_2024_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(v___x_1885_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_pos_2025_; lean_object* v_res_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2184_; 
v_pos_2025_ = lean_ctor_get(v___x_2024_, 0);
v_res_2026_ = lean_ctor_get(v___x_2024_, 1);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2028_ = v___x_2024_;
v_isShared_2029_ = v_isSharedCheck_2184_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_res_2026_);
lean_inc(v_pos_2025_);
lean_dec(v___x_2024_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2184_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v_fst_2035_; lean_object* v_snd_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v_fst_2035_ = lean_ctor_get(v_pos_2025_, 0);
v_snd_2036_ = lean_ctor_get(v_pos_2025_, 1);
v___x_2037_ = lean_string_utf8_byte_size(v_fst_2035_);
v___x_2038_ = lean_nat_dec_eq(v_snd_2036_, v___x_2037_);
if (v___x_2038_ == 0)
{
if (v___x_1905_ == 0)
{
lean_dec(v_res_2026_);
goto v___jp_2030_;
}
else
{
lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2181_; 
lean_inc(v_snd_2036_);
lean_inc(v_fst_2035_);
lean_del_object(v___x_2028_);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_pos_2025_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; lean_object* v_unused_2183_; 
v_unused_2182_ = lean_ctor_get(v_pos_2025_, 1);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_pos_2025_, 0);
lean_dec(v_unused_2183_);
v___x_2040_ = v_pos_2025_;
v_isShared_2041_ = v_isSharedCheck_2181_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v_pos_2025_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2181_;
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
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_fst_2035_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; 
v___x_2045_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2044_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_pos_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2169_; 
v_pos_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v___x_2045_, 1);
lean_dec(v_unused_2170_);
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2169_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_pos_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2169_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v_fst_2050_; lean_object* v_snd_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_fst_2050_ = lean_ctor_get(v_pos_2046_, 0);
v_snd_2051_ = lean_ctor_get(v_pos_2046_, 1);
v___x_2052_ = lean_string_utf8_byte_size(v_fst_2050_);
v___x_2053_ = lean_nat_dec_eq(v_snd_2051_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2162_; 
lean_inc(v_snd_2051_);
lean_inc(v_fst_2050_);
lean_del_object(v___x_2048_);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_pos_2046_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; lean_object* v_unused_2164_; 
v_unused_2163_ = lean_ctor_get(v_pos_2046_, 1);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_pos_2046_, 0);
lean_dec(v_unused_2164_);
v___x_2055_ = v_pos_2046_;
v_isShared_2056_ = v_isSharedCheck_2162_;
goto v_resetjp_2054_;
}
else
{
lean_dec(v_pos_2046_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2162_;
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
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_fst_2050_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2060_; 
v___x_2060_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2059_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_pos_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2150_; 
v_pos_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; 
v_unused_2151_ = lean_ctor_get(v___x_2060_, 1);
lean_dec(v_unused_2151_);
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2150_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_pos_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2150_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v_fst_2065_; lean_object* v_snd_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v_fst_2065_ = lean_ctor_get(v_pos_2061_, 0);
v_snd_2066_ = lean_ctor_get(v_pos_2061_, 1);
v___x_2067_ = lean_string_utf8_byte_size(v_fst_2065_);
v___x_2068_ = lean_nat_dec_eq(v_snd_2066_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2143_; 
lean_inc(v_snd_2066_);
lean_inc(v_fst_2065_);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_pos_2061_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; lean_object* v_unused_2145_; 
v_unused_2144_ = lean_ctor_get(v_pos_2061_, 1);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_pos_2061_, 0);
lean_dec(v_unused_2145_);
v___x_2070_ = v_pos_2061_;
v_isShared_2071_ = v_isSharedCheck_2143_;
goto v_resetjp_2069_;
}
else
{
lean_dec(v_pos_2061_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2143_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = lean_string_utf8_next_fast(v_fst_2065_, v_snd_2066_);
lean_dec(v_snd_2066_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2072_);
v___x_2074_ = v___x_2070_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_fst_2065_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2075_; 
v___x_2075_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2074_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_pos_2076_; lean_object* v_res_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2132_; 
v_pos_2076_ = lean_ctor_get(v___x_2075_, 0);
v_res_2077_ = lean_ctor_get(v___x_2075_, 1);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2079_ = v___x_2075_;
v_isShared_2080_ = v_isSharedCheck_2132_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_res_2077_);
lean_inc(v_pos_2076_);
lean_dec(v___x_2075_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2132_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2087_ = lean_string_dec_eq(v_res_2077_, v___x_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
lean_del_object(v___x_2079_);
v___x_2088_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2089_ = lean_string_dec_eq(v_res_2077_, v___x_2088_);
lean_dec(v_res_2077_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
lean_dec(v_res_2026_);
v___x_2090_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5));
if (v_isShared_2064_ == 0)
{
lean_ctor_set_tag(v___x_2063_, 1);
lean_ctor_set(v___x_2063_, 1, v___x_2090_);
lean_ctor_set(v___x_2063_, 0, v_pos_2076_);
v___x_2092_ = v___x_2063_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_pos_2076_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2094_, 0, v_res_2026_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v___x_2094_);
lean_ctor_set(v___x_2063_, 0, v_pos_2076_);
v___x_2096_ = v___x_2063_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_pos_2076_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
else
{
lean_object* v_fst_2098_; lean_object* v_snd_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
lean_dec(v_res_2077_);
lean_del_object(v___x_2063_);
v_fst_2098_ = lean_ctor_get(v_pos_2076_, 0);
v_snd_2099_ = lean_ctor_get(v_pos_2076_, 1);
v___x_2100_ = lean_string_utf8_byte_size(v_fst_2098_);
v___x_2101_ = lean_nat_dec_eq(v_snd_2099_, v___x_2100_);
if (v___x_2101_ == 0)
{
if (v___x_2087_ == 0)
{
lean_dec(v_res_2026_);
goto v___jp_2081_;
}
else
{
lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2129_; 
lean_inc(v_snd_2099_);
lean_inc(v_fst_2098_);
lean_del_object(v___x_2079_);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_pos_2076_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; lean_object* v_unused_2131_; 
v_unused_2130_ = lean_ctor_get(v_pos_2076_, 1);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_pos_2076_, 0);
lean_dec(v_unused_2131_);
v___x_2103_ = v_pos_2076_;
v_isShared_2104_ = v_isSharedCheck_2129_;
goto v_resetjp_2102_;
}
else
{
lean_dec(v_pos_2076_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2129_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = lean_string_utf8_next_fast(v_fst_2098_, v_snd_2099_);
lean_dec(v_snd_2099_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 1, v___x_2105_);
v___x_2107_ = v___x_2103_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_fst_2098_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; 
v___x_2108_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2107_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_pos_2109_; lean_object* v_res_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2118_; 
v_pos_2109_ = lean_ctor_get(v___x_2108_, 0);
v_res_2110_ = lean_ctor_get(v___x_2108_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2112_ = v___x_2108_;
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_res_2110_);
lean_inc(v_pos_2109_);
lean_dec(v___x_2108_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v_res_2026_);
lean_ctor_set(v___x_2114_, 1, v_res_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 1, v___x_2114_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_pos_2109_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
else
{
lean_object* v_pos_2119_; lean_object* v_err_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_res_2026_);
v_pos_2119_ = lean_ctor_get(v___x_2108_, 0);
v_err_2120_ = lean_ctor_get(v___x_2108_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2108_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_err_2120_);
lean_inc(v_pos_2119_);
lean_dec(v___x_2108_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_pos_2119_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_err_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2026_);
goto v___jp_2081_;
}
}
v___jp_2081_:
{
lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2082_ = lean_box(0);
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 1);
lean_ctor_set(v___x_2079_, 1, v___x_2082_);
v___x_2084_ = v___x_2079_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_pos_2076_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
lean_object* v_pos_2133_; lean_object* v_err_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_del_object(v___x_2063_);
lean_dec(v_res_2026_);
v_pos_2133_ = lean_ctor_get(v___x_2075_, 0);
v_err_2134_ = lean_ctor_get(v___x_2075_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2075_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_err_2134_);
lean_inc(v_pos_2133_);
lean_dec(v___x_2075_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_pos_2133_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_err_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_dec(v_res_2026_);
v___x_2146_ = lean_box(0);
if (v_isShared_2064_ == 0)
{
lean_ctor_set_tag(v___x_2063_, 1);
lean_ctor_set(v___x_2063_, 1, v___x_2146_);
v___x_2148_ = v___x_2063_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_pos_2061_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_pos_2152_; lean_object* v_err_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec(v_res_2026_);
v_pos_2152_ = lean_ctor_get(v___x_2060_, 0);
v_err_2153_ = lean_ctor_get(v___x_2060_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2060_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_err_2153_);
lean_inc(v_pos_2152_);
lean_dec(v___x_2060_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_pos_2152_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_err_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_dec(v_res_2026_);
v___x_2165_ = lean_box(0);
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 1);
lean_ctor_set(v___x_2048_, 1, v___x_2165_);
v___x_2167_ = v___x_2048_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_pos_2046_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_object* v_pos_2171_; lean_object* v_err_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_res_2026_);
v_pos_2171_ = lean_ctor_get(v___x_2045_, 0);
v_err_2172_ = lean_ctor_get(v___x_2045_, 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2045_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_err_2172_);
lean_inc(v_pos_2171_);
lean_dec(v___x_2045_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_pos_2171_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_err_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
}
}
else
{
lean_dec(v_res_2026_);
goto v___jp_2030_;
}
v___jp_2030_:
{
lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2031_ = lean_box(0);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 1);
lean_ctor_set(v___x_2028_, 1, v___x_2031_);
v___x_2033_ = v___x_2028_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_pos_2025_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v_pos_2185_; lean_object* v_err_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
v_pos_2185_ = lean_ctor_get(v___x_2024_, 0);
v_err_2186_ = lean_ctor_get(v___x_2024_, 1);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2024_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_err_2186_);
lean_inc(v_pos_2185_);
lean_dec(v___x_2024_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_pos_2185_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_err_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
v___jp_1886_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1891_, 0, v_id_1887_);
lean_ctor_set(v___x_1891_, 1, v_message_1889_);
lean_ctor_set(v___x_1891_, 2, v_data_x3f_1890_);
lean_ctor_set_uint8(v___x_1891_, sizeof(void*)*3, v_code_1888_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 1, v___x_1891_);
lean_ctor_set(v___x_1874_, 0, v___x_1885_);
v___x_1893_ = v___x_1874_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
v___jp_1895_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1));
v___x_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1885_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
return v___x_1897_;
}
v___jp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1900_, 0, v_a_1899_);
v___x_1901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1885_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
return v___x_1901_;
}
v___jp_1902_:
{
lean_object* v___x_1903_; 
v___x_1903_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_1899_ = v___x_1903_;
goto v___jp_1898_;
}
}
}
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
lean_dec(v_res_1872_);
lean_dec_ref(v_input_1833_);
v___x_2198_ = lean_box(0);
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 1);
lean_ctor_set(v___x_1874_, 1, v___x_2198_);
v___x_2200_ = v___x_1874_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_pos_1871_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
else
{
lean_object* v_pos_2203_; lean_object* v_err_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec_ref(v_input_1833_);
v_pos_2203_ = lean_ctor_get(v___x_1870_, 0);
v_err_2204_ = lean_ctor_get(v___x_1870_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_1870_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_err_2204_);
lean_inc(v_pos_2203_);
lean_dec(v___x_1870_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_pos_2203_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_err_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec_ref(v_input_1833_);
v___x_2216_ = lean_box(0);
v___x_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2217_, 0, v_a_1834_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
return v___x_2217_;
}
v___jp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = lean_string_utf8_next_fast(v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___y_1836_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1839_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_pos_1841_; lean_object* v_res_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1850_; 
v_pos_1841_ = lean_ctor_get(v___x_1840_, 0);
v_res_1842_ = lean_ctor_get(v___x_1840_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1844_ = v___x_1840_;
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_res_1842_);
lean_inc(v_pos_1841_);
lean_dec(v___x_1840_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1850_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_res_1842_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 1, v___x_1846_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_pos_1841_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_object* v_pos_1851_; lean_object* v_err_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_pos_1851_ = lean_ctor_get(v___x_1840_, 0);
v_err_1852_ = lean_ctor_get(v___x_1840_, 1);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1840_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_err_1852_);
lean_inc(v_pos_1851_);
lean_dec(v___x_1840_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_pos_1851_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_err_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object* v_input_2218_){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_inc_ref(v_input_2218_);
v___x_2219_ = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser), 2, 1);
lean_closure_set(v___x_2219_, 0, v_input_2218_);
v___x_2220_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2219_, v_input_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx(uint8_t v_x_2221_){
_start:
{
if (v_x_2221_ == 0)
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_unsigned_to_nat(0u);
return v___x_2222_;
}
else
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_unsigned_to_nat(1u);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___boxed(lean_object* v_x_2224_){
_start:
{
uint8_t v_x_boxed_2225_; lean_object* v_res_2226_; 
v_x_boxed_2225_ = lean_unbox(v_x_2224_);
v_res_2226_ = l_Lean_JsonRpc_MessageDirection_ctorIdx(v_x_boxed_2225_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx(uint8_t v_x_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_JsonRpc_MessageDirection_ctorIdx(v_x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_toCtorIdx___boxed(lean_object* v_x_2229_){
_start:
{
uint8_t v_x_4__boxed_2230_; lean_object* v_res_2231_; 
v_x_4__boxed_2230_ = lean_unbox(v_x_2229_);
v_res_2231_ = l_Lean_JsonRpc_MessageDirection_toCtorIdx(v_x_4__boxed_2230_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object* v_k_2232_){
_start:
{
lean_inc(v_k_2232_);
return v_k_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object* v_k_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(v_k_2233_);
lean_dec(v_k_2233_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object* v_motive_2235_, lean_object* v_ctorIdx_2236_, uint8_t v_t_2237_, lean_object* v_h_2238_, lean_object* v_k_2239_){
_start:
{
lean_inc(v_k_2239_);
return v_k_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object* v_motive_2240_, lean_object* v_ctorIdx_2241_, lean_object* v_t_2242_, lean_object* v_h_2243_, lean_object* v_k_2244_){
_start:
{
uint8_t v_t_boxed_2245_; lean_object* v_res_2246_; 
v_t_boxed_2245_ = lean_unbox(v_t_2242_);
v_res_2246_ = l_Lean_JsonRpc_MessageDirection_ctorElim(v_motive_2240_, v_ctorIdx_2241_, v_t_boxed_2245_, v_h_2243_, v_k_2244_);
lean_dec(v_k_2244_);
lean_dec(v_ctorIdx_2241_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object* v_clientToServer_2247_){
_start:
{
lean_inc(v_clientToServer_2247_);
return v_clientToServer_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object* v_clientToServer_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(v_clientToServer_2248_);
lean_dec(v_clientToServer_2248_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object* v_motive_2250_, uint8_t v_t_2251_, lean_object* v_h_2252_, lean_object* v_clientToServer_2253_){
_start:
{
lean_inc(v_clientToServer_2253_);
return v_clientToServer_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object* v_motive_2254_, lean_object* v_t_2255_, lean_object* v_h_2256_, lean_object* v_clientToServer_2257_){
_start:
{
uint8_t v_t_boxed_2258_; lean_object* v_res_2259_; 
v_t_boxed_2258_ = lean_unbox(v_t_2255_);
v_res_2259_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(v_motive_2254_, v_t_boxed_2258_, v_h_2256_, v_clientToServer_2257_);
lean_dec(v_clientToServer_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object* v_serverToClient_2260_){
_start:
{
lean_inc(v_serverToClient_2260_);
return v_serverToClient_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object* v_serverToClient_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(v_serverToClient_2261_);
lean_dec(v_serverToClient_2261_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object* v_motive_2263_, uint8_t v_t_2264_, lean_object* v_h_2265_, lean_object* v_serverToClient_2266_){
_start:
{
lean_inc(v_serverToClient_2266_);
return v_serverToClient_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object* v_motive_2267_, lean_object* v_t_2268_, lean_object* v_h_2269_, lean_object* v_serverToClient_2270_){
_start:
{
uint8_t v_t_boxed_2271_; lean_object* v_res_2272_; 
v_t_boxed_2271_ = lean_unbox(v_t_2268_);
v_res_2272_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(v_motive_2267_, v_t_boxed_2271_, v_h_2269_, v_serverToClient_2270_);
lean_dec(v_serverToClient_2270_);
return v_res_2272_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default(void){
_start:
{
uint8_t v___x_2273_; 
v___x_2273_ = 0;
return v___x_2273_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection(void){
_start:
{
uint8_t v___x_2274_; 
v___x_2274_ = 0;
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object* v_json_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_Json_getTag_x3f(v_json_2289_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v___x_2291_; 
v___x_2291_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1));
return v___x_2291_;
}
else
{
lean_object* v_val_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v_val_2292_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_val_2292_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2293_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2));
v___x_2294_ = lean_string_dec_eq(v_val_2292_, v___x_2293_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2295_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3));
v___x_2296_ = lean_string_dec_eq(v_val_2292_, v___x_2295_);
lean_dec(v_val_2292_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; 
v___x_2297_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5));
return v___x_2297_;
}
else
{
lean_object* v___x_2298_; 
v___x_2298_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6));
return v___x_2298_;
}
}
else
{
lean_object* v___x_2299_; 
lean_dec(v_val_2292_);
v___x_2299_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7));
return v___x_2299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t v_x_2306_){
_start:
{
if (v_x_2306_ == 0)
{
lean_object* v___x_2307_; 
v___x_2307_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0));
return v___x_2307_;
}
else
{
lean_object* v___x_2308_; 
v___x_2308_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1));
return v___x_2308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object* v_x_2309_){
_start:
{
uint8_t v_x_44__boxed_2310_; lean_object* v_res_2311_; 
v_x_44__boxed_2310_ = lean_unbox(v_x_2309_);
v_res_2311_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_x_44__boxed_2310_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx(uint8_t v_x_2314_){
_start:
{
switch(v_x_2314_)
{
case 0:
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_unsigned_to_nat(0u);
return v___x_2315_;
}
case 1:
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_unsigned_to_nat(1u);
return v___x_2316_;
}
case 2:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_unsigned_to_nat(2u);
return v___x_2317_;
}
default: 
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_unsigned_to_nat(3u);
return v___x_2318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___boxed(lean_object* v_x_2319_){
_start:
{
uint8_t v_x_boxed_2320_; lean_object* v_res_2321_; 
v_x_boxed_2320_ = lean_unbox(v_x_2319_);
v_res_2321_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_boxed_2320_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx(uint8_t v_x_2322_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_JsonRpc_MessageKind_ctorIdx(v_x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_toCtorIdx___boxed(lean_object* v_x_2324_){
_start:
{
uint8_t v_x_4__boxed_2325_; lean_object* v_res_2326_; 
v_x_4__boxed_2325_ = lean_unbox(v_x_2324_);
v_res_2326_ = l_Lean_JsonRpc_MessageKind_toCtorIdx(v_x_4__boxed_2325_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object* v_k_2327_){
_start:
{
lean_inc(v_k_2327_);
return v_k_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object* v_k_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_JsonRpc_MessageKind_ctorElim___redArg(v_k_2328_);
lean_dec(v_k_2328_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object* v_motive_2330_, lean_object* v_ctorIdx_2331_, uint8_t v_t_2332_, lean_object* v_h_2333_, lean_object* v_k_2334_){
_start:
{
lean_inc(v_k_2334_);
return v_k_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object* v_motive_2335_, lean_object* v_ctorIdx_2336_, lean_object* v_t_2337_, lean_object* v_h_2338_, lean_object* v_k_2339_){
_start:
{
uint8_t v_t_boxed_2340_; lean_object* v_res_2341_; 
v_t_boxed_2340_ = lean_unbox(v_t_2337_);
v_res_2341_ = l_Lean_JsonRpc_MessageKind_ctorElim(v_motive_2335_, v_ctorIdx_2336_, v_t_boxed_2340_, v_h_2338_, v_k_2339_);
lean_dec(v_k_2339_);
lean_dec(v_ctorIdx_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object* v_request_2342_){
_start:
{
lean_inc(v_request_2342_);
return v_request_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object* v_request_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_JsonRpc_MessageKind_request_elim___redArg(v_request_2343_);
lean_dec(v_request_2343_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object* v_motive_2345_, uint8_t v_t_2346_, lean_object* v_h_2347_, lean_object* v_request_2348_){
_start:
{
lean_inc(v_request_2348_);
return v_request_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object* v_motive_2349_, lean_object* v_t_2350_, lean_object* v_h_2351_, lean_object* v_request_2352_){
_start:
{
uint8_t v_t_boxed_2353_; lean_object* v_res_2354_; 
v_t_boxed_2353_ = lean_unbox(v_t_2350_);
v_res_2354_ = l_Lean_JsonRpc_MessageKind_request_elim(v_motive_2349_, v_t_boxed_2353_, v_h_2351_, v_request_2352_);
lean_dec(v_request_2352_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object* v_notification_2355_){
_start:
{
lean_inc(v_notification_2355_);
return v_notification_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object* v_notification_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_JsonRpc_MessageKind_notification_elim___redArg(v_notification_2356_);
lean_dec(v_notification_2356_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object* v_motive_2358_, uint8_t v_t_2359_, lean_object* v_h_2360_, lean_object* v_notification_2361_){
_start:
{
lean_inc(v_notification_2361_);
return v_notification_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object* v_motive_2362_, lean_object* v_t_2363_, lean_object* v_h_2364_, lean_object* v_notification_2365_){
_start:
{
uint8_t v_t_boxed_2366_; lean_object* v_res_2367_; 
v_t_boxed_2366_ = lean_unbox(v_t_2363_);
v_res_2367_ = l_Lean_JsonRpc_MessageKind_notification_elim(v_motive_2362_, v_t_boxed_2366_, v_h_2364_, v_notification_2365_);
lean_dec(v_notification_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object* v_response_2368_){
_start:
{
lean_inc(v_response_2368_);
return v_response_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object* v_response_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_JsonRpc_MessageKind_response_elim___redArg(v_response_2369_);
lean_dec(v_response_2369_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object* v_motive_2371_, uint8_t v_t_2372_, lean_object* v_h_2373_, lean_object* v_response_2374_){
_start:
{
lean_inc(v_response_2374_);
return v_response_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object* v_motive_2375_, lean_object* v_t_2376_, lean_object* v_h_2377_, lean_object* v_response_2378_){
_start:
{
uint8_t v_t_boxed_2379_; lean_object* v_res_2380_; 
v_t_boxed_2379_ = lean_unbox(v_t_2376_);
v_res_2380_ = l_Lean_JsonRpc_MessageKind_response_elim(v_motive_2375_, v_t_boxed_2379_, v_h_2377_, v_response_2378_);
lean_dec(v_response_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object* v_responseError_2381_){
_start:
{
lean_inc(v_responseError_2381_);
return v_responseError_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object* v_responseError_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(v_responseError_2382_);
lean_dec(v_responseError_2382_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object* v_motive_2384_, uint8_t v_t_2385_, lean_object* v_h_2386_, lean_object* v_responseError_2387_){
_start:
{
lean_inc(v_responseError_2387_);
return v_responseError_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object* v_motive_2388_, lean_object* v_t_2389_, lean_object* v_h_2390_, lean_object* v_responseError_2391_){
_start:
{
uint8_t v_t_boxed_2392_; lean_object* v_res_2393_; 
v_t_boxed_2392_ = lean_unbox(v_t_2389_);
v_res_2393_ = l_Lean_JsonRpc_MessageKind_responseError_elim(v_motive_2388_, v_t_boxed_2392_, v_h_2390_, v_responseError_2391_);
lean_dec(v_responseError_2391_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object* v_json_2414_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_Json_getTag_x3f(v_json_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v___x_2416_; 
v___x_2416_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0));
return v___x_2416_;
}
else
{
lean_object* v_val_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v_val_2417_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_val_2417_);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2418_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1));
v___x_2419_ = lean_string_dec_eq(v_val_2417_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2));
v___x_2421_ = lean_string_dec_eq(v_val_2417_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3));
v___x_2423_ = lean_string_dec_eq(v_val_2417_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; uint8_t v___x_2425_; 
v___x_2424_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4));
v___x_2425_ = lean_string_dec_eq(v_val_2417_, v___x_2424_);
lean_dec(v_val_2417_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; 
v___x_2426_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5));
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; 
v___x_2427_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6));
return v___x_2427_;
}
}
else
{
lean_object* v___x_2428_; 
lean_dec(v_val_2417_);
v___x_2428_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7));
return v___x_2428_;
}
}
else
{
lean_object* v___x_2429_; 
lean_dec(v_val_2417_);
v___x_2429_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8));
return v___x_2429_;
}
}
else
{
lean_object* v___x_2430_; 
lean_dec(v_val_2417_);
v___x_2430_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9));
return v___x_2430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t v_x_2441_){
_start:
{
switch(v_x_2441_)
{
case 0:
{
lean_object* v___x_2442_; 
v___x_2442_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0));
return v___x_2442_;
}
case 1:
{
lean_object* v___x_2443_; 
v___x_2443_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1));
return v___x_2443_;
}
case 2:
{
lean_object* v___x_2444_; 
v___x_2444_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2));
return v___x_2444_;
}
default: 
{
lean_object* v___x_2445_; 
v___x_2445_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3));
return v___x_2445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object* v_x_2446_){
_start:
{
uint8_t v_x_84__boxed_2447_; lean_object* v_res_2448_; 
v_x_84__boxed_2447_ = lean_unbox(v_x_2446_);
v_res_2448_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_x_84__boxed_2447_);
return v_res_2448_;
}
}
LEAN_EXPORT uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object* v_x_2451_){
_start:
{
switch(lean_obj_tag(v_x_2451_))
{
case 0:
{
uint8_t v___x_2452_; 
v___x_2452_ = 0;
return v___x_2452_;
}
case 1:
{
uint8_t v___x_2453_; 
v___x_2453_ = 1;
return v___x_2453_;
}
case 2:
{
uint8_t v___x_2454_; 
v___x_2454_ = 2;
return v___x_2454_;
}
default: 
{
uint8_t v___x_2455_; 
v___x_2455_ = 3;
return v___x_2455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object* v_x_2456_){
_start:
{
uint8_t v_res_2457_; lean_object* v_r_2458_; 
v_res_2457_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_x_2456_);
lean_dec_ref(v_x_2456_);
v_r_2458_ = lean_box(v_res_2457_);
return v_r_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(lean_object* v_j_2459_, lean_object* v_k_2460_){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = l_Lean_Json_getObjValD(v_j_2459_, v_k_2460_);
v___x_2462_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0___boxed(lean_object* v_j_2463_, lean_object* v_k_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(v_j_2463_, v_k_2464_);
lean_dec_ref(v_k_2464_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage(lean_object* v_h_2468_, lean_object* v_nBytes_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_IO_FS_Stream_readJson(v_h_2468_, v_nBytes_2469_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2591_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2591_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2591_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___y_2477_; lean_object* v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v_a_2491_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_a_2472_);
v___x_2503_ = l_Lean_Json_getObjVal_x3f(v_a_2472_, v___x_2502_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; 
lean_del_object(v___x_2474_);
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
v_a_2491_ = v_a_2504_;
goto v___jp_2490_;
}
else
{
lean_object* v_a_2505_; 
v_a_2505_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2503_, 1);
if (lean_obj_tag(v_a_2505_) == 3)
{
lean_object* v_s_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v_s_2506_ = lean_ctor_get(v_a_2505_, 0);
lean_inc_ref(v_s_2506_);
lean_dec_ref_known(v_a_2505_, 1);
v___x_2507_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_2508_ = lean_string_dec_eq(v_s_2506_, v___x_2507_);
lean_dec_ref(v_s_2506_);
if (v___x_2508_ == 0)
{
lean_del_object(v___x_2474_);
goto v___jp_2500_;
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_a_2472_);
v___x_2510_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_2472_, v___x_2509_);
if (lean_obj_tag(v___x_2510_) == 0)
{
goto v___jp_2539_;
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v_a_2566_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2566_);
v___x_2567_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2472_);
v___x_2568_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2472_, v___x_2567_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_dec_ref_known(v___x_2568_, 1);
lean_dec(v_a_2566_);
goto v___jp_2539_;
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2590_; 
lean_dec_ref_known(v___x_2510_, 1);
lean_del_object(v___x_2474_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2590_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2590_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___y_2574_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2580_ = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(v_a_2472_, v___x_2579_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v___x_2581_; 
lean_dec_ref_known(v___x_2580_, 1);
v___x_2581_ = lean_box(0);
v___y_2574_ = v___x_2581_;
goto v___jp_2573_;
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_a_2582_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2580_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2580_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
v___y_2574_ = v___x_2587_;
goto v___jp_2573_;
}
}
}
v___jp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2575_, 0, v_a_2566_);
lean_ctor_set(v___x_2575_, 1, v_a_2569_);
lean_ctor_set(v___x_2575_, 2, v___y_2574_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set_tag(v___x_2571_, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2575_);
v___x_2577_ = v___x_2571_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
v___jp_2511_:
{
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2512_; 
lean_del_object(v___x_2474_);
v_a_2512_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2510_, 1);
v_a_2491_ = v_a_2512_;
goto v___jp_2490_;
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_a_2513_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2510_, 1);
v___x_2514_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
lean_inc(v_a_2472_);
v___x_2515_ = l_Lean_Json_getObjVal_x3f(v_a_2472_, v___x_2514_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; 
lean_dec(v_a_2513_);
lean_del_object(v___x_2474_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v_a_2491_ = v_a_2516_;
goto v___jp_2490_;
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_a_2517_ = lean_ctor_get(v___x_2515_, 0);
lean_inc_n(v_a_2517_, 2);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2518_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_2519_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_2517_, v___x_2518_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; 
lean_dec(v_a_2517_);
lean_dec(v_a_2513_);
lean_del_object(v___x_2474_);
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v_a_2491_ = v_a_2520_;
goto v___jp_2490_;
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v_a_2521_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2519_, 1);
v___x_2522_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_2517_);
v___x_2523_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2517_, v___x_2522_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; 
lean_dec(v_a_2521_);
lean_dec(v_a_2517_);
lean_dec(v_a_2513_);
lean_del_object(v___x_2474_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v_a_2491_ = v_a_2524_;
goto v___jp_2490_;
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec(v_a_2472_);
v_a_2525_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2526_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2527_ = l_Lean_Json_getObjVal_x3f(v_a_2517_, v___x_2526_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v___x_2528_; uint8_t v___x_2529_; 
lean_dec_ref_known(v___x_2527_, 1);
v___x_2528_ = lean_box(0);
v___x_2529_ = lean_unbox(v_a_2521_);
lean_dec(v_a_2521_);
v___y_2477_ = v_a_2513_;
v___y_2478_ = v_a_2525_;
v___y_2479_ = v___x_2529_;
v___y_2480_ = v___x_2528_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2538_; 
v_a_2530_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2532_ = v___x_2527_;
v_isShared_2533_ = v_isSharedCheck_2538_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2527_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2538_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
uint8_t v___x_2536_; 
v___x_2536_ = lean_unbox(v_a_2521_);
lean_dec(v_a_2521_);
v___y_2477_ = v_a_2513_;
v___y_2478_ = v_a_2525_;
v___y_2479_ = v___x_2536_;
v___y_2480_ = v___x_2535_;
goto v___jp_2476_;
}
}
}
}
}
}
}
}
v___jp_2539_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2472_);
v___x_2541_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2472_, v___x_2540_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_dec_ref_known(v___x_2541_, 1);
if (lean_obj_tag(v___x_2510_) == 0)
{
goto v___jp_2511_;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v_a_2542_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2542_);
v___x_2543_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_2472_);
v___x_2544_ = l_Lean_Json_getObjVal_x3f(v_a_2472_, v___x_2543_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_dec_ref_known(v___x_2544_, 1);
lean_dec(v_a_2542_);
goto v___jp_2511_;
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref_known(v___x_2510_, 1);
lean_del_object(v___x_2474_);
lean_dec(v_a_2472_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2553_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2553_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2551_; 
v___x_2549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2549_, 0, v_a_2542_);
lean_ctor_set(v___x_2549_, 1, v_a_2545_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set_tag(v___x_2547_, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2549_);
v___x_2551_ = v___x_2547_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
lean_dec_ref(v___x_2510_);
lean_del_object(v___x_2474_);
v_a_2554_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2541_, 1);
v___x_2555_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2556_ = l_Lean_Json_getObjValAs_x3f___at___00IO_FS_Stream_readMessage_spec__0(v_a_2472_, v___x_2555_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v___x_2557_; 
lean_dec_ref_known(v___x_2556_, 1);
v___x_2557_ = lean_box(0);
v___y_2486_ = v_a_2554_;
v___y_2487_ = v___x_2557_;
goto v___jp_2485_;
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
v_a_2558_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2556_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2556_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
v___y_2486_ = v_a_2554_;
v___y_2487_ = v___x_2563_;
goto v___jp_2485_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2505_);
lean_del_object(v___x_2474_);
goto v___jp_2500_;
}
}
v___jp_2476_:
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2481_, 0, v___y_2477_);
lean_ctor_set(v___x_2481_, 1, v___y_2478_);
lean_ctor_set(v___x_2481_, 2, v___y_2480_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*3, v___y_2479_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2481_);
v___x_2483_ = v___x_2474_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
v___jp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___y_2486_);
lean_ctor_set(v___x_2488_, 1, v___y_2487_);
v___x_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
return v___x_2489_;
}
v___jp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2492_ = ((lean_object*)(l_IO_FS_Stream_readMessage___closed__0));
v___x_2493_ = l_Lean_Json_compress(v_a_2472_);
v___x_2494_ = lean_string_append(v___x_2492_, v___x_2493_);
lean_dec_ref(v___x_2493_);
v___x_2495_ = ((lean_object*)(l_IO_FS_Stream_readMessage___closed__1));
v___x_2496_ = lean_string_append(v___x_2494_, v___x_2495_);
v___x_2497_ = lean_string_append(v___x_2496_, v_a_2491_);
lean_dec_ref(v_a_2491_);
v___x_2498_ = lean_mk_io_user_error(v___x_2497_);
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
return v___x_2499_;
}
v___jp_2500_:
{
lean_object* v___x_2501_; 
v___x_2501_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_2491_ = v___x_2501_;
goto v___jp_2490_;
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
v_a_2592_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2471_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2471_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object* v_h_2600_, lean_object* v_nBytes_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_IO_FS_Stream_readMessage(v_h_2600_, v_nBytes_2601_);
lean_dec(v_nBytes_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object* v_h_2611_, lean_object* v_nBytes_2612_, lean_object* v_expectedMethod_2613_, lean_object* v_inst_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_IO_FS_Stream_readMessage(v_h_2611_, v_nBytes_2612_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2804_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2619_ = v___x_2616_;
v_isShared_2620_ = v_isSharedCheck_2804_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2804_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
if (lean_obj_tag(v_a_2617_) == 0)
{
lean_object* v_id_2621_; lean_object* v_method_2622_; lean_object* v_params_x3f_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2663_; 
v_id_2621_ = lean_ctor_get(v_a_2617_, 0);
v_method_2622_ = lean_ctor_get(v_a_2617_, 1);
v_params_x3f_2623_ = lean_ctor_get(v_a_2617_, 2);
v_isSharedCheck_2663_ = !lean_is_exclusive(v_a_2617_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2625_ = v_a_2617_;
v_isShared_2626_ = v_isSharedCheck_2663_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_params_x3f_2623_);
lean_inc(v_method_2622_);
lean_inc(v_id_2621_);
lean_dec(v_a_2617_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2663_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
uint8_t v___x_2627_; 
v___x_2627_ = lean_string_dec_eq(v_method_2622_, v_expectedMethod_2613_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
lean_del_object(v___x_2625_);
lean_dec(v_params_x3f_2623_);
lean_dec(v_id_2621_);
lean_dec_ref(v_inst_2614_);
v___x_2628_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2629_ = lean_string_append(v___x_2628_, v_expectedMethod_2613_);
lean_dec_ref(v_expectedMethod_2613_);
v___x_2630_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2631_ = lean_string_append(v___x_2629_, v___x_2630_);
v___x_2632_ = lean_string_append(v___x_2631_, v_method_2622_);
lean_dec_ref(v_method_2622_);
v___x_2633_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2634_ = lean_string_append(v___x_2632_, v___x_2633_);
v___x_2635_ = lean_mk_io_user_error(v___x_2634_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set_tag(v___x_2619_, 1);
lean_ctor_set(v___x_2619_, 0, v___x_2635_);
v___x_2637_ = v___x_2619_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_dec_ref(v_method_2622_);
v___x_2639_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2640_ = l_Lean_Option_toJson___redArg(v___x_2639_, v_params_x3f_2623_);
lean_inc(v___x_2640_);
v___x_2641_ = lean_apply_1(v_inst_2614_, v___x_2640_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_del_object(v___x_2625_);
lean_dec(v_id_2621_);
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v___x_2643_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2644_ = l_Lean_Json_compress(v___x_2640_);
v___x_2645_ = lean_string_append(v___x_2643_, v___x_2644_);
lean_dec_ref(v___x_2644_);
v___x_2646_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2647_ = lean_string_append(v___x_2645_, v___x_2646_);
v___x_2648_ = lean_string_append(v___x_2647_, v_expectedMethod_2613_);
lean_dec_ref(v_expectedMethod_2613_);
v___x_2649_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2650_ = lean_string_append(v___x_2648_, v___x_2649_);
v___x_2651_ = lean_string_append(v___x_2650_, v_a_2642_);
lean_dec(v_a_2642_);
v___x_2652_ = lean_mk_io_user_error(v___x_2651_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set_tag(v___x_2619_, 1);
lean_ctor_set(v___x_2619_, 0, v___x_2652_);
v___x_2654_ = v___x_2619_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; 
lean_dec(v___x_2640_);
v_a_2656_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2641_, 1);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 2, v_a_2656_);
lean_ctor_set(v___x_2625_, 1, v_expectedMethod_2613_);
v___x_2658_ = v___x_2625_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_id_2621_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_expectedMethod_2613_);
lean_ctor_set(v_reuseFailAlloc_2662_, 2, v_a_2656_);
v___x_2658_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2660_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2658_);
v___x_2660_ = v___x_2619_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___y_2668_; 
lean_dec_ref(v_inst_2614_);
lean_dec_ref(v_expectedMethod_2613_);
v___x_2664_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__6));
v___x_2665_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2666_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2617_))
{
case 0:
{
lean_object* v_id_2679_; lean_object* v_method_2680_; lean_object* v_params_x3f_2681_; lean_object* v___x_2682_; lean_object* v___y_2684_; 
v_id_2679_ = lean_ctor_get(v_a_2617_, 0);
lean_inc(v_id_2679_);
v_method_2680_ = lean_ctor_get(v_a_2617_, 1);
lean_inc_ref(v_method_2680_);
v_params_x3f_2681_ = lean_ctor_get(v_a_2617_, 2);
lean_inc(v_params_x3f_2681_);
lean_dec_ref_known(v_a_2617_, 3);
v___x_2682_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2679_) == 0)
{
lean_object* v_s_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_s_2695_ = lean_ctor_get(v_id_2679_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_id_2679_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v_id_2679_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_s_2695_);
lean_dec(v_id_2679_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set_tag(v___x_2697_, 3);
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_s_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
v___y_2684_ = v___x_2700_;
goto v___jp_2683_;
}
}
}
else
{
lean_object* v_n_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
v_n_2703_ = lean_ctor_get(v_id_2679_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_id_2679_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v_id_2679_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_n_2703_);
lean_dec(v_id_2679_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set_tag(v___x_2705_, 2);
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_n_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
v___y_2684_ = v___x_2708_;
goto v___jp_2683_;
}
}
}
v___jp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2682_);
lean_ctor_set(v___x_2685_, 1, v___y_2684_);
v___x_2686_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2687_, 0, v_method_2680_);
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2686_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = lean_box(0);
v___x_2690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2688_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2685_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2693_ = l_Lean_Json_opt___redArg(v___x_2665_, v___x_2692_, v_params_x3f_2681_);
v___x_2694_ = l_List_appendTR___redArg(v___x_2691_, v___x_2693_);
v___y_2668_ = v___x_2694_;
goto v___jp_2667_;
}
}
case 1:
{
lean_object* v_method_2711_; lean_object* v_params_x3f_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_method_2711_ = lean_ctor_get(v_a_2617_, 0);
lean_inc_ref(v_method_2711_);
v_params_x3f_2712_ = lean_ctor_get(v_a_2617_, 1);
lean_inc(v_params_x3f_2712_);
lean_dec_ref_known(v_a_2617_, 2);
v___x_2713_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2714_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2714_, 0, v_method_2711_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2717_ = l_Lean_Json_opt___redArg(v___x_2665_, v___x_2716_, v_params_x3f_2712_);
v___x_2718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2715_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___y_2668_ = v___x_2718_;
goto v___jp_2667_;
}
case 2:
{
lean_object* v_id_2719_; lean_object* v_result_2720_; lean_object* v___x_2721_; lean_object* v___y_2723_; 
v_id_2719_ = lean_ctor_get(v_a_2617_, 0);
lean_inc(v_id_2719_);
v_result_2720_ = lean_ctor_get(v_a_2617_, 1);
lean_inc(v_result_2720_);
lean_dec_ref_known(v_a_2617_, 2);
v___x_2721_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2719_) == 0)
{
lean_object* v_s_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
v_s_2730_ = lean_ctor_get(v_id_2719_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_id_2719_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v_id_2719_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_s_2730_);
lean_dec(v_id_2719_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set_tag(v___x_2732_, 3);
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_s_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
v___y_2723_ = v___x_2735_;
goto v___jp_2722_;
}
}
}
else
{
lean_object* v_n_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
v_n_2738_ = lean_ctor_get(v_id_2719_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_id_2719_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v_id_2719_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_n_2738_);
lean_dec(v_id_2719_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set_tag(v___x_2740_, 2);
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_n_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
v___y_2723_ = v___x_2743_;
goto v___jp_2722_;
}
}
}
v___jp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2721_);
lean_ctor_set(v___x_2724_, 1, v___y_2723_);
v___x_2725_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
lean_ctor_set(v___x_2726_, 1, v_result_2720_);
v___x_2727_ = lean_box(0);
v___x_2728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2724_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___y_2668_ = v___x_2729_;
goto v___jp_2667_;
}
}
default: 
{
lean_object* v_id_2746_; uint8_t v_code_2747_; lean_object* v_message_2748_; lean_object* v_data_x3f_2749_; lean_object* v___x_2750_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___x_2770_; lean_object* v___y_2772_; 
v_id_2746_ = lean_ctor_get(v_a_2617_, 0);
lean_inc(v_id_2746_);
v_code_2747_ = lean_ctor_get_uint8(v_a_2617_, sizeof(void*)*3);
v_message_2748_ = lean_ctor_get(v_a_2617_, 1);
lean_inc_ref(v_message_2748_);
v_data_x3f_2749_ = lean_ctor_get(v_a_2617_, 2);
lean_inc(v_data_x3f_2749_);
lean_dec_ref_known(v_a_2617_, 3);
v___x_2750_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2770_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2746_) == 0)
{
lean_object* v_s_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v_s_2788_ = lean_ctor_get(v_id_2746_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_id_2746_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v_id_2746_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_s_2788_);
lean_dec(v_id_2746_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set_tag(v___x_2790_, 3);
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_s_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
v___y_2772_ = v___x_2793_;
goto v___jp_2771_;
}
}
}
else
{
lean_object* v_n_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_n_2796_ = lean_ctor_get(v_id_2746_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_id_2746_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v_id_2746_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_n_2796_);
lean_dec(v_id_2746_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
lean_ctor_set_tag(v___x_2798_, 2);
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_n_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
v___y_2772_ = v___x_2801_;
goto v___jp_2771_;
}
}
}
v___jp_2751_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_inc(v___y_2755_);
lean_inc_ref(v___y_2752_);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___y_2752_);
lean_ctor_set(v___x_2756_, 1, v___y_2755_);
v___x_2757_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_message_2748_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = lean_box(0);
v___x_2761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2756_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2764_ = l_Lean_Json_opt___redArg(v___x_2750_, v___x_2763_, v_data_x3f_2749_);
v___x_2765_ = l_List_appendTR___redArg(v___x_2762_, v___x_2764_);
v___x_2766_ = l_Lean_Json_mkObj(v___x_2765_);
lean_dec(v___x_2765_);
lean_inc_ref(v___y_2754_);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___y_2754_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
lean_ctor_set(v___x_2768_, 1, v___x_2760_);
v___x_2769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___y_2753_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___y_2668_ = v___x_2769_;
goto v___jp_2667_;
}
v___jp_2771_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2770_);
lean_ctor_set(v___x_2773_, 1, v___y_2772_);
v___x_2774_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2775_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2747_)
{
case 0:
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2776_;
goto v___jp_2751_;
}
case 1:
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2777_;
goto v___jp_2751_;
}
case 2:
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2778_;
goto v___jp_2751_;
}
case 3:
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2779_;
goto v___jp_2751_;
}
case 4:
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2780_;
goto v___jp_2751_;
}
case 5:
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2781_;
goto v___jp_2751_;
}
case 6:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2782_;
goto v___jp_2751_;
}
case 7:
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2783_;
goto v___jp_2751_;
}
case 8:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2784_;
goto v___jp_2751_;
}
case 9:
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2785_;
goto v___jp_2751_;
}
case 10:
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2786_;
goto v___jp_2751_;
}
default: 
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2752_ = v___x_2775_;
v___y_2753_ = v___x_2773_;
v___y_2754_ = v___x_2774_;
v___y_2755_ = v___x_2787_;
goto v___jp_2751_;
}
}
}
}
}
v___jp_2667_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2666_);
lean_ctor_set(v___x_2669_, 1, v___y_2668_);
v___x_2670_ = l_Lean_Json_mkObj(v___x_2669_);
lean_dec_ref_known(v___x_2669_, 2);
v___x_2671_ = l_Lean_Json_compress(v___x_2670_);
v___x_2672_ = lean_string_append(v___x_2664_, v___x_2671_);
lean_dec_ref(v___x_2671_);
v___x_2673_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2674_ = lean_string_append(v___x_2672_, v___x_2673_);
v___x_2675_ = lean_mk_io_user_error(v___x_2674_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set_tag(v___x_2619_, 1);
lean_ctor_set(v___x_2619_, 0, v___x_2675_);
v___x_2677_ = v___x_2619_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec_ref(v_inst_2614_);
lean_dec_ref(v_expectedMethod_2613_);
v_a_2805_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2616_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2616_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* v_h_2813_, lean_object* v_nBytes_2814_, lean_object* v_expectedMethod_2815_, lean_object* v_inst_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_IO_FS_Stream_readRequestAs___redArg(v_h_2813_, v_nBytes_2814_, v_expectedMethod_2815_, v_inst_2816_);
lean_dec(v_nBytes_2814_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs(lean_object* v_h_2819_, lean_object* v_nBytes_2820_, lean_object* v_expectedMethod_2821_, lean_object* v_00_u03b1_2822_, lean_object* v_inst_2823_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_IO_FS_Stream_readRequestAs___redArg(v_h_2819_, v_nBytes_2820_, v_expectedMethod_2821_, v_inst_2823_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object* v_h_2826_, lean_object* v_nBytes_2827_, lean_object* v_expectedMethod_2828_, lean_object* v_00_u03b1_2829_, lean_object* v_inst_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_IO_FS_Stream_readRequestAs(v_h_2826_, v_nBytes_2827_, v_expectedMethod_2828_, v_00_u03b1_2829_, v_inst_2830_);
lean_dec(v_nBytes_2827_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object* v_h_2834_, lean_object* v_nBytes_2835_, lean_object* v_expectedMethod_2836_, lean_object* v_inst_2837_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_IO_FS_Stream_readMessage(v_h_2834_, v_nBytes_2835_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_3026_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_3026_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_3026_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
if (lean_obj_tag(v_a_2840_) == 1)
{
lean_object* v_method_2844_; lean_object* v_params_x3f_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2885_; 
v_method_2844_ = lean_ctor_get(v_a_2840_, 0);
v_params_x3f_2845_ = lean_ctor_get(v_a_2840_, 1);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_a_2840_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2847_ = v_a_2840_;
v_isShared_2848_ = v_isSharedCheck_2885_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_params_x3f_2845_);
lean_inc(v_method_2844_);
lean_dec(v_a_2840_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2885_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_string_dec_eq(v_method_2844_, v_expectedMethod_2836_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
lean_del_object(v___x_2847_);
lean_dec(v_params_x3f_2845_);
lean_dec_ref(v_inst_2837_);
v___x_2850_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2851_ = lean_string_append(v___x_2850_, v_expectedMethod_2836_);
lean_dec_ref(v_expectedMethod_2836_);
v___x_2852_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2853_ = lean_string_append(v___x_2851_, v___x_2852_);
v___x_2854_ = lean_string_append(v___x_2853_, v_method_2844_);
lean_dec_ref(v_method_2844_);
v___x_2855_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2856_ = lean_string_append(v___x_2854_, v___x_2855_);
v___x_2857_ = lean_mk_io_user_error(v___x_2856_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set_tag(v___x_2842_, 1);
lean_ctor_set(v___x_2842_, 0, v___x_2857_);
v___x_2859_ = v___x_2842_;
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
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec_ref(v_method_2844_);
v___x_2861_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2862_ = l_Lean_Option_toJson___redArg(v___x_2861_, v_params_x3f_2845_);
lean_inc(v___x_2862_);
v___x_2863_ = lean_apply_1(v_inst_2837_, v___x_2862_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
lean_del_object(v___x_2847_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v___x_2865_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2866_ = l_Lean_Json_compress(v___x_2862_);
v___x_2867_ = lean_string_append(v___x_2865_, v___x_2866_);
lean_dec_ref(v___x_2866_);
v___x_2868_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2869_ = lean_string_append(v___x_2867_, v___x_2868_);
v___x_2870_ = lean_string_append(v___x_2869_, v_expectedMethod_2836_);
lean_dec_ref(v_expectedMethod_2836_);
v___x_2871_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2872_ = lean_string_append(v___x_2870_, v___x_2871_);
v___x_2873_ = lean_string_append(v___x_2872_, v_a_2864_);
lean_dec(v_a_2864_);
v___x_2874_ = lean_mk_io_user_error(v___x_2873_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set_tag(v___x_2842_, 1);
lean_ctor_set(v___x_2842_, 0, v___x_2874_);
v___x_2876_ = v___x_2842_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; 
lean_dec(v___x_2862_);
v_a_2878_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2863_, 1);
if (v_isShared_2848_ == 0)
{
lean_ctor_set_tag(v___x_2847_, 0);
lean_ctor_set(v___x_2847_, 1, v_a_2878_);
lean_ctor_set(v___x_2847_, 0, v_expectedMethod_2836_);
v___x_2880_ = v___x_2847_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_expectedMethod_2836_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_a_2878_);
v___x_2880_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2882_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2880_);
v___x_2882_ = v___x_2842_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
}
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___y_2890_; 
lean_dec_ref(v_inst_2837_);
lean_dec_ref(v_expectedMethod_2836_);
v___x_2886_ = ((lean_object*)(l_IO_FS_Stream_readNotificationAs___redArg___closed__0));
v___x_2887_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2888_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2840_))
{
case 0:
{
lean_object* v_id_2901_; lean_object* v_method_2902_; lean_object* v_params_x3f_2903_; lean_object* v___x_2904_; lean_object* v___y_2906_; 
v_id_2901_ = lean_ctor_get(v_a_2840_, 0);
lean_inc(v_id_2901_);
v_method_2902_ = lean_ctor_get(v_a_2840_, 1);
lean_inc_ref(v_method_2902_);
v_params_x3f_2903_ = lean_ctor_get(v_a_2840_, 2);
lean_inc(v_params_x3f_2903_);
lean_dec_ref_known(v_a_2840_, 3);
v___x_2904_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2901_) == 0)
{
lean_object* v_s_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
v_s_2917_ = lean_ctor_get(v_id_2901_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_id_2901_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v_id_2901_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_s_2917_);
lean_dec(v_id_2901_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set_tag(v___x_2919_, 3);
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_s_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
v___y_2906_ = v___x_2922_;
goto v___jp_2905_;
}
}
}
else
{
lean_object* v_n_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
v_n_2925_ = lean_ctor_get(v_id_2901_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_id_2901_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v_id_2901_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_n_2925_);
lean_dec(v_id_2901_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
lean_ctor_set_tag(v___x_2927_, 2);
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_n_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
v___y_2906_ = v___x_2930_;
goto v___jp_2905_;
}
}
}
v___jp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2904_);
lean_ctor_set(v___x_2907_, 1, v___y_2906_);
v___x_2908_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2909_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_method_2902_);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = lean_box(0);
v___x_2912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2907_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2915_ = l_Lean_Json_opt___redArg(v___x_2887_, v___x_2914_, v_params_x3f_2903_);
v___x_2916_ = l_List_appendTR___redArg(v___x_2913_, v___x_2915_);
v___y_2890_ = v___x_2916_;
goto v___jp_2889_;
}
}
case 1:
{
lean_object* v_method_2933_; lean_object* v_params_x3f_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_method_2933_ = lean_ctor_get(v_a_2840_, 0);
lean_inc_ref(v_method_2933_);
v_params_x3f_2934_ = lean_ctor_get(v_a_2840_, 1);
lean_inc(v_params_x3f_2934_);
lean_dec_ref_known(v_a_2840_, 2);
v___x_2935_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2936_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2936_, 0, v_method_2933_);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2935_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___x_2938_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2939_ = l_Lean_Json_opt___redArg(v___x_2887_, v___x_2938_, v_params_x3f_2934_);
v___x_2940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2937_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___y_2890_ = v___x_2940_;
goto v___jp_2889_;
}
case 2:
{
lean_object* v_id_2941_; lean_object* v_result_2942_; lean_object* v___x_2943_; lean_object* v___y_2945_; 
v_id_2941_ = lean_ctor_get(v_a_2840_, 0);
lean_inc(v_id_2941_);
v_result_2942_ = lean_ctor_get(v_a_2840_, 1);
lean_inc(v_result_2942_);
lean_dec_ref_known(v_a_2840_, 2);
v___x_2943_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2941_) == 0)
{
lean_object* v_s_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
v_s_2952_ = lean_ctor_get(v_id_2941_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_id_2941_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v_id_2941_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_s_2952_);
lean_dec(v_id_2941_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set_tag(v___x_2954_, 3);
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_s_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
v___y_2945_ = v___x_2957_;
goto v___jp_2944_;
}
}
}
else
{
lean_object* v_n_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
v_n_2960_ = lean_ctor_get(v_id_2941_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v_id_2941_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v_id_2941_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_n_2960_);
lean_dec(v_id_2941_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set_tag(v___x_2962_, 2);
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_n_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
v___y_2945_ = v___x_2965_;
goto v___jp_2944_;
}
}
}
v___jp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2943_);
lean_ctor_set(v___x_2946_, 1, v___y_2945_);
v___x_2947_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v_result_2942_);
v___x_2949_ = lean_box(0);
v___x_2950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2948_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2946_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___y_2890_ = v___x_2951_;
goto v___jp_2889_;
}
}
default: 
{
lean_object* v_id_2968_; uint8_t v_code_2969_; lean_object* v_message_2970_; lean_object* v_data_x3f_2971_; lean_object* v___x_2972_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___x_2992_; lean_object* v___y_2994_; 
v_id_2968_ = lean_ctor_get(v_a_2840_, 0);
lean_inc(v_id_2968_);
v_code_2969_ = lean_ctor_get_uint8(v_a_2840_, sizeof(void*)*3);
v_message_2970_ = lean_ctor_get(v_a_2840_, 1);
lean_inc_ref(v_message_2970_);
v_data_x3f_2971_ = lean_ctor_get(v_a_2840_, 2);
lean_inc(v_data_x3f_2971_);
lean_dec_ref_known(v_a_2840_, 3);
v___x_2972_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2992_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2968_) == 0)
{
lean_object* v_s_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
v_s_3010_ = lean_ctor_get(v_id_2968_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_id_2968_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v_id_2968_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_s_3010_);
lean_dec(v_id_2968_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
lean_ctor_set_tag(v___x_3012_, 3);
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_s_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
v___y_2994_ = v___x_3015_;
goto v___jp_2993_;
}
}
}
else
{
lean_object* v_n_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
v_n_3018_ = lean_ctor_get(v_id_2968_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_id_2968_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v_id_2968_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_n_3018_);
lean_dec(v_id_2968_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set_tag(v___x_3020_, 2);
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_n_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
v___y_2994_ = v___x_3023_;
goto v___jp_2993_;
}
}
}
v___jp_2973_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_inc(v___y_2977_);
lean_inc_ref(v___y_2976_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___y_2976_);
lean_ctor_set(v___x_2978_, 1, v___y_2977_);
v___x_2979_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_message_2970_);
v___x_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2979_);
lean_ctor_set(v___x_2981_, 1, v___x_2980_);
v___x_2982_ = lean_box(0);
v___x_2983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2981_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2978_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2986_ = l_Lean_Json_opt___redArg(v___x_2972_, v___x_2985_, v_data_x3f_2971_);
v___x_2987_ = l_List_appendTR___redArg(v___x_2984_, v___x_2986_);
v___x_2988_ = l_Lean_Json_mkObj(v___x_2987_);
lean_dec(v___x_2987_);
lean_inc_ref(v___y_2975_);
v___x_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___y_2975_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
lean_ctor_set(v___x_2990_, 1, v___x_2982_);
v___x_2991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___y_2974_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
v___y_2890_ = v___x_2991_;
goto v___jp_2889_;
}
v___jp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2992_);
lean_ctor_set(v___x_2995_, 1, v___y_2994_);
v___x_2996_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2997_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2969_)
{
case 0:
{
lean_object* v___x_2998_; 
v___x_2998_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2998_;
goto v___jp_2973_;
}
case 1:
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_2999_;
goto v___jp_2973_;
}
case 2:
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_3000_;
goto v___jp_2973_;
}
case 3:
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_3001_;
goto v___jp_2973_;
}
case 4:
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_3002_;
goto v___jp_2973_;
}
case 5:
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_3003_;
goto v___jp_2973_;
}
case 6:
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_3004_;
goto v___jp_2973_;
}
case 7:
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_3005_;
goto v___jp_2973_;
}
case 8:
{
lean_object* v___x_3006_; 
v___x_3006_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_3006_;
goto v___jp_2973_;
}
case 9:
{
lean_object* v___x_3007_; 
v___x_3007_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_3007_;
goto v___jp_2973_;
}
case 10:
{
lean_object* v___x_3008_; 
v___x_3008_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_3008_;
goto v___jp_2973_;
}
default: 
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2974_ = v___x_2995_;
v___y_2975_ = v___x_2996_;
v___y_2976_ = v___x_2997_;
v___y_2977_ = v___x_3009_;
goto v___jp_2973_;
}
}
}
}
}
v___jp_2889_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2888_);
lean_ctor_set(v___x_2891_, 1, v___y_2890_);
v___x_2892_ = l_Lean_Json_mkObj(v___x_2891_);
lean_dec_ref_known(v___x_2891_, 2);
v___x_2893_ = l_Lean_Json_compress(v___x_2892_);
v___x_2894_ = lean_string_append(v___x_2886_, v___x_2893_);
lean_dec_ref(v___x_2893_);
v___x_2895_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2896_ = lean_string_append(v___x_2894_, v___x_2895_);
v___x_2897_ = lean_mk_io_user_error(v___x_2896_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set_tag(v___x_2842_, 1);
lean_ctor_set(v___x_2842_, 0, v___x_2897_);
v___x_2899_ = v___x_2842_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref(v_inst_2837_);
lean_dec_ref(v_expectedMethod_2836_);
v_a_3027_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2839_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2839_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* v_h_3035_, lean_object* v_nBytes_3036_, lean_object* v_expectedMethod_3037_, lean_object* v_inst_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_IO_FS_Stream_readNotificationAs___redArg(v_h_3035_, v_nBytes_3036_, v_expectedMethod_3037_, v_inst_3038_);
lean_dec(v_nBytes_3036_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs(lean_object* v_h_3041_, lean_object* v_nBytes_3042_, lean_object* v_expectedMethod_3043_, lean_object* v_00_u03b1_3044_, lean_object* v_inst_3045_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_IO_FS_Stream_readNotificationAs___redArg(v_h_3041_, v_nBytes_3042_, v_expectedMethod_3043_, v_inst_3045_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object* v_h_3048_, lean_object* v_nBytes_3049_, lean_object* v_expectedMethod_3050_, lean_object* v_00_u03b1_3051_, lean_object* v_inst_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_IO_FS_Stream_readNotificationAs(v_h_3048_, v_nBytes_3049_, v_expectedMethod_3050_, v_00_u03b1_3051_, v_inst_3052_);
lean_dec(v_nBytes_3049_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object* v_h_3059_, lean_object* v_nBytes_3060_, lean_object* v_expectedID_3061_, lean_object* v_inst_3062_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_IO_FS_Stream_readMessage(v_h_3059_, v_nBytes_3060_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3268_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3067_ = v___x_3064_;
v_isShared_3068_ = v_isSharedCheck_3268_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3064_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3268_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___y_3070_; lean_object* v___y_3071_; 
if (lean_obj_tag(v_a_3065_) == 2)
{
lean_object* v_id_3077_; lean_object* v_result_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3129_; 
v_id_3077_ = lean_ctor_get(v_a_3065_, 0);
v_result_3078_ = lean_ctor_get(v_a_3065_, 1);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_a_3065_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3080_ = v_a_3065_;
v_isShared_3081_ = v_isSharedCheck_3129_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_result_3078_);
lean_inc(v_id_3077_);
lean_dec(v_a_3065_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3129_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
uint8_t v___x_3082_; 
v___x_3082_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3077_, v_expectedID_3061_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; lean_object* v___y_3085_; 
lean_del_object(v___x_3080_);
lean_dec(v_result_3078_);
lean_dec_ref(v_inst_3062_);
v___x_3083_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__0));
switch(lean_obj_tag(v_expectedID_3061_))
{
case 0:
{
lean_object* v_s_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v_s_3095_ = lean_ctor_get(v_expectedID_3061_, 0);
lean_inc_ref(v_s_3095_);
lean_dec_ref_known(v_expectedID_3061_, 1);
v___x_3096_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3097_ = lean_string_append(v___x_3096_, v_s_3095_);
lean_dec_ref(v_s_3095_);
v___x_3098_ = lean_string_append(v___x_3097_, v___x_3096_);
v___y_3085_ = v___x_3098_;
goto v___jp_3084_;
}
case 1:
{
lean_object* v_n_3099_; lean_object* v___x_3100_; 
v_n_3099_ = lean_ctor_get(v_expectedID_3061_, 0);
lean_inc_ref(v_n_3099_);
lean_dec_ref_known(v_expectedID_3061_, 1);
v___x_3100_ = l_Lean_JsonNumber_toString(v_n_3099_);
v___y_3085_ = v___x_3100_;
goto v___jp_3084_;
}
default: 
{
lean_object* v___x_3101_; 
v___x_3101_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___y_3085_ = v___x_3101_;
goto v___jp_3084_;
}
}
v___jp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_string_append(v___x_3083_, v___y_3085_);
lean_dec_ref(v___y_3085_);
v___x_3087_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__1));
v___x_3088_ = lean_string_append(v___x_3086_, v___x_3087_);
if (lean_obj_tag(v_id_3077_) == 0)
{
lean_object* v_s_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v_s_3089_ = lean_ctor_get(v_id_3077_, 0);
lean_inc_ref(v_s_3089_);
lean_dec_ref_known(v_id_3077_, 1);
v___x_3090_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3091_ = lean_string_append(v___x_3090_, v_s_3089_);
lean_dec_ref(v_s_3089_);
v___x_3092_ = lean_string_append(v___x_3091_, v___x_3090_);
v___y_3070_ = v___x_3088_;
v___y_3071_ = v___x_3092_;
goto v___jp_3069_;
}
else
{
lean_object* v_n_3093_; lean_object* v___x_3094_; 
v_n_3093_ = lean_ctor_get(v_id_3077_, 0);
lean_inc_ref(v_n_3093_);
lean_dec_ref_known(v_id_3077_, 1);
v___x_3094_ = l_Lean_JsonNumber_toString(v_n_3093_);
v___y_3070_ = v___x_3088_;
v___y_3071_ = v___x_3094_;
goto v___jp_3069_;
}
}
}
else
{
lean_object* v___x_3102_; 
lean_dec(v_id_3077_);
lean_del_object(v___x_3067_);
lean_inc(v_result_3078_);
v___x_3102_ = lean_apply_1(v_inst_3062_, v_result_3078_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3117_; 
lean_del_object(v___x_3080_);
lean_dec(v_expectedID_3061_);
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3117_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3117_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3107_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__2));
v___x_3108_ = l_Lean_Json_compress(v_result_3078_);
v___x_3109_ = lean_string_append(v___x_3107_, v___x_3108_);
lean_dec_ref(v___x_3108_);
v___x_3110_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_3111_ = lean_string_append(v___x_3109_, v___x_3110_);
v___x_3112_ = lean_string_append(v___x_3111_, v_a_3103_);
lean_dec(v_a_3103_);
v___x_3113_ = lean_mk_io_user_error(v___x_3112_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set_tag(v___x_3105_, 1);
lean_ctor_set(v___x_3105_, 0, v___x_3113_);
v___x_3115_ = v___x_3105_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_result_3078_);
v_a_3118_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3120_ = v___x_3102_;
v_isShared_3121_ = v_isSharedCheck_3128_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3102_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3128_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set_tag(v___x_3080_, 0);
lean_ctor_set(v___x_3080_, 1, v_a_3118_);
lean_ctor_set(v___x_3080_, 0, v_expectedID_3061_);
v___x_3123_ = v___x_3080_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_expectedID_3061_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3125_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set_tag(v___x_3120_, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3123_);
v___x_3125_ = v___x_3120_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3123_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___y_3134_; 
lean_del_object(v___x_3067_);
lean_dec_ref(v_inst_3062_);
lean_dec(v_expectedID_3061_);
v___x_3130_ = ((lean_object*)(l_IO_FS_Stream_readResponseAs___redArg___closed__3));
v___x_3131_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_3132_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_3065_))
{
case 0:
{
lean_object* v_id_3143_; lean_object* v_method_3144_; lean_object* v_params_x3f_3145_; lean_object* v___x_3146_; lean_object* v___y_3148_; 
v_id_3143_ = lean_ctor_get(v_a_3065_, 0);
lean_inc(v_id_3143_);
v_method_3144_ = lean_ctor_get(v_a_3065_, 1);
lean_inc_ref(v_method_3144_);
v_params_x3f_3145_ = lean_ctor_get(v_a_3065_, 2);
lean_inc(v_params_x3f_3145_);
lean_dec_ref_known(v_a_3065_, 3);
v___x_3146_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3143_) == 0)
{
lean_object* v_s_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
v_s_3159_ = lean_ctor_get(v_id_3143_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_id_3143_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v_id_3143_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_s_3159_);
lean_dec(v_id_3143_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
lean_ctor_set_tag(v___x_3161_, 3);
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_s_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
v___y_3148_ = v___x_3164_;
goto v___jp_3147_;
}
}
}
else
{
lean_object* v_n_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
v_n_3167_ = lean_ctor_get(v_id_3143_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_id_3143_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v_id_3143_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_n_3167_);
lean_dec(v_id_3143_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set_tag(v___x_3169_, 2);
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_n_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
v___y_3148_ = v___x_3172_;
goto v___jp_3147_;
}
}
}
v___jp_3147_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3146_);
lean_ctor_set(v___x_3149_, 1, v___y_3148_);
v___x_3150_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3151_, 0, v_method_3144_);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3150_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3152_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3149_);
lean_ctor_set(v___x_3155_, 1, v___x_3154_);
v___x_3156_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3157_ = l_Lean_Json_opt___redArg(v___x_3131_, v___x_3156_, v_params_x3f_3145_);
v___x_3158_ = l_List_appendTR___redArg(v___x_3155_, v___x_3157_);
v___y_3134_ = v___x_3158_;
goto v___jp_3133_;
}
}
case 1:
{
lean_object* v_method_3175_; lean_object* v_params_x3f_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_method_3175_ = lean_ctor_get(v_a_3065_, 0);
lean_inc_ref(v_method_3175_);
v_params_x3f_3176_ = lean_ctor_get(v_a_3065_, 1);
lean_inc(v_params_x3f_3176_);
lean_dec_ref_known(v_a_3065_, 2);
v___x_3177_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3178_, 0, v_method_3175_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3177_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3181_ = l_Lean_Json_opt___redArg(v___x_3131_, v___x_3180_, v_params_x3f_3176_);
v___x_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3179_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___y_3134_ = v___x_3182_;
goto v___jp_3133_;
}
case 2:
{
lean_object* v_id_3183_; lean_object* v_result_3184_; lean_object* v___x_3185_; lean_object* v___y_3187_; 
v_id_3183_ = lean_ctor_get(v_a_3065_, 0);
lean_inc(v_id_3183_);
v_result_3184_ = lean_ctor_get(v_a_3065_, 1);
lean_inc(v_result_3184_);
lean_dec_ref_known(v_a_3065_, 2);
v___x_3185_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3183_) == 0)
{
lean_object* v_s_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
v_s_3194_ = lean_ctor_get(v_id_3183_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_id_3183_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v_id_3183_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_s_3194_);
lean_dec(v_id_3183_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
lean_ctor_set_tag(v___x_3196_, 3);
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_s_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
v___y_3187_ = v___x_3199_;
goto v___jp_3186_;
}
}
}
else
{
lean_object* v_n_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
v_n_3202_ = lean_ctor_get(v_id_3183_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_id_3183_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v_id_3183_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_n_3202_);
lean_dec(v_id_3183_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 2);
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_n_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
v___y_3187_ = v___x_3207_;
goto v___jp_3186_;
}
}
}
v___jp_3186_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3185_);
lean_ctor_set(v___x_3188_, 1, v___y_3187_);
v___x_3189_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set(v___x_3190_, 1, v_result_3184_);
v___x_3191_ = lean_box(0);
v___x_3192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3188_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___y_3134_ = v___x_3193_;
goto v___jp_3133_;
}
}
default: 
{
lean_object* v_id_3210_; uint8_t v_code_3211_; lean_object* v_message_3212_; lean_object* v_data_x3f_3213_; lean_object* v___x_3214_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___x_3234_; lean_object* v___y_3236_; 
v_id_3210_ = lean_ctor_get(v_a_3065_, 0);
lean_inc(v_id_3210_);
v_code_3211_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*3);
v_message_3212_ = lean_ctor_get(v_a_3065_, 1);
lean_inc_ref(v_message_3212_);
v_data_x3f_3213_ = lean_ctor_get(v_a_3065_, 2);
lean_inc(v_data_x3f_3213_);
lean_dec_ref_known(v_a_3065_, 3);
v___x_3214_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_3234_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3210_) == 0)
{
lean_object* v_s_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
v_s_3252_ = lean_ctor_get(v_id_3210_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_id_3210_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v_id_3210_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_s_3252_);
lean_dec(v_id_3210_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
lean_ctor_set_tag(v___x_3254_, 3);
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_s_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
v___y_3236_ = v___x_3257_;
goto v___jp_3235_;
}
}
}
else
{
lean_object* v_n_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
v_n_3260_ = lean_ctor_get(v_id_3210_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_id_3210_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v_id_3210_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_n_3260_);
lean_dec(v_id_3210_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
lean_ctor_set_tag(v___x_3262_, 2);
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_n_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
v___y_3236_ = v___x_3265_;
goto v___jp_3235_;
}
}
}
v___jp_3215_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
lean_inc(v___y_3219_);
lean_inc_ref(v___y_3217_);
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___y_3217_);
lean_ctor_set(v___x_3220_, 1, v___y_3219_);
v___x_3221_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3222_, 0, v_message_3212_);
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3221_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = lean_box(0);
v___x_3225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3223_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3220_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3228_ = l_Lean_Json_opt___redArg(v___x_3214_, v___x_3227_, v_data_x3f_3213_);
v___x_3229_ = l_List_appendTR___redArg(v___x_3226_, v___x_3228_);
v___x_3230_ = l_Lean_Json_mkObj(v___x_3229_);
lean_dec(v___x_3229_);
lean_inc_ref(v___y_3216_);
v___x_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___y_3216_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v___x_3224_);
v___x_3233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___y_3218_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___y_3134_ = v___x_3233_;
goto v___jp_3133_;
}
v___jp_3235_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3234_);
lean_ctor_set(v___x_3237_, 1, v___y_3236_);
v___x_3238_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3239_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3211_)
{
case 0:
{
lean_object* v___x_3240_; 
v___x_3240_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3240_;
goto v___jp_3215_;
}
case 1:
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3241_;
goto v___jp_3215_;
}
case 2:
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3242_;
goto v___jp_3215_;
}
case 3:
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3243_;
goto v___jp_3215_;
}
case 4:
{
lean_object* v___x_3244_; 
v___x_3244_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3244_;
goto v___jp_3215_;
}
case 5:
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3245_;
goto v___jp_3215_;
}
case 6:
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3246_;
goto v___jp_3215_;
}
case 7:
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3247_;
goto v___jp_3215_;
}
case 8:
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3248_;
goto v___jp_3215_;
}
case 9:
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3249_;
goto v___jp_3215_;
}
case 10:
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3250_;
goto v___jp_3215_;
}
default: 
{
lean_object* v___x_3251_; 
v___x_3251_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3216_ = v___x_3238_;
v___y_3217_ = v___x_3239_;
v___y_3218_ = v___x_3237_;
v___y_3219_ = v___x_3251_;
goto v___jp_3215_;
}
}
}
}
}
v___jp_3133_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3132_);
lean_ctor_set(v___x_3135_, 1, v___y_3134_);
v___x_3136_ = l_Lean_Json_mkObj(v___x_3135_);
lean_dec_ref_known(v___x_3135_, 2);
v___x_3137_ = l_Lean_Json_compress(v___x_3136_);
v___x_3138_ = lean_string_append(v___x_3130_, v___x_3137_);
lean_dec_ref(v___x_3137_);
v___x_3139_ = ((lean_object*)(l_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_3140_ = lean_string_append(v___x_3138_, v___x_3139_);
v___x_3141_ = lean_mk_io_user_error(v___x_3140_);
v___x_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
return v___x_3142_;
}
}
v___jp_3069_:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3072_ = lean_string_append(v___y_3070_, v___y_3071_);
lean_dec_ref(v___y_3071_);
v___x_3073_ = lean_mk_io_user_error(v___x_3072_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 1);
lean_ctor_set(v___x_3067_, 0, v___x_3073_);
v___x_3075_ = v___x_3067_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_dec_ref(v_inst_3062_);
lean_dec(v_expectedID_3061_);
v_a_3269_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3064_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3064_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* v_h_3277_, lean_object* v_nBytes_3278_, lean_object* v_expectedID_3279_, lean_object* v_inst_3280_, lean_object* v_a_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_IO_FS_Stream_readResponseAs___redArg(v_h_3277_, v_nBytes_3278_, v_expectedID_3279_, v_inst_3280_);
lean_dec(v_nBytes_3278_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs(lean_object* v_h_3283_, lean_object* v_nBytes_3284_, lean_object* v_expectedID_3285_, lean_object* v_00_u03b1_3286_, lean_object* v_inst_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_IO_FS_Stream_readResponseAs___redArg(v_h_3283_, v_nBytes_3284_, v_expectedID_3285_, v_inst_3287_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readResponseAs___boxed(lean_object* v_h_3290_, lean_object* v_nBytes_3291_, lean_object* v_expectedID_3292_, lean_object* v_00_u03b1_3293_, lean_object* v_inst_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_IO_FS_Stream_readResponseAs(v_h_3290_, v_nBytes_3291_, v_expectedID_3292_, v_00_u03b1_3293_, v_inst_3294_);
lean_dec(v_nBytes_3291_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(lean_object* v_k_3297_, lean_object* v_x_3298_){
_start:
{
if (lean_obj_tag(v_x_3298_) == 0)
{
lean_object* v___x_3299_; 
lean_dec_ref(v_k_3297_);
v___x_3299_ = lean_box(0);
return v___x_3299_;
}
else
{
lean_object* v_val_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_val_3300_ = lean_ctor_get(v_x_3298_, 0);
lean_inc(v_val_3300_);
lean_dec_ref_known(v_x_3298_, 1);
v___x_3301_ = l_Lean_Json_Structured_toJson(v_val_3300_);
v___x_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3302_, 0, v_k_3297_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(lean_object* v_k_3305_, lean_object* v_x_3306_){
_start:
{
if (lean_obj_tag(v_x_3306_) == 0)
{
lean_object* v___x_3307_; 
lean_dec_ref(v_k_3305_);
v___x_3307_ = lean_box(0);
return v___x_3307_;
}
else
{
lean_object* v_val_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_val_3308_ = lean_ctor_get(v_x_3306_, 0);
lean_inc(v_val_3308_);
v___x_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3309_, 0, v_k_3305_);
lean_ctor_set(v___x_3309_, 1, v_val_3308_);
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
return v___x_3311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* v_k_3312_, lean_object* v_x_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(v_k_3312_, v_x_3313_);
lean_dec(v_x_3313_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage(lean_object* v_h_3315_, lean_object* v_m_3316_){
_start:
{
lean_object* v___x_3318_; lean_object* v___y_3320_; 
v___x_3318_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_3316_))
{
case 0:
{
lean_object* v_id_3324_; lean_object* v_method_3325_; lean_object* v_params_x3f_3326_; lean_object* v___x_3327_; lean_object* v___y_3329_; 
v_id_3324_ = lean_ctor_get(v_m_3316_, 0);
lean_inc(v_id_3324_);
v_method_3325_ = lean_ctor_get(v_m_3316_, 1);
lean_inc_ref(v_method_3325_);
v_params_x3f_3326_ = lean_ctor_get(v_m_3316_, 2);
lean_inc(v_params_x3f_3326_);
lean_dec_ref_known(v_m_3316_, 3);
v___x_3327_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3324_))
{
case 0:
{
lean_object* v_s_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
v_s_3340_ = lean_ctor_get(v_id_3324_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v_id_3324_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v_id_3324_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_s_3340_);
lean_dec(v_id_3324_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set_tag(v___x_3342_, 3);
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_s_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
v___y_3329_ = v___x_3345_;
goto v___jp_3328_;
}
}
}
case 1:
{
lean_object* v_n_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
v_n_3348_ = lean_ctor_get(v_id_3324_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_id_3324_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v_id_3324_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_n_3348_);
lean_dec(v_id_3324_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 2);
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_n_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
v___y_3329_ = v___x_3353_;
goto v___jp_3328_;
}
}
}
default: 
{
lean_object* v___x_3356_; 
v___x_3356_ = lean_box(0);
v___y_3329_ = v___x_3356_;
goto v___jp_3328_;
}
}
v___jp_3328_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3327_);
lean_ctor_set(v___x_3330_, 1, v___y_3329_);
v___x_3331_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3332_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3332_, 0, v_method_3325_);
v___x_3333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3331_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = lean_box(0);
v___x_3335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3330_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3338_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(v___x_3337_, v_params_x3f_3326_);
v___x_3339_ = l_List_appendTR___redArg(v___x_3336_, v___x_3338_);
v___y_3320_ = v___x_3339_;
goto v___jp_3319_;
}
}
case 1:
{
lean_object* v_method_3357_; lean_object* v_params_x3f_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3370_; 
v_method_3357_ = lean_ctor_get(v_m_3316_, 0);
v_params_x3f_3358_ = lean_ctor_get(v_m_3316_, 1);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_m_3316_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3360_ = v_m_3316_;
v_isShared_3361_ = v_isSharedCheck_3370_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_params_x3f_3358_);
lean_inc(v_method_3357_);
lean_dec(v_m_3316_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3370_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3362_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3363_, 0, v_method_3357_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 0);
lean_ctor_set(v___x_3360_, 1, v___x_3363_);
lean_ctor_set(v___x_3360_, 0, v___x_3362_);
v___x_3365_ = v___x_3360_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3366_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3367_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__0(v___x_3366_, v_params_x3f_3358_);
v___x_3368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3365_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___y_3320_ = v___x_3368_;
goto v___jp_3319_;
}
}
}
case 2:
{
lean_object* v_id_3371_; lean_object* v_result_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3404_; 
v_id_3371_ = lean_ctor_get(v_m_3316_, 0);
v_result_3372_ = lean_ctor_get(v_m_3316_, 1);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_m_3316_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3374_ = v_m_3316_;
v_isShared_3375_ = v_isSharedCheck_3404_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_result_3372_);
lean_inc(v_id_3371_);
lean_dec(v_m_3316_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3404_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___y_3378_; 
v___x_3376_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3371_))
{
case 0:
{
lean_object* v_s_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
v_s_3387_ = lean_ctor_get(v_id_3371_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_id_3371_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v_id_3371_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_s_3387_);
lean_dec(v_id_3371_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set_tag(v___x_3389_, 3);
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_s_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
v___y_3378_ = v___x_3392_;
goto v___jp_3377_;
}
}
}
case 1:
{
lean_object* v_n_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
v_n_3395_ = lean_ctor_get(v_id_3371_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_id_3371_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v_id_3371_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_n_3395_);
lean_dec(v_id_3371_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 2);
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_n_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
v___y_3378_ = v___x_3400_;
goto v___jp_3377_;
}
}
}
default: 
{
lean_object* v___x_3403_; 
v___x_3403_ = lean_box(0);
v___y_3378_ = v___x_3403_;
goto v___jp_3377_;
}
}
v___jp_3377_:
{
lean_object* v___x_3380_; 
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 0);
lean_ctor_set(v___x_3374_, 1, v___y_3378_);
lean_ctor_set(v___x_3374_, 0, v___x_3376_);
v___x_3380_ = v___x_3374_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v___y_3378_);
v___x_3380_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3381_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
lean_ctor_set(v___x_3382_, 1, v_result_3372_);
v___x_3383_ = lean_box(0);
v___x_3384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3382_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3380_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___y_3320_ = v___x_3385_;
goto v___jp_3319_;
}
}
}
}
default: 
{
lean_object* v_id_3405_; uint8_t v_code_3406_; lean_object* v_message_3407_; lean_object* v_data_x3f_3408_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___x_3428_; lean_object* v___y_3430_; 
v_id_3405_ = lean_ctor_get(v_m_3316_, 0);
lean_inc(v_id_3405_);
v_code_3406_ = lean_ctor_get_uint8(v_m_3316_, sizeof(void*)*3);
v_message_3407_ = lean_ctor_get(v_m_3316_, 1);
lean_inc_ref(v_message_3407_);
v_data_x3f_3408_ = lean_ctor_get(v_m_3316_, 2);
lean_inc(v_data_x3f_3408_);
lean_dec_ref_known(v_m_3316_, 3);
v___x_3428_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3405_))
{
case 0:
{
lean_object* v_s_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
v_s_3446_ = lean_ctor_get(v_id_3405_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_id_3405_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v_id_3405_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_s_3446_);
lean_dec(v_id_3405_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
lean_ctor_set_tag(v___x_3448_, 3);
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_s_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
v___y_3430_ = v___x_3451_;
goto v___jp_3429_;
}
}
}
case 1:
{
lean_object* v_n_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
v_n_3454_ = lean_ctor_get(v_id_3405_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v_id_3405_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v_id_3405_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_n_3454_);
lean_dec(v_id_3405_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set_tag(v___x_3456_, 2);
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_n_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
v___y_3430_ = v___x_3459_;
goto v___jp_3429_;
}
}
}
default: 
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_box(0);
v___y_3430_ = v___x_3462_;
goto v___jp_3429_;
}
}
v___jp_3409_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_inc(v___y_3413_);
lean_inc_ref(v___y_3412_);
v___x_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___y_3412_);
lean_ctor_set(v___x_3414_, 1, v___y_3413_);
v___x_3415_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3416_, 0, v_message_3407_);
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___x_3418_ = lean_box(0);
v___x_3419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3417_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3414_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3422_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeMessage_spec__1(v___x_3421_, v_data_x3f_3408_);
lean_dec(v_data_x3f_3408_);
v___x_3423_ = l_List_appendTR___redArg(v___x_3420_, v___x_3422_);
v___x_3424_ = l_Lean_Json_mkObj(v___x_3423_);
lean_dec(v___x_3423_);
lean_inc_ref(v___y_3411_);
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___y_3411_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
lean_ctor_set(v___x_3426_, 1, v___x_3418_);
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___y_3410_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___y_3320_ = v___x_3427_;
goto v___jp_3319_;
}
v___jp_3429_:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3428_);
lean_ctor_set(v___x_3431_, 1, v___y_3430_);
v___x_3432_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3433_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3406_)
{
case 0:
{
lean_object* v___x_3434_; 
v___x_3434_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3434_;
goto v___jp_3409_;
}
case 1:
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3435_;
goto v___jp_3409_;
}
case 2:
{
lean_object* v___x_3436_; 
v___x_3436_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3436_;
goto v___jp_3409_;
}
case 3:
{
lean_object* v___x_3437_; 
v___x_3437_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3437_;
goto v___jp_3409_;
}
case 4:
{
lean_object* v___x_3438_; 
v___x_3438_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3438_;
goto v___jp_3409_;
}
case 5:
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3439_;
goto v___jp_3409_;
}
case 6:
{
lean_object* v___x_3440_; 
v___x_3440_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3440_;
goto v___jp_3409_;
}
case 7:
{
lean_object* v___x_3441_; 
v___x_3441_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3441_;
goto v___jp_3409_;
}
case 8:
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3442_;
goto v___jp_3409_;
}
case 9:
{
lean_object* v___x_3443_; 
v___x_3443_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3443_;
goto v___jp_3409_;
}
case 10:
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3444_;
goto v___jp_3409_;
}
default: 
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3410_ = v___x_3431_;
v___y_3411_ = v___x_3432_;
v___y_3412_ = v___x_3433_;
v___y_3413_ = v___x_3445_;
goto v___jp_3409_;
}
}
}
}
}
v___jp_3319_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3318_);
lean_ctor_set(v___x_3321_, 1, v___y_3320_);
v___x_3322_ = l_Lean_Json_mkObj(v___x_3321_);
lean_dec_ref_known(v___x_3321_, 2);
v___x_3323_ = l_Lean_IO_FS_Stream_writeJson(v_h_3315_, v___x_3322_);
return v___x_3323_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object* v_h_3463_, lean_object* v_m_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v_res_3466_; 
v_res_3466_ = l_IO_FS_Stream_writeMessage(v_h_3463_, v_m_3464_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg(lean_object* v_inst_3467_, lean_object* v_h_3468_, lean_object* v_r_3469_){
_start:
{
lean_object* v_id_3471_; lean_object* v_method_3472_; lean_object* v_param_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3493_; 
v_id_3471_ = lean_ctor_get(v_r_3469_, 0);
v_method_3472_ = lean_ctor_get(v_r_3469_, 1);
v_param_3473_ = lean_ctor_get(v_r_3469_, 2);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_r_3469_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3475_ = v_r_3469_;
v_isShared_3476_ = v_isSharedCheck_3493_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_param_3473_);
lean_inc(v_method_3472_);
lean_inc(v_id_3471_);
lean_dec(v_r_3469_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3493_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___y_3478_; lean_object* v___x_3483_; 
v___x_3483_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3467_, v_param_3473_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v___x_3484_; 
lean_dec_ref_known(v___x_3483_, 1);
v___x_3484_ = lean_box(0);
v___y_3478_ = v___x_3484_;
goto v___jp_3477_;
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
v_a_3485_ = lean_ctor_get(v___x_3483_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3483_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3483_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
v___y_3478_ = v___x_3490_;
goto v___jp_3477_;
}
}
}
v___jp_3477_:
{
lean_object* v___x_3480_; 
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 2, v___y_3478_);
v___x_3480_ = v___x_3475_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_id_3471_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_method_3472_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v___y_3478_);
v___x_3480_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3481_; 
v___x_3481_ = l_IO_FS_Stream_writeMessage(v_h_3468_, v___x_3480_);
return v___x_3481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___redArg___boxed(lean_object* v_inst_3494_, lean_object* v_h_3495_, lean_object* v_r_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_IO_FS_Stream_writeRequest___redArg(v_inst_3494_, v_h_3495_, v_r_3496_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest(lean_object* v_00_u03b1_3499_, lean_object* v_inst_3500_, lean_object* v_h_3501_, lean_object* v_r_3502_){
_start:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_IO_FS_Stream_writeRequest___redArg(v_inst_3500_, v_h_3501_, v_r_3502_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeRequest___boxed(lean_object* v_00_u03b1_3505_, lean_object* v_inst_3506_, lean_object* v_h_3507_, lean_object* v_r_3508_, lean_object* v_a_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_IO_FS_Stream_writeRequest(v_00_u03b1_3505_, v_inst_3506_, v_h_3507_, v_r_3508_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg(lean_object* v_inst_3511_, lean_object* v_h_3512_, lean_object* v_n_3513_){
_start:
{
lean_object* v_method_3515_; lean_object* v_param_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3536_; 
v_method_3515_ = lean_ctor_get(v_n_3513_, 0);
v_param_3516_ = lean_ctor_get(v_n_3513_, 1);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_n_3513_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3518_ = v_n_3513_;
v_isShared_3519_ = v_isSharedCheck_3536_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_param_3516_);
lean_inc(v_method_3515_);
lean_dec(v_n_3513_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3536_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___y_3521_; lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3511_, v_param_3516_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v___x_3527_; 
lean_dec_ref_known(v___x_3526_, 1);
v___x_3527_ = lean_box(0);
v___y_3521_ = v___x_3527_;
goto v___jp_3520_;
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
v_a_3528_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3526_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3526_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
v___y_3521_ = v___x_3533_;
goto v___jp_3520_;
}
}
}
v___jp_3520_:
{
lean_object* v___x_3523_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set_tag(v___x_3518_, 1);
lean_ctor_set(v___x_3518_, 1, v___y_3521_);
v___x_3523_ = v___x_3518_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_method_3515_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v___y_3521_);
v___x_3523_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_IO_FS_Stream_writeMessage(v_h_3512_, v___x_3523_);
return v___x_3524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___redArg___boxed(lean_object* v_inst_3537_, lean_object* v_h_3538_, lean_object* v_n_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_IO_FS_Stream_writeNotification___redArg(v_inst_3537_, v_h_3538_, v_n_3539_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification(lean_object* v_00_u03b1_3542_, lean_object* v_inst_3543_, lean_object* v_h_3544_, lean_object* v_n_3545_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l_IO_FS_Stream_writeNotification___redArg(v_inst_3543_, v_h_3544_, v_n_3545_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeNotification___boxed(lean_object* v_00_u03b1_3548_, lean_object* v_inst_3549_, lean_object* v_h_3550_, lean_object* v_n_3551_, lean_object* v_a_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_IO_FS_Stream_writeNotification(v_00_u03b1_3548_, v_inst_3549_, v_h_3550_, v_n_3551_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg(lean_object* v_inst_3554_, lean_object* v_h_3555_, lean_object* v_r_3556_){
_start:
{
lean_object* v_id_3558_; lean_object* v_result_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3568_; 
v_id_3558_ = lean_ctor_get(v_r_3556_, 0);
v_result_3559_ = lean_ctor_get(v_r_3556_, 1);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_r_3556_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3561_ = v_r_3556_;
v_isShared_3562_ = v_isSharedCheck_3568_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_result_3559_);
lean_inc(v_id_3558_);
lean_dec(v_r_3556_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3568_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; lean_object* v___x_3565_; 
v___x_3563_ = lean_apply_1(v_inst_3554_, v_result_3559_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set_tag(v___x_3561_, 2);
lean_ctor_set(v___x_3561_, 1, v___x_3563_);
v___x_3565_ = v___x_3561_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_id_3558_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v___x_3563_);
v___x_3565_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_IO_FS_Stream_writeMessage(v_h_3555_, v___x_3565_);
return v___x_3566_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___redArg___boxed(lean_object* v_inst_3569_, lean_object* v_h_3570_, lean_object* v_r_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_IO_FS_Stream_writeResponse___redArg(v_inst_3569_, v_h_3570_, v_r_3571_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse(lean_object* v_00_u03b1_3574_, lean_object* v_inst_3575_, lean_object* v_h_3576_, lean_object* v_r_3577_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_IO_FS_Stream_writeResponse___redArg(v_inst_3575_, v_h_3576_, v_r_3577_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponse___boxed(lean_object* v_00_u03b1_3580_, lean_object* v_inst_3581_, lean_object* v_h_3582_, lean_object* v_r_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_IO_FS_Stream_writeResponse(v_00_u03b1_3580_, v_inst_3581_, v_h_3582_, v_r_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError(lean_object* v_h_3586_, lean_object* v_e_3587_){
_start:
{
lean_object* v_id_3589_; uint8_t v_code_3590_; lean_object* v_message_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3600_; 
v_id_3589_ = lean_ctor_get(v_e_3587_, 0);
v_code_3590_ = lean_ctor_get_uint8(v_e_3587_, sizeof(void*)*3);
v_message_3591_ = lean_ctor_get(v_e_3587_, 1);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_e_3587_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; 
v_unused_3601_ = lean_ctor_get(v_e_3587_, 2);
lean_dec(v_unused_3601_);
v___x_3593_ = v_e_3587_;
v_isShared_3594_ = v_isSharedCheck_3600_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_message_3591_);
lean_inc(v_id_3589_);
lean_dec(v_e_3587_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3600_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3595_; lean_object* v___x_3597_; 
v___x_3595_ = lean_box(0);
if (v_isShared_3594_ == 0)
{
lean_ctor_set_tag(v___x_3593_, 3);
lean_ctor_set(v___x_3593_, 2, v___x_3595_);
v___x_3597_ = v___x_3593_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_id_3589_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_message_3591_);
lean_ctor_set(v_reuseFailAlloc_3599_, 2, v___x_3595_);
lean_ctor_set_uint8(v_reuseFailAlloc_3599_, sizeof(void*)*3, v_code_3590_);
v___x_3597_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_IO_FS_Stream_writeMessage(v_h_3586_, v___x_3597_);
return v___x_3598_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseError___boxed(lean_object* v_h_3602_, lean_object* v_e_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_IO_FS_Stream_writeResponseError(v_h_3602_, v_e_3603_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* v_inst_3606_, lean_object* v_h_3607_, lean_object* v_e_3608_){
_start:
{
lean_object* v_id_3610_; uint8_t v_code_3611_; lean_object* v_message_3612_; lean_object* v_data_x3f_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3633_; 
v_id_3610_ = lean_ctor_get(v_e_3608_, 0);
v_code_3611_ = lean_ctor_get_uint8(v_e_3608_, sizeof(void*)*3);
v_message_3612_ = lean_ctor_get(v_e_3608_, 1);
v_data_x3f_3613_ = lean_ctor_get(v_e_3608_, 2);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_e_3608_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3615_ = v_e_3608_;
v_isShared_3616_ = v_isSharedCheck_3633_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_data_x3f_3613_);
lean_inc(v_message_3612_);
lean_inc(v_id_3610_);
lean_dec(v_e_3608_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3633_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___y_3618_; 
if (lean_obj_tag(v_data_x3f_3613_) == 0)
{
lean_object* v___x_3623_; 
lean_dec_ref(v_inst_3606_);
v___x_3623_ = lean_box(0);
v___y_3618_ = v___x_3623_;
goto v___jp_3617_;
}
else
{
lean_object* v_val_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3632_; 
v_val_3624_ = lean_ctor_get(v_data_x3f_3613_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v_data_x3f_3613_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3626_ = v_data_x3f_3613_;
v_isShared_3627_ = v_isSharedCheck_3632_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_val_3624_);
lean_dec(v_data_x3f_3613_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3632_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3628_ = lean_apply_1(v_inst_3606_, v_val_3624_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 0, v___x_3628_);
v___x_3630_ = v___x_3626_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
v___y_3618_ = v___x_3630_;
goto v___jp_3617_;
}
}
}
v___jp_3617_:
{
lean_object* v___x_3620_; 
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 3);
lean_ctor_set(v___x_3615_, 2, v___y_3618_);
v___x_3620_ = v___x_3615_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_id_3610_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_message_3612_);
lean_ctor_set(v_reuseFailAlloc_3622_, 2, v___y_3618_);
lean_ctor_set_uint8(v_reuseFailAlloc_3622_, sizeof(void*)*3, v_code_3611_);
v___x_3620_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___x_3621_; 
v___x_3621_ = l_IO_FS_Stream_writeMessage(v_h_3607_, v___x_3620_);
return v___x_3621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object* v_inst_3634_, lean_object* v_h_3635_, lean_object* v_e_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3634_, v_h_3635_, v_e_3636_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData(lean_object* v_00_u03b1_3639_, lean_object* v_inst_3640_, lean_object* v_h_3641_, lean_object* v_e_3642_){
_start:
{
lean_object* v___x_3644_; 
v___x_3644_ = l_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3640_, v_h_3641_, v_e_3642_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object* v_00_u03b1_3645_, lean_object* v_inst_3646_, lean_object* v_h_3647_, lean_object* v_e_3648_, lean_object* v_a_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_IO_FS_Stream_writeResponseErrorWithData(v_00_u03b1_3645_, v_inst_3646_, v_h_3647_, v_e_3648_);
return v_res_3650_;
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
