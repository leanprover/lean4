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
uint8_t l_Lean_JsonRpc_instBEqRequestID_beq(lean_object* v_x_50_, lean_object* v_x_51_){
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
LEAN_EXPORT void l_Lean_JsonRpc_instBEqRequestID_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_50_ = stack[0].m_obj;
lean_object* v_x_51_ = stack[1].m_obj;
uint8_t v_res_62_;
v_res_62_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_x_50_, v_x_51_);
stack->m_num = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequestID_beq___boxed(lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_x_63_, v_x_64_);
lean_dec(v_x_64_);
lean_dec(v_x_63_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
uint64_t l_Lean_JsonRpc_instHashableRequestID_hash(lean_object* v_x_69_){
_start:
{
switch(lean_obj_tag(v_x_69_))
{
case 0:
{
lean_object* v_s_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; 
v_s_70_ = lean_ctor_get(v_x_69_, 0);
v___x_71_ = 0ULL;
v___x_72_ = lean_string_hash(v_s_70_);
v___x_73_ = lean_uint64_mix_hash(v___x_71_, v___x_72_);
return v___x_73_;
}
case 1:
{
lean_object* v_n_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; 
v_n_74_ = lean_ctor_get(v_x_69_, 0);
v___x_75_ = 1ULL;
v___x_76_ = l_Lean_instHashableJsonNumber_hash(v_n_74_);
v___x_77_ = lean_uint64_mix_hash(v___x_75_, v___x_76_);
return v___x_77_;
}
default: 
{
uint64_t v___x_78_; 
v___x_78_ = 2ULL;
return v___x_78_;
}
}
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instHashableRequestID_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_69_ = stack[0].m_obj;
uint64_t v_res_79_;
v_res_79_ = l_Lean_JsonRpc_instHashableRequestID_hash(v_x_69_);
stack->m_num = v_res_79_;
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
uint8_t l_Lean_JsonRpc_instOrdRequestID_ord(lean_object* v_x_85_, lean_object* v_x_86_){
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
LEAN_EXPORT void l_Lean_JsonRpc_instOrdRequestID_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_85_ = stack[0].m_obj;
lean_object* v_x_86_ = stack[1].m_obj;
uint8_t v_res_102_;
v_res_102_ = l_Lean_JsonRpc_instOrdRequestID_ord(v_x_85_, v_x_86_);
stack->m_num = v_res_102_;
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
lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___impl(uint8_t v_x_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_box(v_x_124_);
v___x_126_ = lean_obj_tag_nat(v___x_125_);
lean_dec(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_124_ = stack[0].m_num;
lean_object* v_res_127_;
v_res_127_ = l_Lean_JsonRpc_ErrorCode_ctorIdx___impl(v_x_124_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorIdx___impl___boxed(lean_object* v_x_128_){
_start:
{
uint8_t v_x_4__boxed_129_; lean_object* v_res_130_; 
v_x_4__boxed_129_ = lean_unbox(v_x_128_);
v_res_130_ = l_Lean_JsonRpc_ErrorCode_ctorIdx___impl(v_x_4__boxed_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(lean_object* v_k_131_){
_start:
{
lean_inc(v_k_131_);
return v_k_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___redArg___boxed(lean_object* v_k_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_JsonRpc_ErrorCode_ctorElim___redArg(v_k_132_);
lean_dec(v_k_132_);
return v_res_133_;
}
}
lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim(lean_object* v_motive_134_, lean_object* v_ctorIdx_135_, uint8_t v_t_136_, lean_object* v_h_137_, lean_object* v_k_138_){
_start:
{
lean_inc(v_k_138_);
return v_k_138_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_135_ = stack[1].m_obj;
uint8_t v_t_136_ = stack[2].m_num;
lean_object* v_k_138_ = stack[4].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_JsonRpc_ErrorCode_ctorElim(lean_box(0), v_ctorIdx_135_, v_t_136_, lean_box(0), v_k_138_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_ctorElim___boxed(lean_object* v_motive_140_, lean_object* v_ctorIdx_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_k_144_){
_start:
{
uint8_t v_t_boxed_145_; lean_object* v_res_146_; 
v_t_boxed_145_ = lean_unbox(v_t_142_);
v_res_146_ = l_Lean_JsonRpc_ErrorCode_ctorElim(v_motive_140_, v_ctorIdx_141_, v_t_boxed_145_, v_h_143_, v_k_144_);
lean_dec(v_k_144_);
lean_dec(v_ctorIdx_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(lean_object* v_parseError_147_){
_start:
{
lean_inc(v_parseError_147_);
return v_parseError_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg___boxed(lean_object* v_parseError_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_JsonRpc_ErrorCode_parseError_elim___redArg(v_parseError_148_);
lean_dec(v_parseError_148_);
return v_res_149_;
}
}
lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_object* v_motive_150_, uint8_t v_t_151_, lean_object* v_h_152_, lean_object* v_parseError_153_){
_start:
{
lean_inc(v_parseError_153_);
return v_parseError_153_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_parseError_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_151_ = stack[1].m_num;
lean_object* v_parseError_153_ = stack[3].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_JsonRpc_ErrorCode_parseError_elim(lean_box(0), v_t_151_, lean_box(0), v_parseError_153_);
stack->m_obj
 = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_parseError_elim___boxed(lean_object* v_motive_155_, lean_object* v_t_156_, lean_object* v_h_157_, lean_object* v_parseError_158_){
_start:
{
uint8_t v_t_boxed_159_; lean_object* v_res_160_; 
v_t_boxed_159_ = lean_unbox(v_t_156_);
v_res_160_ = l_Lean_JsonRpc_ErrorCode_parseError_elim(v_motive_155_, v_t_boxed_159_, v_h_157_, v_parseError_158_);
lean_dec(v_parseError_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(lean_object* v_invalidRequest_161_){
_start:
{
lean_inc(v_invalidRequest_161_);
return v_invalidRequest_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg___boxed(lean_object* v_invalidRequest_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___redArg(v_invalidRequest_162_);
lean_dec(v_invalidRequest_162_);
return v_res_163_;
}
}
lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_object* v_motive_164_, uint8_t v_t_165_, lean_object* v_h_166_, lean_object* v_invalidRequest_167_){
_start:
{
lean_inc(v_invalidRequest_167_);
return v_invalidRequest_167_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_invalidRequest_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_165_ = stack[1].m_num;
lean_object* v_invalidRequest_167_ = stack[3].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(lean_box(0), v_t_165_, lean_box(0), v_invalidRequest_167_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidRequest_elim___boxed(lean_object* v_motive_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_invalidRequest_172_){
_start:
{
uint8_t v_t_boxed_173_; lean_object* v_res_174_; 
v_t_boxed_173_ = lean_unbox(v_t_170_);
v_res_174_ = l_Lean_JsonRpc_ErrorCode_invalidRequest_elim(v_motive_169_, v_t_boxed_173_, v_h_171_, v_invalidRequest_172_);
lean_dec(v_invalidRequest_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(lean_object* v_methodNotFound_175_){
_start:
{
lean_inc(v_methodNotFound_175_);
return v_methodNotFound_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg___boxed(lean_object* v_methodNotFound_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___redArg(v_methodNotFound_176_);
lean_dec(v_methodNotFound_176_);
return v_res_177_;
}
}
lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(lean_object* v_motive_178_, uint8_t v_t_179_, lean_object* v_h_180_, lean_object* v_methodNotFound_181_){
_start:
{
lean_inc(v_methodNotFound_181_);
return v_methodNotFound_181_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_methodNotFound_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_179_ = stack[1].m_num;
lean_object* v_methodNotFound_181_ = stack[3].m_obj;
lean_object* v_res_182_;
v_res_182_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(lean_box(0), v_t_179_, lean_box(0), v_methodNotFound_181_);
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_methodNotFound_elim___boxed(lean_object* v_motive_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_methodNotFound_186_){
_start:
{
uint8_t v_t_boxed_187_; lean_object* v_res_188_; 
v_t_boxed_187_ = lean_unbox(v_t_184_);
v_res_188_ = l_Lean_JsonRpc_ErrorCode_methodNotFound_elim(v_motive_183_, v_t_boxed_187_, v_h_185_, v_methodNotFound_186_);
lean_dec(v_methodNotFound_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(lean_object* v_invalidParams_189_){
_start:
{
lean_inc(v_invalidParams_189_);
return v_invalidParams_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg___boxed(lean_object* v_invalidParams_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim___redArg(v_invalidParams_190_);
lean_dec(v_invalidParams_190_);
return v_res_191_;
}
}
lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_object* v_motive_192_, uint8_t v_t_193_, lean_object* v_h_194_, lean_object* v_invalidParams_195_){
_start:
{
lean_inc(v_invalidParams_195_);
return v_invalidParams_195_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_invalidParams_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_193_ = stack[1].m_num;
lean_object* v_invalidParams_195_ = stack[3].m_obj;
lean_object* v_res_196_;
v_res_196_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim(lean_box(0), v_t_193_, lean_box(0), v_invalidParams_195_);
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_invalidParams_elim___boxed(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_invalidParams_200_){
_start:
{
uint8_t v_t_boxed_201_; lean_object* v_res_202_; 
v_t_boxed_201_ = lean_unbox(v_t_198_);
v_res_202_ = l_Lean_JsonRpc_ErrorCode_invalidParams_elim(v_motive_197_, v_t_boxed_201_, v_h_199_, v_invalidParams_200_);
lean_dec(v_invalidParams_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(lean_object* v_internalError_203_){
_start:
{
lean_inc(v_internalError_203_);
return v_internalError_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg___boxed(lean_object* v_internalError_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_JsonRpc_ErrorCode_internalError_elim___redArg(v_internalError_204_);
lean_dec(v_internalError_204_);
return v_res_205_;
}
}
lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_object* v_motive_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_internalError_209_){
_start:
{
lean_inc(v_internalError_209_);
return v_internalError_209_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_internalError_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_207_ = stack[1].m_num;
lean_object* v_internalError_209_ = stack[3].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_JsonRpc_ErrorCode_internalError_elim(lean_box(0), v_t_207_, lean_box(0), v_internalError_209_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_internalError_elim___boxed(lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_internalError_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Lean_JsonRpc_ErrorCode_internalError_elim(v_motive_211_, v_t_boxed_215_, v_h_213_, v_internalError_214_);
lean_dec(v_internalError_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(lean_object* v_serverNotInitialized_217_){
_start:
{
lean_inc(v_serverNotInitialized_217_);
return v_serverNotInitialized_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg___boxed(lean_object* v_serverNotInitialized_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___redArg(v_serverNotInitialized_218_);
lean_dec(v_serverNotInitialized_218_);
return v_res_219_;
}
}
lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_object* v_motive_220_, uint8_t v_t_221_, lean_object* v_h_222_, lean_object* v_serverNotInitialized_223_){
_start:
{
lean_inc(v_serverNotInitialized_223_);
return v_serverNotInitialized_223_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_221_ = stack[1].m_num;
lean_object* v_serverNotInitialized_223_ = stack[3].m_obj;
lean_object* v_res_224_;
v_res_224_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(lean_box(0), v_t_221_, lean_box(0), v_serverNotInitialized_223_);
stack->m_obj
 = v_res_224_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim___boxed(lean_object* v_motive_225_, lean_object* v_t_226_, lean_object* v_h_227_, lean_object* v_serverNotInitialized_228_){
_start:
{
uint8_t v_t_boxed_229_; lean_object* v_res_230_; 
v_t_boxed_229_ = lean_unbox(v_t_226_);
v_res_230_ = l_Lean_JsonRpc_ErrorCode_serverNotInitialized_elim(v_motive_225_, v_t_boxed_229_, v_h_227_, v_serverNotInitialized_228_);
lean_dec(v_serverNotInitialized_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(lean_object* v_unknownErrorCode_231_){
_start:
{
lean_inc(v_unknownErrorCode_231_);
return v_unknownErrorCode_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg___boxed(lean_object* v_unknownErrorCode_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim___redArg(v_unknownErrorCode_232_);
lean_dec(v_unknownErrorCode_232_);
return v_res_233_;
}
}
lean_object* l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_object* v_motive_234_, uint8_t v_t_235_, lean_object* v_h_236_, lean_object* v_unknownErrorCode_237_){
_start:
{
lean_inc(v_unknownErrorCode_237_);
return v_unknownErrorCode_237_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_235_ = stack[1].m_num;
lean_object* v_unknownErrorCode_237_ = stack[3].m_obj;
lean_object* v_res_238_;
v_res_238_ = l_Lean_JsonRpc_ErrorCode_unknownErrorCode_elim(lean_box(0), v_t_235_, lean_box(0), v_unknownErrorCode_237_);
stack->m_obj
 = v_res_238_;
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
lean_object* l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_object* v_motive_248_, uint8_t v_t_249_, lean_object* v_h_250_, lean_object* v_contentModified_251_){
_start:
{
lean_inc(v_contentModified_251_);
return v_contentModified_251_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_contentModified_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_249_ = stack[1].m_num;
lean_object* v_contentModified_251_ = stack[3].m_obj;
lean_object* v_res_252_;
v_res_252_ = l_Lean_JsonRpc_ErrorCode_contentModified_elim(lean_box(0), v_t_249_, lean_box(0), v_contentModified_251_);
stack->m_obj
 = v_res_252_;
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
lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_object* v_motive_262_, uint8_t v_t_263_, lean_object* v_h_264_, lean_object* v_requestCancelled_265_){
_start:
{
lean_inc(v_requestCancelled_265_);
return v_requestCancelled_265_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_requestCancelled_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_263_ = stack[1].m_num;
lean_object* v_requestCancelled_265_ = stack[3].m_obj;
lean_object* v_res_266_;
v_res_266_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(lean_box(0), v_t_263_, lean_box(0), v_requestCancelled_265_);
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_requestCancelled_elim___boxed(lean_object* v_motive_267_, lean_object* v_t_268_, lean_object* v_h_269_, lean_object* v_requestCancelled_270_){
_start:
{
uint8_t v_t_boxed_271_; lean_object* v_res_272_; 
v_t_boxed_271_ = lean_unbox(v_t_268_);
v_res_272_ = l_Lean_JsonRpc_ErrorCode_requestCancelled_elim(v_motive_267_, v_t_boxed_271_, v_h_269_, v_requestCancelled_270_);
lean_dec(v_requestCancelled_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(lean_object* v_rpcNeedsReconnect_273_){
_start:
{
lean_inc(v_rpcNeedsReconnect_273_);
return v_rpcNeedsReconnect_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg___boxed(lean_object* v_rpcNeedsReconnect_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___redArg(v_rpcNeedsReconnect_274_);
lean_dec(v_rpcNeedsReconnect_274_);
return v_res_275_;
}
}
lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(lean_object* v_motive_276_, uint8_t v_t_277_, lean_object* v_h_278_, lean_object* v_rpcNeedsReconnect_279_){
_start:
{
lean_inc(v_rpcNeedsReconnect_279_);
return v_rpcNeedsReconnect_279_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_277_ = stack[1].m_num;
lean_object* v_rpcNeedsReconnect_279_ = stack[3].m_obj;
lean_object* v_res_280_;
v_res_280_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(lean_box(0), v_t_277_, lean_box(0), v_rpcNeedsReconnect_279_);
stack->m_obj
 = v_res_280_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim___boxed(lean_object* v_motive_281_, lean_object* v_t_282_, lean_object* v_h_283_, lean_object* v_rpcNeedsReconnect_284_){
_start:
{
uint8_t v_t_boxed_285_; lean_object* v_res_286_; 
v_t_boxed_285_ = lean_unbox(v_t_282_);
v_res_286_ = l_Lean_JsonRpc_ErrorCode_rpcNeedsReconnect_elim(v_motive_281_, v_t_boxed_285_, v_h_283_, v_rpcNeedsReconnect_284_);
lean_dec(v_rpcNeedsReconnect_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(lean_object* v_workerExited_287_){
_start:
{
lean_inc(v_workerExited_287_);
return v_workerExited_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg___boxed(lean_object* v_workerExited_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim___redArg(v_workerExited_288_);
lean_dec(v_workerExited_288_);
return v_res_289_;
}
}
lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim(lean_object* v_motive_290_, uint8_t v_t_291_, lean_object* v_h_292_, lean_object* v_workerExited_293_){
_start:
{
lean_inc(v_workerExited_293_);
return v_workerExited_293_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_workerExited_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_291_ = stack[1].m_num;
lean_object* v_workerExited_293_ = stack[3].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim(lean_box(0), v_t_291_, lean_box(0), v_workerExited_293_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerExited_elim___boxed(lean_object* v_motive_295_, lean_object* v_t_296_, lean_object* v_h_297_, lean_object* v_workerExited_298_){
_start:
{
uint8_t v_t_boxed_299_; lean_object* v_res_300_; 
v_t_boxed_299_ = lean_unbox(v_t_296_);
v_res_300_ = l_Lean_JsonRpc_ErrorCode_workerExited_elim(v_motive_295_, v_t_boxed_299_, v_h_297_, v_workerExited_298_);
lean_dec(v_workerExited_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(lean_object* v_workerCrashed_301_){
_start:
{
lean_inc(v_workerCrashed_301_);
return v_workerCrashed_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg___boxed(lean_object* v_workerCrashed_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___redArg(v_workerCrashed_302_);
lean_dec(v_workerCrashed_302_);
return v_res_303_;
}
}
lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_object* v_motive_304_, uint8_t v_t_305_, lean_object* v_h_306_, lean_object* v_workerCrashed_307_){
_start:
{
lean_inc(v_workerCrashed_307_);
return v_workerCrashed_307_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_ErrorCode_workerCrashed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_305_ = stack[1].m_num;
lean_object* v_workerCrashed_307_ = stack[3].m_obj;
lean_object* v_res_308_;
v_res_308_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(lean_box(0), v_t_305_, lean_box(0), v_workerCrashed_307_);
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ErrorCode_workerCrashed_elim___boxed(lean_object* v_motive_309_, lean_object* v_t_310_, lean_object* v_h_311_, lean_object* v_workerCrashed_312_){
_start:
{
uint8_t v_t_boxed_313_; lean_object* v_res_314_; 
v_t_boxed_313_ = lean_unbox(v_t_310_);
v_res_314_ = l_Lean_JsonRpc_ErrorCode_workerCrashed_elim(v_motive_309_, v_t_boxed_313_, v_h_311_, v_workerCrashed_312_);
lean_dec(v_workerCrashed_312_);
return v_res_314_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode_default(void){
_start:
{
uint8_t v___x_315_; 
v___x_315_ = 0;
return v___x_315_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedErrorCode(void){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
}
uint8_t l_Lean_JsonRpc_instBEqErrorCode_beq(uint8_t v_x_317_, uint8_t v_y_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_319_ = lean_box(v_x_317_);
v___x_320_ = lean_obj_tag_nat(v___x_319_);
lean_dec(v___x_319_);
v___x_321_ = lean_box(v_y_318_);
v___x_322_ = lean_obj_tag_nat(v___x_321_);
lean_dec(v___x_321_);
v___x_323_ = lean_nat_dec_eq(v___x_320_, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instBEqErrorCode_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_317_ = stack[0].m_num;
uint8_t v_y_318_ = stack[1].m_num;
uint8_t v_res_324_;
v_res_324_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_x_317_, v_y_318_);
stack->m_num = v_res_324_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqErrorCode_beq___boxed(lean_object* v_x_325_, lean_object* v_y_326_){
_start:
{
uint8_t v_x_24__boxed_327_; uint8_t v_y_25__boxed_328_; uint8_t v_res_329_; lean_object* v_r_330_; 
v_x_24__boxed_327_ = lean_unbox(v_x_325_);
v_y_25__boxed_328_ = lean_unbox(v_y_326_);
v_res_329_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_x_24__boxed_327_, v_y_25__boxed_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_unsigned_to_nat(32700u);
v___x_337_ = lean_nat_to_int(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__2);
v___x_339_ = lean_int_neg(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(32600u);
v___x_341_ = lean_nat_to_int(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__4);
v___x_343_ = lean_int_neg(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(32601u);
v___x_345_ = lean_nat_to_int(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__6);
v___x_347_ = lean_int_neg(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(32602u);
v___x_349_ = lean_nat_to_int(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__8);
v___x_351_ = lean_int_neg(v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(32603u);
v___x_353_ = lean_nat_to_int(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__10);
v___x_355_ = lean_int_neg(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_unsigned_to_nat(32002u);
v___x_357_ = lean_nat_to_int(v___x_356_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__12);
v___x_359_ = lean_int_neg(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(32001u);
v___x_361_ = lean_nat_to_int(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__14);
v___x_363_ = lean_int_neg(v___x_362_);
return v___x_363_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_unsigned_to_nat(32801u);
v___x_365_ = lean_nat_to_int(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__16);
v___x_367_ = lean_int_neg(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(32800u);
v___x_369_ = lean_nat_to_int(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__18);
v___x_371_ = lean_int_neg(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_unsigned_to_nat(32900u);
v___x_373_ = lean_nat_to_int(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__20);
v___x_375_ = lean_int_neg(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(32901u);
v___x_377_ = lean_nat_to_int(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__22);
v___x_379_ = lean_int_neg(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_unsigned_to_nat(32902u);
v___x_381_ = lean_nat_to_int(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__24);
v___x_383_ = lean_int_neg(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_420_) == 2)
{
lean_object* v_n_423_; lean_object* v_mantissa_424_; lean_object* v_exponent_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_n_423_ = lean_ctor_get(v_x_420_, 0);
v_mantissa_424_ = lean_ctor_get(v_n_423_, 0);
v_exponent_425_ = lean_ctor_get(v_n_423_, 1);
v___x_426_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_427_ = lean_int_dec_eq(v_mantissa_424_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_429_ = lean_int_dec_eq(v_mantissa_424_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_431_ = lean_int_dec_eq(v_mantissa_424_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_433_ = lean_int_dec_eq(v_mantissa_424_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_435_ = lean_int_dec_eq(v_mantissa_424_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_437_ = lean_int_dec_eq(v_mantissa_424_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_439_ = lean_int_dec_eq(v_mantissa_424_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_441_ = lean_int_dec_eq(v_mantissa_424_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_443_ = lean_int_dec_eq(v_mantissa_424_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_445_ = lean_int_dec_eq(v_mantissa_424_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_447_ = lean_int_dec_eq(v_mantissa_424_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_449_ = lean_int_dec_eq(v_mantissa_424_, v___x_448_);
if (v___x_449_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_nat_dec_eq(v_exponent_425_, v___x_450_);
if (v___x_451_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_452_; 
v___x_452_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_452_;
}
}
}
else
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_nat_dec_eq(v_exponent_425_, v___x_453_);
if (v___x_454_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_455_; 
v___x_455_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_455_;
}
}
}
else
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_nat_dec_eq(v_exponent_425_, v___x_456_);
if (v___x_457_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_458_;
}
}
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_nat_dec_eq(v_exponent_425_, v___x_459_);
if (v___x_460_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_461_;
}
}
}
else
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_nat_dec_eq(v_exponent_425_, v___x_462_);
if (v___x_463_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_464_; 
v___x_464_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_464_;
}
}
}
else
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_nat_dec_eq(v_exponent_425_, v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_467_; 
v___x_467_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_467_;
}
}
}
else
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_nat_dec_eq(v_exponent_425_, v___x_468_);
if (v___x_469_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_470_; 
v___x_470_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_470_;
}
}
}
else
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_nat_dec_eq(v_exponent_425_, v___x_471_);
if (v___x_472_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_473_;
}
}
}
else
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_nat_dec_eq(v_exponent_425_, v___x_474_);
if (v___x_475_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_476_; 
v___x_476_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_476_;
}
}
}
else
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_nat_dec_eq(v_exponent_425_, v___x_477_);
if (v___x_478_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_479_; 
v___x_479_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_479_;
}
}
}
else
{
lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_nat_dec_eq(v_exponent_425_, v___x_480_);
if (v___x_481_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_482_;
}
}
}
else
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_nat_dec_eq(v_exponent_425_, v___x_483_);
if (v___x_484_ == 0)
{
goto v___jp_421_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_485_;
}
}
}
else
{
goto v___jp_421_;
}
v___jp_421_:
{
lean_object* v___x_422_; 
v___x_422_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___boxed(lean_object* v_x_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_JsonRpc_instFromJsonErrorCode___lam__0(v_x_486_);
lean_dec(v_x_486_);
return v_res_487_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_491_ = l_Lean_JsonNumber_fromInt(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__0);
v___x_493_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_495_ = l_Lean_JsonNumber_fromInt(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__2);
v___x_497_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_499_ = l_Lean_JsonNumber_fromInt(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__4);
v___x_501_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_503_ = l_Lean_JsonNumber_fromInt(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__6);
v___x_505_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_507_ = l_Lean_JsonNumber_fromInt(v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__8);
v___x_509_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_511_ = l_Lean_JsonNumber_fromInt(v___x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__10);
v___x_513_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_515_ = l_Lean_JsonNumber_fromInt(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__12);
v___x_517_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_519_ = l_Lean_JsonNumber_fromInt(v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__14);
v___x_521_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_523_ = l_Lean_JsonNumber_fromInt(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__16);
v___x_525_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_527_ = l_Lean_JsonNumber_fromInt(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__18);
v___x_529_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_531_ = l_Lean_JsonNumber_fromInt(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__20);
v___x_533_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_535_ = l_Lean_JsonNumber_fromInt(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__22);
v___x_537_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0(uint8_t v_x_538_){
_start:
{
switch(v_x_538_)
{
case 0:
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
return v___x_539_;
}
case 1:
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
return v___x_540_;
}
case 2:
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
return v___x_541_;
}
case 3:
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
return v___x_542_;
}
case 4:
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
return v___x_543_;
}
case 5:
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
return v___x_544_;
}
case 6:
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
return v___x_545_;
}
case 7:
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
return v___x_546_;
}
case 8:
{
lean_object* v___x_547_; 
v___x_547_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
return v___x_547_;
}
case 9:
{
lean_object* v___x_548_; 
v___x_548_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
return v___x_548_;
}
case 10:
{
lean_object* v___x_549_; 
v___x_549_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
return v___x_549_;
}
default: 
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
return v___x_550_;
}
}
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instToJsonErrorCode___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_538_ = stack[0].m_num;
lean_object* v_res_551_;
v_res_551_ = l_Lean_JsonRpc_instToJsonErrorCode___lam__0(v_x_538_);
stack->m_obj
 = v_res_551_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonErrorCode___lam__0___boxed(lean_object* v_x_552_){
_start:
{
uint8_t v_x_474__boxed_553_; lean_object* v_res_554_; 
v_x_474__boxed_553_ = lean_unbox(v_x_552_);
v_res_554_ = l_Lean_JsonRpc_instToJsonErrorCode___lam__0(v_x_474__boxed_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___impl(lean_object* v_x_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = lean_obj_tag_nat(v_x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_ctorIdx___impl___boxed(lean_object* v_x_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_JsonRpc_Message_ctorIdx___impl(v_x_559_);
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
uint8_t l_Lean_JsonRpc_instBEqRequest_beq___redArg(lean_object* v_inst_641_, lean_object* v_x_642_, lean_object* v_x_643_){
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
LEAN_EXPORT void l_Lean_JsonRpc_instBEqRequest_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_641_ = stack[0].m_obj;
lean_object* v_x_642_ = stack[1].m_obj;
lean_object* v_x_643_ = stack[2].m_obj;
uint8_t v_res_654_;
v_res_654_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_641_, v_x_642_, v_x_643_);
stack->m_num = v_res_654_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___redArg___boxed(lean_object* v_inst_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
uint8_t v_res_658_; lean_object* v_r_659_; 
v_res_658_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_655_, v_x_656_, v_x_657_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
uint8_t l_Lean_JsonRpc_instBEqRequest_beq(lean_object* v_00_u03b1_660_, lean_object* v_inst_661_, lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = l_Lean_JsonRpc_instBEqRequest_beq___redArg(v_inst_661_, v_x_662_, v_x_663_);
return v___x_664_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instBEqRequest_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_661_ = stack[1].m_obj;
lean_object* v_x_662_ = stack[2].m_obj;
lean_object* v_x_663_ = stack[3].m_obj;
uint8_t v_res_665_;
v_res_665_ = l_Lean_JsonRpc_instBEqRequest_beq(lean_box(0), v_inst_661_, v_x_662_, v_x_663_);
stack->m_num = v_res_665_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest_beq___boxed(lean_object* v_00_u03b1_666_, lean_object* v_inst_667_, lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Lean_JsonRpc_instBEqRequest_beq(v_00_u03b1_666_, v_inst_667_, v_x_668_, v_x_669_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest___redArg(lean_object* v_inst_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_673_, 0, lean_box(0));
lean_closure_set(v___x_673_, 1, v_inst_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqRequest(lean_object* v_00_u03b1_674_, lean_object* v_inst_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqRequest_beq___boxed), 4, 2);
lean_closure_set(v___x_676_, 0, lean_box(0));
lean_closure_set(v___x_676_, 1, v_inst_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0(lean_object* v_inst_677_, lean_object* v_r_678_){
_start:
{
lean_object* v_id_679_; lean_object* v_method_680_; lean_object* v_param_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_701_; 
v_id_679_ = lean_ctor_get(v_r_678_, 0);
v_method_680_ = lean_ctor_get(v_r_678_, 1);
v_param_681_ = lean_ctor_get(v_r_678_, 2);
v_isSharedCheck_701_ = !lean_is_exclusive(v_r_678_);
if (v_isSharedCheck_701_ == 0)
{
v___x_683_ = v_r_678_;
v_isShared_684_ = v_isSharedCheck_701_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_param_681_);
lean_inc(v_method_680_);
lean_inc(v_id_679_);
lean_dec(v_r_678_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_701_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_677_, v_param_681_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v___x_686_; lean_object* v___x_688_; 
lean_dec_ref_known(v___x_685_, 1);
v___x_686_ = lean_box(0);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 2, v___x_686_);
v___x_688_ = v___x_683_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_id_679_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_method_680_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_700_; 
v_a_690_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_700_ == 0)
{
v___x_692_ = v___x_685_;
v_isShared_693_ = v_isSharedCheck_700_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_685_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_700_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_699_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 2, v___x_695_);
v___x_697_ = v___x_683_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_id_679_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_method_680_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg(lean_object* v_inst_702_){
_start:
{
lean_object* v___f_703_; 
v___f_703_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_703_, 0, v_inst_702_);
return v___f_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson(lean_object* v_00_u03b1_704_, lean_object* v_inst_705_){
_start:
{
lean_object* v___f_706_; 
v___f_706_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutRequestMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_706_, 0, v_inst_705_);
return v___f_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(lean_object* v_x_707_){
_start:
{
if (lean_obj_tag(v_x_707_) == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_box(0);
return v___x_708_;
}
else
{
lean_object* v_val_709_; lean_object* v___x_710_; 
v_val_709_ = lean_ctor_get(v_x_707_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v_x_707_, 1);
v___x_710_ = l_Lean_Json_Structured_toJson(v_val_709_);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Request_ofMessage_x3f(lean_object* v_x_711_){
_start:
{
if (lean_obj_tag(v_x_711_) == 0)
{
lean_object* v_id_712_; lean_object* v_method_713_; lean_object* v_params_x3f_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_723_; 
v_id_712_ = lean_ctor_get(v_x_711_, 0);
v_method_713_ = lean_ctor_get(v_x_711_, 1);
v_params_x3f_714_ = lean_ctor_get(v_x_711_, 2);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_711_);
if (v_isSharedCheck_723_ == 0)
{
v___x_716_ = v_x_711_;
v_isShared_717_ = v_isSharedCheck_723_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_params_x3f_714_);
lean_inc(v_method_713_);
lean_inc(v_id_712_);
lean_dec(v_x_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_723_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_714_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 2, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_id_712_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_method_713_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v___x_718_);
v___x_720_ = v_reuseFailAlloc_722_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; 
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
}
else
{
lean_object* v___x_724_; 
lean_dec_ref(v_x_711_);
v___x_724_ = lean_box(0);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default___redArg(lean_object* v_inst_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v_inst_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification_default(lean_object* v_00_u03b1_728_, lean_object* v_inst_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification___redArg(lean_object* v_inst_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedNotification(lean_object* v_a_733_, lean_object* v_inst_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_JsonRpc_instInhabitedNotification_default___redArg(v_inst_734_);
return v___x_735_;
}
}
uint8_t l_Lean_JsonRpc_instBEqNotification_beq___redArg(lean_object* v_inst_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
lean_object* v_method_739_; lean_object* v_param_740_; lean_object* v_method_741_; lean_object* v_param_742_; uint8_t v___x_743_; 
v_method_739_ = lean_ctor_get(v_x_737_, 0);
lean_inc_ref(v_method_739_);
v_param_740_ = lean_ctor_get(v_x_737_, 1);
lean_inc(v_param_740_);
lean_dec_ref(v_x_737_);
v_method_741_ = lean_ctor_get(v_x_738_, 0);
lean_inc_ref(v_method_741_);
v_param_742_ = lean_ctor_get(v_x_738_, 1);
lean_inc(v_param_742_);
lean_dec_ref(v_x_738_);
v___x_743_ = lean_string_dec_eq(v_method_739_, v_method_741_);
lean_dec_ref(v_method_741_);
lean_dec_ref(v_method_739_);
if (v___x_743_ == 0)
{
lean_dec(v_param_742_);
lean_dec(v_param_740_);
lean_dec_ref(v_inst_736_);
return v___x_743_;
}
else
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_apply_2(v_inst_736_, v_param_740_, v_param_742_);
v___x_745_ = lean_unbox(v___x_744_);
return v___x_745_;
}
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instBEqNotification_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_736_ = stack[0].m_obj;
lean_object* v_x_737_ = stack[1].m_obj;
lean_object* v_x_738_ = stack[2].m_obj;
uint8_t v_res_746_;
v_res_746_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_736_, v_x_737_, v_x_738_);
stack->m_num = v_res_746_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqNotification_beq___redArg___boxed(lean_object* v_inst_747_, lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_747_, v_x_748_, v_x_749_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
uint8_t l_Lean_JsonRpc_instBEqNotification_beq(lean_object* v_00_u03b1_752_, lean_object* v_inst_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = l_Lean_JsonRpc_instBEqNotification_beq___redArg(v_inst_753_, v_x_754_, v_x_755_);
return v___x_756_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instBEqNotification_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_753_ = stack[1].m_obj;
lean_object* v_x_754_ = stack[2].m_obj;
lean_object* v_x_755_ = stack[3].m_obj;
uint8_t v_res_757_;
v_res_757_ = l_Lean_JsonRpc_instBEqNotification_beq(lean_box(0), v_inst_753_, v_x_754_, v_x_755_);
stack->m_num = v_res_757_;
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
lean_dec_ref_known(v___x_776_, 1);
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
v___x_804_ = l_Lean_Option_toJson___at___00Lean_JsonRpc_Request_ofMessage_x3f_spec__0(v_params_x3f_800_);
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
uint8_t l_Lean_JsonRpc_instBEqResponse_beq___redArg(lean_object* v_inst_822_, lean_object* v_x_823_, lean_object* v_x_824_){
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
LEAN_EXPORT void l_Lean_JsonRpc_instBEqResponse_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_822_ = stack[0].m_obj;
lean_object* v_x_823_ = stack[1].m_obj;
lean_object* v_x_824_ = stack[2].m_obj;
uint8_t v_res_832_;
v_res_832_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_822_, v_x_823_, v_x_824_);
stack->m_num = v_res_832_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___redArg___boxed(lean_object* v_inst_833_, lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_833_, v_x_834_, v_x_835_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
uint8_t l_Lean_JsonRpc_instBEqResponse_beq(lean_object* v_00_u03b1_838_, lean_object* v_inst_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
uint8_t v___x_842_; 
v___x_842_ = l_Lean_JsonRpc_instBEqResponse_beq___redArg(v_inst_839_, v_x_840_, v_x_841_);
return v___x_842_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instBEqResponse_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_839_ = stack[1].m_obj;
lean_object* v_x_840_ = stack[2].m_obj;
lean_object* v_x_841_ = stack[3].m_obj;
uint8_t v_res_843_;
v_res_843_ = l_Lean_JsonRpc_instBEqResponse_beq(lean_box(0), v_inst_839_, v_x_840_, v_x_841_);
stack->m_num = v_res_843_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse_beq___boxed(lean_object* v_00_u03b1_844_, lean_object* v_inst_845_, lean_object* v_x_846_, lean_object* v_x_847_){
_start:
{
uint8_t v_res_848_; lean_object* v_r_849_; 
v_res_848_ = l_Lean_JsonRpc_instBEqResponse_beq(v_00_u03b1_844_, v_inst_845_, v_x_846_, v_x_847_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse___redArg(lean_object* v_inst_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_851_, 0, lean_box(0));
lean_closure_set(v___x_851_, 1, v_inst_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponse(lean_object* v_00_u03b1_852_, lean_object* v_inst_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponse_beq___boxed), 4, 2);
lean_closure_set(v___x_854_, 0, lean_box(0));
lean_closure_set(v___x_854_, 1, v_inst_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0(lean_object* v_inst_855_, lean_object* v_r_856_){
_start:
{
lean_object* v_id_857_; lean_object* v_result_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_866_; 
v_id_857_ = lean_ctor_get(v_r_856_, 0);
v_result_858_ = lean_ctor_get(v_r_856_, 1);
v_isSharedCheck_866_ = !lean_is_exclusive(v_r_856_);
if (v_isSharedCheck_866_ == 0)
{
v___x_860_ = v_r_856_;
v_isShared_861_ = v_isSharedCheck_866_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_result_858_);
lean_inc(v_id_857_);
lean_dec(v_r_856_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_866_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_862_ = lean_apply_1(v_inst_855_, v_result_858_);
if (v_isShared_861_ == 0)
{
lean_ctor_set_tag(v___x_860_, 2);
lean_ctor_set(v___x_860_, 1, v___x_862_);
v___x_864_ = v___x_860_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_id_857_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg(lean_object* v_inst_867_){
_start:
{
lean_object* v___f_868_; 
v___f_868_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_868_, 0, v_inst_867_);
return v___f_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson(lean_object* v_00_u03b1_869_, lean_object* v_inst_870_){
_start:
{
lean_object* v___f_871_; 
v___f_871_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_871_, 0, v_inst_870_);
return v___f_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Response_ofMessage_x3f(lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_872_) == 2)
{
lean_object* v_id_873_; lean_object* v_result_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_882_; 
v_id_873_ = lean_ctor_get(v_x_872_, 0);
v_result_874_ = lean_ctor_get(v_x_872_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_x_872_);
if (v_isSharedCheck_882_ == 0)
{
v___x_876_ = v_x_872_;
v_isShared_877_ = v_isSharedCheck_882_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_result_874_);
lean_inc(v_id_873_);
lean_dec(v_x_872_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_882_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set_tag(v___x_876_, 0);
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_id_873_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_result_874_);
v___x_879_ = v_reuseFailAlloc_881_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; 
v___x_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
}
else
{
lean_object* v___x_883_; 
lean_dec_ref(v_x_872_);
v___x_883_ = lean_box(0);
return v___x_883_;
}
}
}
lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___redArg(){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___closed__0));
return v___x_890_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instInhabitedResponseError_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_891_;
v_res_891_ = l_Lean_JsonRpc_instInhabitedResponseError_default___redArg();
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default___redArg___boxed(lean_object* v___dummy_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_JsonRpc_instInhabitedResponseError_default___redArg();
return v_res_893_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0(void){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_JsonRpc_instInhabitedResponseError_default___redArg();
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError_default(lean_object* v_00_u03b1_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_896_;
}
}
lean_object* l_Lean_JsonRpc_instInhabitedResponseError___redArg(){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_898_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instInhabitedResponseError___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_899_;
v_res_899_ = l_Lean_JsonRpc_instInhabitedResponseError___redArg();
stack->m_obj
 = v_res_899_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError___redArg___boxed(lean_object* v___dummy_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_JsonRpc_instInhabitedResponseError___redArg();
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instInhabitedResponseError(lean_object* v_a_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = lean_obj_once(&l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0, &l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0_once, _init_l_Lean_JsonRpc_instInhabitedResponseError_default___closed__0);
return v___x_903_;
}
}
uint8_t l_Lean_JsonRpc_instBEqResponseError_beq___redArg(lean_object* v_inst_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
lean_object* v_id_907_; uint8_t v_code_908_; lean_object* v_message_909_; lean_object* v_data_x3f_910_; lean_object* v_id_911_; uint8_t v_code_912_; lean_object* v_message_913_; lean_object* v_data_x3f_914_; uint8_t v___x_915_; 
v_id_907_ = lean_ctor_get(v_x_905_, 0);
lean_inc(v_id_907_);
v_code_908_ = lean_ctor_get_uint8(v_x_905_, sizeof(void*)*3);
v_message_909_ = lean_ctor_get(v_x_905_, 1);
lean_inc_ref(v_message_909_);
v_data_x3f_910_ = lean_ctor_get(v_x_905_, 2);
lean_inc(v_data_x3f_910_);
lean_dec_ref(v_x_905_);
v_id_911_ = lean_ctor_get(v_x_906_, 0);
lean_inc(v_id_911_);
v_code_912_ = lean_ctor_get_uint8(v_x_906_, sizeof(void*)*3);
v_message_913_ = lean_ctor_get(v_x_906_, 1);
lean_inc_ref(v_message_913_);
v_data_x3f_914_ = lean_ctor_get(v_x_906_, 2);
lean_inc(v_data_x3f_914_);
lean_dec_ref(v_x_906_);
v___x_915_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_907_, v_id_911_);
lean_dec(v_id_911_);
lean_dec(v_id_907_);
if (v___x_915_ == 0)
{
lean_dec(v_data_x3f_914_);
lean_dec_ref(v_message_913_);
lean_dec(v_data_x3f_910_);
lean_dec_ref(v_message_909_);
lean_dec_ref(v_inst_904_);
return v___x_915_;
}
else
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_JsonRpc_instBEqErrorCode_beq(v_code_908_, v_code_912_);
if (v___x_916_ == 0)
{
lean_dec(v_data_x3f_914_);
lean_dec_ref(v_message_913_);
lean_dec(v_data_x3f_910_);
lean_dec_ref(v_message_909_);
lean_dec_ref(v_inst_904_);
return v___x_916_;
}
else
{
uint8_t v___x_917_; 
v___x_917_ = lean_string_dec_eq(v_message_909_, v_message_913_);
lean_dec_ref(v_message_913_);
lean_dec_ref(v_message_909_);
if (v___x_917_ == 0)
{
lean_dec(v_data_x3f_914_);
lean_dec(v_data_x3f_910_);
lean_dec_ref(v_inst_904_);
return v___x_917_;
}
else
{
uint8_t v___x_918_; 
v___x_918_ = l_instBEqOption_beq___redArg(v_inst_904_, v_data_x3f_910_, v_data_x3f_914_);
return v___x_918_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instBEqResponseError_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_904_ = stack[0].m_obj;
lean_object* v_x_905_ = stack[1].m_obj;
lean_object* v_x_906_ = stack[2].m_obj;
uint8_t v_res_919_;
v_res_919_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_904_, v_x_905_, v_x_906_);
stack->m_num = v_res_919_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___redArg___boxed(lean_object* v_inst_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
uint8_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_920_, v_x_921_, v_x_922_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
uint8_t l_Lean_JsonRpc_instBEqResponseError_beq(lean_object* v_00_u03b1_925_, lean_object* v_inst_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
uint8_t v___x_929_; 
v___x_929_ = l_Lean_JsonRpc_instBEqResponseError_beq___redArg(v_inst_926_, v_x_927_, v_x_928_);
return v___x_929_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instBEqResponseError_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_926_ = stack[1].m_obj;
lean_object* v_x_927_ = stack[2].m_obj;
lean_object* v_x_928_ = stack[3].m_obj;
uint8_t v_res_930_;
v_res_930_ = l_Lean_JsonRpc_instBEqResponseError_beq(lean_box(0), v_inst_926_, v_x_927_, v_x_928_);
stack->m_num = v_res_930_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError_beq___boxed(lean_object* v_00_u03b1_931_, lean_object* v_inst_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
uint8_t v_res_935_; lean_object* v_r_936_; 
v_res_935_ = l_Lean_JsonRpc_instBEqResponseError_beq(v_00_u03b1_931_, v_inst_932_, v_x_933_, v_x_934_);
v_r_936_ = lean_box(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError___redArg(lean_object* v_inst_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_938_, 0, lean_box(0));
lean_closure_set(v___x_938_, 1, v_inst_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instBEqResponseError(lean_object* v_00_u03b1_939_, lean_object* v_inst_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instBEqResponseError_beq___boxed), 4, 2);
lean_closure_set(v___x_941_, 0, lean_box(0));
lean_closure_set(v___x_941_, 1, v_inst_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0(lean_object* v_inst_942_, lean_object* v_r_943_){
_start:
{
lean_object* v_data_x3f_944_; 
v_data_x3f_944_ = lean_ctor_get(v_r_943_, 2);
lean_inc(v_data_x3f_944_);
if (lean_obj_tag(v_data_x3f_944_) == 0)
{
lean_object* v_id_945_; uint8_t v_code_946_; lean_object* v_message_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v_inst_942_);
v_id_945_ = lean_ctor_get(v_r_943_, 0);
v_code_946_ = lean_ctor_get_uint8(v_r_943_, sizeof(void*)*3);
v_message_947_ = lean_ctor_get(v_r_943_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v_r_943_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v_r_943_, 2);
lean_dec(v_unused_956_);
v___x_949_ = v_r_943_;
v_isShared_950_ = v_isSharedCheck_955_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_message_947_);
lean_inc(v_id_945_);
lean_dec(v_r_943_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_955_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_box(0);
if (v_isShared_950_ == 0)
{
lean_ctor_set_tag(v___x_949_, 3);
lean_ctor_set(v___x_949_, 2, v___x_951_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_id_945_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_message_947_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v___x_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3, v_code_946_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
else
{
lean_object* v_id_957_; uint8_t v_code_958_; lean_object* v_message_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_975_; 
v_id_957_ = lean_ctor_get(v_r_943_, 0);
v_code_958_ = lean_ctor_get_uint8(v_r_943_, sizeof(void*)*3);
v_message_959_ = lean_ctor_get(v_r_943_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_r_943_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v_r_943_, 2);
lean_dec(v_unused_976_);
v___x_961_ = v_r_943_;
v_isShared_962_ = v_isSharedCheck_975_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_message_959_);
lean_inc(v_id_957_);
lean_dec(v_r_943_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_975_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_val_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_974_; 
v_val_963_ = lean_ctor_get(v_data_x3f_944_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v_data_x3f_944_);
if (v_isSharedCheck_974_ == 0)
{
v___x_965_ = v_data_x3f_944_;
v_isShared_966_ = v_isSharedCheck_974_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_val_963_);
lean_dec(v_data_x3f_944_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_974_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = lean_apply_1(v_inst_942_, v_val_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_967_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_973_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 3);
lean_ctor_set(v___x_961_, 2, v___x_969_);
v___x_971_ = v___x_961_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_id_957_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_message_959_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v___x_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3, v_code_958_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg(lean_object* v_inst_977_){
_start:
{
lean_object* v___f_978_; 
v___f_978_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_978_, 0, v_inst_977_);
return v___f_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson(lean_object* v_00_u03b1_979_, lean_object* v_inst_980_){
_start:
{
lean_object* v___f_981_; 
v___f_981_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instCoeOutResponseErrorMessageOfToJson___redArg___lam__0), 2, 1);
lean_closure_set(v___f_981_, 0, v_inst_980_);
return v___f_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeOutResponseErrorUnitMessage___lam__0(lean_object* v_r_982_){
_start:
{
lean_object* v_id_983_; uint8_t v_code_984_; lean_object* v_message_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v_id_983_ = lean_ctor_get(v_r_982_, 0);
v_code_984_ = lean_ctor_get_uint8(v_r_982_, sizeof(void*)*3);
v_message_985_ = lean_ctor_get(v_r_982_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_r_982_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v_r_982_, 2);
lean_dec(v_unused_994_);
v___x_987_ = v_r_982_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_message_985_);
lean_inc(v_id_983_);
lean_dec(v_r_982_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_box(0);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 3);
lean_ctor_set(v___x_987_, 2, v___x_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_id_983_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_message_985_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v___x_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_992_, sizeof(void*)*3, v_code_984_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_ResponseError_ofMessage_x3f(lean_object* v_x_997_){
_start:
{
if (lean_obj_tag(v_x_997_) == 3)
{
lean_object* v_id_998_; uint8_t v_code_999_; lean_object* v_message_1000_; lean_object* v_data_x3f_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1009_; 
v_id_998_ = lean_ctor_get(v_x_997_, 0);
v_code_999_ = lean_ctor_get_uint8(v_x_997_, sizeof(void*)*3);
v_message_1000_ = lean_ctor_get(v_x_997_, 1);
v_data_x3f_1001_ = lean_ctor_get(v_x_997_, 2);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_x_997_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1003_ = v_x_997_;
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_data_x3f_1001_);
lean_inc(v_message_1000_);
lean_inc(v_id_998_);
lean_dec(v_x_997_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set_tag(v___x_1003_, 0);
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_id_998_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_message_1000_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_data_x3f_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1008_, sizeof(void*)*3, v_code_999_);
v___x_1006_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
}
else
{
lean_object* v___x_1010_; 
lean_dec_ref(v_x_997_);
v___x_1010_ = lean_box(0);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeStringRequestID___lam__0(lean_object* v_s_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_s_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instCoeJsonNumberRequestID___lam__0(lean_object* v_n_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_n_1015_);
return v___x_1016_;
}
}
uint8_t l_Lean_JsonRpc_RequestID_lt(lean_object* v_x_1019_, lean_object* v_x_1020_){
_start:
{
switch(lean_obj_tag(v_x_1019_))
{
case 0:
{
if (lean_obj_tag(v_x_1020_) == 0)
{
lean_object* v_s_1021_; lean_object* v_s_1022_; uint8_t v___x_1023_; 
v_s_1021_ = lean_ctor_get(v_x_1019_, 0);
lean_inc_ref(v_s_1021_);
lean_dec_ref_known(v_x_1019_, 1);
v_s_1022_ = lean_ctor_get(v_x_1020_, 0);
lean_inc_ref(v_s_1022_);
lean_dec_ref_known(v_x_1020_, 1);
v___x_1023_ = lean_string_dec_lt(v_s_1021_, v_s_1022_);
lean_dec_ref(v_s_1022_);
lean_dec_ref(v_s_1021_);
return v___x_1023_;
}
else
{
uint8_t v___x_1024_; 
lean_dec_ref_known(v_x_1019_, 1);
lean_dec(v_x_1020_);
v___x_1024_ = 0;
return v___x_1024_;
}
}
case 1:
{
switch(lean_obj_tag(v_x_1020_))
{
case 1:
{
lean_object* v_n_1025_; lean_object* v_n_1026_; uint8_t v___x_1027_; 
v_n_1025_ = lean_ctor_get(v_x_1019_, 0);
lean_inc_ref(v_n_1025_);
lean_dec_ref_known(v_x_1019_, 1);
v_n_1026_ = lean_ctor_get(v_x_1020_, 0);
lean_inc_ref(v_n_1026_);
lean_dec_ref_known(v_x_1020_, 1);
v___x_1027_ = l_Lean_JsonNumber_lt(v_n_1025_, v_n_1026_);
return v___x_1027_;
}
case 0:
{
uint8_t v___x_1028_; 
lean_dec_ref_known(v_x_1020_, 1);
lean_dec_ref_known(v_x_1019_, 1);
v___x_1028_ = 1;
return v___x_1028_;
}
default: 
{
uint8_t v___x_1029_; 
lean_dec_ref_known(v_x_1019_, 1);
lean_dec(v_x_1020_);
v___x_1029_ = 0;
return v___x_1029_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_1020_))
{
case 1:
{
uint8_t v___x_1030_; 
lean_dec_ref_known(v_x_1020_, 1);
v___x_1030_ = 1;
return v___x_1030_;
}
case 0:
{
uint8_t v___x_1031_; 
lean_dec_ref_known(v_x_1020_, 1);
v___x_1031_ = 1;
return v___x_1031_;
}
default: 
{
uint8_t v___x_1032_; 
lean_dec(v_x_1020_);
v___x_1032_ = 0;
return v___x_1032_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_JsonRpc_RequestID_lt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1019_ = stack[0].m_obj;
lean_object* v_x_1020_ = stack[1].m_obj;
uint8_t v_res_1033_;
v_res_1033_ = l_Lean_JsonRpc_RequestID_lt(v_x_1019_, v_x_1020_);
stack->m_num = v_res_1033_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_RequestID_lt___boxed(lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
uint8_t v_res_1036_; lean_object* v_r_1037_; 
v_res_1036_ = l_Lean_JsonRpc_RequestID_lt(v_x_1034_, v_x_1035_);
v_r_1037_ = lean_box(v_res_1036_);
return v_r_1037_;
}
}
static lean_object* _init_l_Lean_JsonRpc_RequestID_ltProp(void){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_box(0);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_JsonRpc_instLTRequestID(void){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_box(0);
return v___x_1039_;
}
}
uint8_t l_Lean_JsonRpc_instDecidableLtRequestID(lean_object* v_a_1040_, lean_object* v_b_1041_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = l_Lean_JsonRpc_RequestID_lt(v_a_1040_, v_b_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instDecidableLtRequestID_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1040_ = stack[0].m_obj;
lean_object* v_b_1041_ = stack[1].m_obj;
uint8_t v_res_1043_;
v_res_1043_ = l_Lean_JsonRpc_instDecidableLtRequestID(v_a_1040_, v_b_1041_);
stack->m_num = v_res_1043_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instDecidableLtRequestID___boxed(lean_object* v_a_1044_, lean_object* v_b_1045_){
_start:
{
uint8_t v_res_1046_; lean_object* v_r_1047_; 
v_res_1046_ = l_Lean_JsonRpc_instDecidableLtRequestID(v_a_1044_, v_b_1045_);
v_r_1047_ = lean_box(v_res_1046_);
return v_r_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonRequestID___lam__0(lean_object* v_j_1051_){
_start:
{
switch(lean_obj_tag(v_j_1051_))
{
case 3:
{
lean_object* v_s_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1060_; 
v_s_1052_ = lean_ctor_get(v_j_1051_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_j_1051_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1054_ = v_j_1051_;
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_s_1052_);
lean_dec(v_j_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 0);
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_s_1052_);
v___x_1057_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
}
}
case 2:
{
lean_object* v_n_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1069_; 
v_n_1061_ = lean_ctor_get(v_j_1051_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_j_1051_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1063_ = v_j_1051_;
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_n_1061_);
lean_dec(v_j_1051_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set_tag(v___x_1063_, 1);
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_n_1061_);
v___x_1066_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
}
}
default: 
{
lean_object* v___x_1070_; 
lean_dec(v_j_1051_);
v___x_1070_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonRequestID___lam__0(lean_object* v_rid_1073_){
_start:
{
switch(lean_obj_tag(v_rid_1073_))
{
case 0:
{
lean_object* v_s_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_s_1074_ = lean_ctor_get(v_rid_1073_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_rid_1073_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v_rid_1073_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_s_1074_);
lean_dec(v_rid_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 3);
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_s_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
case 1:
{
lean_object* v_n_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_n_1082_ = lean_ctor_get(v_rid_1073_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_rid_1073_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v_rid_1073_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_n_1082_);
lean_dec(v_rid_1073_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 2);
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_n_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
default: 
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_box(0);
return v___x_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessage___lam__0(lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v_m_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___y_1113_; 
v___x_1111_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_1110_))
{
case 0:
{
lean_object* v_id_1116_; lean_object* v_method_1117_; lean_object* v_params_x3f_1118_; lean_object* v___x_1119_; lean_object* v___y_1121_; 
lean_dec_ref(v___x_1109_);
v_id_1116_ = lean_ctor_get(v_m_1110_, 0);
lean_inc(v_id_1116_);
v_method_1117_ = lean_ctor_get(v_m_1110_, 1);
lean_inc_ref(v_method_1117_);
v_params_x3f_1118_ = lean_ctor_get(v_m_1110_, 2);
lean_inc(v_params_x3f_1118_);
lean_dec_ref_known(v_m_1110_, 3);
v___x_1119_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1116_))
{
case 0:
{
lean_object* v_s_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_s_1132_ = lean_ctor_get(v_id_1116_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_id_1116_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v_id_1116_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_s_1132_);
lean_dec(v_id_1116_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 3);
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_s_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
v___y_1121_ = v___x_1137_;
goto v___jp_1120_;
}
}
}
case 1:
{
lean_object* v_n_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_n_1140_ = lean_ctor_get(v_id_1116_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_id_1116_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v_id_1116_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_n_1140_);
lean_dec(v_id_1116_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set_tag(v___x_1142_, 2);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_n_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
v___y_1121_ = v___x_1145_;
goto v___jp_1120_;
}
}
}
default: 
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_box(0);
v___y_1121_ = v___x_1148_;
goto v___jp_1120_;
}
}
v___jp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1119_);
lean_ctor_set(v___x_1122_, 1, v___y_1121_);
v___x_1123_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1124_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_method_1117_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1122_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1130_ = l_Lean_Json_opt___redArg(v___x_1108_, v___x_1129_, v_params_x3f_1118_);
v___x_1131_ = l_List_appendTR___redArg(v___x_1128_, v___x_1130_);
v___y_1113_ = v___x_1131_;
goto v___jp_1112_;
}
}
case 1:
{
lean_object* v_method_1149_; lean_object* v_params_x3f_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v___x_1109_);
v_method_1149_ = lean_ctor_get(v_m_1110_, 0);
v_params_x3f_1150_ = lean_ctor_get(v_m_1110_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_m_1110_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1152_ = v_m_1110_;
v_isShared_1153_ = v_isSharedCheck_1162_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_params_x3f_1150_);
lean_inc(v_method_1149_);
lean_dec(v_m_1110_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1162_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1154_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_1155_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_method_1149_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 0);
lean_ctor_set(v___x_1152_, 1, v___x_1155_);
lean_ctor_set(v___x_1152_, 0, v___x_1154_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1159_ = l_Lean_Json_opt___redArg(v___x_1108_, v___x_1158_, v_params_x3f_1150_);
v___x_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1157_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___y_1113_ = v___x_1160_;
goto v___jp_1112_;
}
}
}
case 2:
{
lean_object* v_id_1163_; lean_object* v_result_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v___x_1109_);
lean_dec_ref(v___x_1108_);
v_id_1163_ = lean_ctor_get(v_m_1110_, 0);
v_result_1164_ = lean_ctor_get(v_m_1110_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_m_1110_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1166_ = v_m_1110_;
v_isShared_1167_ = v_isSharedCheck_1196_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_result_1164_);
lean_inc(v_id_1163_);
lean_dec(v_m_1110_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1196_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___y_1170_; 
v___x_1168_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1163_))
{
case 0:
{
lean_object* v_s_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
v_s_1179_ = lean_ctor_get(v_id_1163_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_id_1163_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v_id_1163_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_s_1179_);
lean_dec(v_id_1163_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set_tag(v___x_1181_, 3);
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_s_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
v___y_1170_ = v___x_1184_;
goto v___jp_1169_;
}
}
}
case 1:
{
lean_object* v_n_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_n_1187_ = lean_ctor_get(v_id_1163_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_id_1163_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v_id_1163_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_n_1187_);
lean_dec(v_id_1163_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 2);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_n_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
v___y_1170_ = v___x_1192_;
goto v___jp_1169_;
}
}
}
default: 
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_box(0);
v___y_1170_ = v___x_1195_;
goto v___jp_1169_;
}
}
v___jp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set_tag(v___x_1166_, 0);
lean_ctor_set(v___x_1166_, 1, v___y_1170_);
lean_ctor_set(v___x_1166_, 0, v___x_1168_);
v___x_1172_ = v___x_1166_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___y_1170_);
v___x_1172_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1173_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v_result_1164_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1172_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___y_1113_ = v___x_1177_;
goto v___jp_1112_;
}
}
}
}
default: 
{
lean_object* v_id_1197_; uint8_t v_code_1198_; lean_object* v_message_1199_; lean_object* v_data_x3f_1200_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___x_1220_; lean_object* v___y_1222_; 
lean_dec_ref(v___x_1108_);
v_id_1197_ = lean_ctor_get(v_m_1110_, 0);
lean_inc(v_id_1197_);
v_code_1198_ = lean_ctor_get_uint8(v_m_1110_, sizeof(void*)*3);
v_message_1199_ = lean_ctor_get(v_m_1110_, 1);
lean_inc_ref(v_message_1199_);
v_data_x3f_1200_ = lean_ctor_get(v_m_1110_, 2);
lean_inc(v_data_x3f_1200_);
lean_dec_ref_known(v_m_1110_, 3);
v___x_1220_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_1197_))
{
case 0:
{
lean_object* v_s_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_s_1238_ = lean_ctor_get(v_id_1197_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_id_1197_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v_id_1197_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_s_1238_);
lean_dec(v_id_1197_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 3);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_s_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
v___y_1222_ = v___x_1243_;
goto v___jp_1221_;
}
}
}
case 1:
{
lean_object* v_n_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
v_n_1246_ = lean_ctor_get(v_id_1197_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_id_1197_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v_id_1197_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_n_1246_);
lean_dec(v_id_1197_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 2);
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_n_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
v___y_1222_ = v___x_1251_;
goto v___jp_1221_;
}
}
}
default: 
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_box(0);
v___y_1222_ = v___x_1254_;
goto v___jp_1221_;
}
}
v___jp_1201_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1202_);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___y_1202_);
lean_ctor_set(v___x_1206_, 1, v___y_1205_);
v___x_1207_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_message_1199_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_box(0);
v___x_1211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1206_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1214_ = l_Lean_Json_opt___redArg(v___x_1109_, v___x_1213_, v_data_x3f_1200_);
v___x_1215_ = l_List_appendTR___redArg(v___x_1212_, v___x_1214_);
v___x_1216_ = l_Lean_Json_mkObj(v___x_1215_);
lean_dec(v___x_1215_);
lean_inc_ref(v___y_1204_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___y_1204_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v___x_1210_);
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___y_1203_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___y_1113_ = v___x_1219_;
goto v___jp_1112_;
}
v___jp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1220_);
lean_ctor_set(v___x_1223_, 1, v___y_1222_);
v___x_1224_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1225_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_1198_)
{
case 0:
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1226_;
goto v___jp_1201_;
}
case 1:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1227_;
goto v___jp_1201_;
}
case 2:
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1228_;
goto v___jp_1201_;
}
case 3:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1229_;
goto v___jp_1201_;
}
case 4:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1230_;
goto v___jp_1201_;
}
case 5:
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1231_;
goto v___jp_1201_;
}
case 6:
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1232_;
goto v___jp_1201_;
}
case 7:
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1233_;
goto v___jp_1201_;
}
case 8:
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1234_;
goto v___jp_1201_;
}
case 9:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1235_;
goto v___jp_1201_;
}
case 10:
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1236_;
goto v___jp_1201_;
}
default: 
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_1202_ = v___x_1225_;
v___y_1203_ = v___x_1223_;
v___y_1204_ = v___x_1224_;
v___y_1205_ = v___x_1237_;
goto v___jp_1201_;
}
}
}
}
}
v___jp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1111_);
lean_ctor_set(v___x_1114_, 1, v___y_1113_);
v___x_1115_ = l_Lean_Json_mkObj(v___x_1114_);
lean_dec_ref_known(v___x_1114_, 2);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessage___lam__0(lean_object* v___f_1264_, lean_object* v___f_1265_, lean_object* v___x_1266_, lean_object* v___x_1267_, lean_object* v_j_1268_){
_start:
{
lean_object* v___y_1272_; uint8_t v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1268_);
v___x_1284_ = l_Lean_Json_getObjVal_x3f(v_j_1268_, v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_j_1268_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___f_1265_);
lean_dec_ref(v___f_1264_);
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v_a_1293_; 
v_a_1293_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1284_, 1);
if (lean_obj_tag(v_a_1293_) == 3)
{
lean_object* v_s_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v_s_1294_ = lean_ctor_get(v_a_1293_, 0);
lean_inc_ref(v_s_1294_);
lean_dec_ref_known(v_a_1293_, 1);
v___x_1295_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1296_ = lean_string_dec_eq(v_s_1294_, v___x_1295_);
lean_dec_ref(v_s_1294_);
if (v___x_1296_ == 0)
{
lean_dec(v_j_1268_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___f_1265_);
lean_dec_ref(v___f_1264_);
goto v___jp_1269_;
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1268_);
v___x_1298_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1268_, v___f_1264_, v___x_1297_);
if (lean_obj_tag(v___x_1298_) == 0)
{
goto v___jp_1355_;
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_a_1382_ = lean_ctor_get(v___x_1298_, 0);
v___x_1383_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1266_);
lean_inc(v_j_1268_);
v___x_1384_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1268_, v___x_1266_, v___x_1383_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_dec_ref_known(v___x_1384_, 1);
goto v___jp_1355_;
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1406_; 
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1298_, 1);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___f_1265_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1406_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1406_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___y_1390_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1396_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1268_, v___x_1267_, v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v___x_1397_; 
lean_dec_ref_known(v___x_1396_, 1);
v___x_1397_ = lean_box(0);
v___y_1390_ = v___x_1397_;
goto v___jp_1389_;
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_a_1398_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1396_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1396_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
v___y_1390_ = v___x_1403_;
goto v___jp_1389_;
}
}
}
v___jp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1391_, 0, v_a_1382_);
lean_ctor_set(v___x_1391_, 1, v_a_1385_);
lean_ctor_set(v___x_1391_, 2, v___y_1390_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1391_);
v___x_1393_ = v___x_1387_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
v___jp_1299_:
{
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_j_1268_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___f_1265_);
v_a_1300_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1298_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1298_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_a_1308_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1309_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1310_ = l_Lean_Json_getObjVal_x3f(v_j_1268_, v___x_1309_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v_a_1308_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___f_1265_);
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1310_, 0);
lean_inc_n(v_a_1319_, 2);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1320_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1321_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1319_, v___f_1265_, v___x_1320_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v_a_1319_);
lean_dec(v_a_1308_);
lean_dec_ref(v___x_1266_);
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_a_1330_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1321_, 1);
v___x_1331_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1319_);
v___x_1332_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1319_, v___x_1266_, v___x_1331_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_a_1330_);
lean_dec(v_a_1319_);
lean_dec(v_a_1308_);
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_a_1341_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1332_, 1);
v___x_1342_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1343_ = l_Lean_Json_getObjVal_x3f(v_a_1319_, v___x_1342_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
lean_dec_ref_known(v___x_1343_, 1);
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_unbox(v_a_1330_);
lean_dec(v_a_1330_);
v___y_1272_ = v_a_1341_;
v___y_1273_ = v___x_1345_;
v___y_1274_ = v_a_1308_;
v___y_1275_ = v___x_1344_;
goto v___jp_1271_;
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1354_; 
v_a_1346_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1348_ = v___x_1343_;
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1343_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_unbox(v_a_1330_);
lean_dec(v_a_1330_);
v___y_1272_ = v_a_1341_;
v___y_1273_ = v___x_1352_;
v___y_1274_ = v_a_1308_;
v___y_1275_ = v___x_1351_;
goto v___jp_1271_;
}
}
}
}
}
}
}
}
v___jp_1355_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc_ref(v___x_1266_);
lean_inc(v_j_1268_);
v___x_1357_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1268_, v___x_1266_, v___x_1356_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_dec_ref_known(v___x_1357_, 1);
lean_dec_ref(v___x_1267_);
if (lean_obj_tag(v___x_1298_) == 0)
{
goto v___jp_1299_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_a_1358_ = lean_ctor_get(v___x_1298_, 0);
v___x_1359_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1268_);
v___x_1360_ = l_Lean_Json_getObjVal_x3f(v_j_1268_, v___x_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_dec_ref_known(v___x_1360_, 1);
goto v___jp_1299_;
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1369_; 
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1298_, 1);
lean_dec(v_j_1268_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___f_1265_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_a_1358_);
lean_ctor_set(v___x_1365_, 1, v_a_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec_ref(v___x_1298_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___f_1265_);
v_a_1370_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1371_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1372_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1268_, v___x_1267_, v___x_1371_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1373_; 
lean_dec_ref_known(v___x_1372_, 1);
v___x_1373_ = lean_box(0);
v___y_1279_ = v_a_1370_;
v___y_1280_ = v___x_1373_;
goto v___jp_1278_;
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1372_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1372_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
v___y_1279_ = v_a_1370_;
v___y_1280_ = v___x_1379_;
goto v___jp_1278_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1293_);
lean_dec(v_j_1268_);
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___x_1266_);
lean_dec_ref(v___f_1265_);
lean_dec_ref(v___f_1264_);
goto v___jp_1269_;
}
}
v___jp_1269_:
{
lean_object* v___x_1270_; 
v___x_1270_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__1));
return v___x_1270_;
}
v___jp_1271_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1276_, 0, v___y_1274_);
lean_ctor_set(v___x_1276_, 1, v___y_1272_);
lean_ctor_set(v___x_1276_, 2, v___y_1275_);
lean_ctor_set_uint8(v___x_1276_, sizeof(void*)*3, v___y_1273_);
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
return v___x_1277_;
}
v___jp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___y_1279_);
lean_ctor_set(v___x_1281_, 1, v___y_1280_);
v___x_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0(lean_object* v___x_1420_, lean_object* v_inst_1421_, lean_object* v_j_1422_){
_start:
{
lean_object* v_method_1426_; lean_object* v_params_x3f_1427_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_j_1422_);
v___x_1450_ = l_Lean_Json_getObjVal_x3f(v_j_1422_, v___x_1449_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_j_1422_);
lean_dec_ref(v_inst_1421_);
lean_dec_ref(v___x_1420_);
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
else
{
lean_object* v_a_1459_; 
v_a_1459_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1450_, 1);
if (lean_obj_tag(v_a_1459_) == 3)
{
lean_object* v_s_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_s_1460_ = lean_ctor_get(v_a_1459_, 0);
lean_inc_ref(v_s_1460_);
lean_dec_ref_known(v_a_1459_, 1);
v___x_1461_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1462_ = lean_string_dec_eq(v_s_1460_, v___x_1461_);
lean_dec_ref(v_s_1460_);
if (v___x_1462_ == 0)
{
lean_dec(v_j_1422_);
lean_dec_ref(v_inst_1421_);
lean_dec_ref(v___x_1420_);
goto v___jp_1447_;
}
else
{
lean_object* v___f_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___f_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___f_1463_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___closed__0));
v___x_1464_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__0));
v___x_1465_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___closed__1));
v___f_1466_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___closed__0));
v___x_1467_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_j_1422_);
v___x_1468_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1422_, v___f_1463_, v___x_1467_);
if (lean_obj_tag(v___x_1468_) == 0)
{
goto v___jp_1509_;
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1422_);
v___x_1527_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1422_, v___x_1464_, v___x_1526_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_dec_ref_known(v___x_1527_, 1);
goto v___jp_1509_;
}
else
{
lean_dec_ref_known(v___x_1527_, 1);
lean_dec_ref_known(v___x_1468_, 1);
lean_dec(v_j_1422_);
lean_dec_ref(v_inst_1421_);
lean_dec_ref(v___x_1420_);
goto v___jp_1423_;
}
}
v___jp_1469_:
{
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_j_1422_);
v_a_1470_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1468_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1468_);
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
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec_ref_known(v___x_1468_, 1);
v___x_1478_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1479_ = l_Lean_Json_getObjVal_x3f(v_j_1422_, v___x_1478_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v_a_1488_ = lean_ctor_get(v___x_1479_, 0);
lean_inc_n(v_a_1488_, 2);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1489_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1490_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1488_, v___f_1466_, v___x_1489_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_a_1488_);
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec_ref_known(v___x_1490_, 1);
v___x_1499_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_1500_ = l_Lean_Json_getObjValAs_x3f___redArg(v_a_1488_, v___x_1464_, v___x_1499_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
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
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
lean_dec_ref_known(v___x_1500_, 1);
goto v___jp_1423_;
}
}
}
}
}
v___jp_1509_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_j_1422_);
v___x_1511_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1422_, v___x_1464_, v___x_1510_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_dec_ref_known(v___x_1511_, 1);
lean_dec_ref(v_inst_1421_);
lean_dec_ref(v___x_1420_);
if (lean_obj_tag(v___x_1468_) == 0)
{
goto v___jp_1469_;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_j_1422_);
v___x_1513_ = l_Lean_Json_getObjVal_x3f(v_j_1422_, v___x_1512_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_dec_ref_known(v___x_1513_, 1);
goto v___jp_1469_;
}
else
{
lean_dec_ref_known(v___x_1513_, 1);
lean_dec_ref_known(v___x_1468_, 1);
lean_dec(v_j_1422_);
goto v___jp_1423_;
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_dec_ref(v___x_1468_);
v_a_1514_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1515_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_1516_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1422_, v___x_1465_, v___x_1515_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v___x_1517_; 
lean_dec_ref_known(v___x_1516_, 1);
v___x_1517_ = lean_box(0);
v_method_1426_ = v_a_1514_;
v_params_x3f_1427_ = v___x_1517_;
goto v___jp_1425_;
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
v_a_1518_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1516_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1516_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
v_method_1426_ = v_a_1514_;
v_params_x3f_1427_ = v___x_1523_;
goto v___jp_1425_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1459_);
lean_dec(v_j_1422_);
lean_dec_ref(v_inst_1421_);
lean_dec_ref(v___x_1420_);
goto v___jp_1447_;
}
}
v___jp_1423_:
{
lean_object* v___x_1424_; 
v___x_1424_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__1));
return v___x_1424_;
}
v___jp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = l_Lean_Option_toJson___redArg(v___x_1420_, v_params_x3f_1427_);
v___x_1429_ = lean_apply_1(v_inst_1421_, v___x_1428_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v_method_1426_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1446_; 
v_a_1438_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1440_ = v___x_1429_;
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1429_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v_method_1426_);
lean_ctor_set(v___x_1442_, 1, v_a_1438_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1442_);
v___x_1444_ = v___x_1440_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
v___jp_1447_:
{
lean_object* v___x_1448_; 
v___x_1448_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0___closed__2));
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification___redArg(lean_object* v_inst_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___f_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___f_1530_ = lean_alloc_closure((void*)(l_Lean_JsonRpc_instFromJsonNotification___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1530_, 0, v___x_1529_);
lean_closure_set(v___f_1530_, 1, v_inst_1528_);
return v___f_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonNotification(lean_object* v_00_u03b1_1531_, lean_object* v_inst_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_JsonRpc_instFromJsonNotification___redArg(v_inst_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___impl(lean_object* v_x_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_obj_tag_nat(v_x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorIdx___impl___boxed(lean_object* v_x_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_JsonRpc_MessageMetaData_ctorIdx___impl(v_x_1536_);
lean_dec_ref(v_x_1536_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(lean_object* v_t_1538_, lean_object* v_k_1539_){
_start:
{
switch(lean_obj_tag(v_t_1538_))
{
case 0:
{
lean_object* v_id_1540_; lean_object* v_method_1541_; lean_object* v___x_1542_; 
v_id_1540_ = lean_ctor_get(v_t_1538_, 0);
lean_inc(v_id_1540_);
v_method_1541_ = lean_ctor_get(v_t_1538_, 1);
lean_inc_ref(v_method_1541_);
lean_dec_ref_known(v_t_1538_, 2);
v___x_1542_ = lean_apply_2(v_k_1539_, v_id_1540_, v_method_1541_);
return v___x_1542_;
}
case 1:
{
lean_object* v_method_1543_; lean_object* v___x_1544_; 
v_method_1543_ = lean_ctor_get(v_t_1538_, 0);
lean_inc_ref(v_method_1543_);
lean_dec_ref_known(v_t_1538_, 1);
v___x_1544_ = lean_apply_1(v_k_1539_, v_method_1543_);
return v___x_1544_;
}
case 2:
{
lean_object* v_id_1545_; lean_object* v___x_1546_; 
v_id_1545_ = lean_ctor_get(v_t_1538_, 0);
lean_inc(v_id_1545_);
lean_dec_ref_known(v_t_1538_, 1);
v___x_1546_ = lean_apply_1(v_k_1539_, v_id_1545_);
return v___x_1546_;
}
default: 
{
lean_object* v_id_1547_; uint8_t v_code_1548_; lean_object* v_message_1549_; lean_object* v_data_x3f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_id_1547_ = lean_ctor_get(v_t_1538_, 0);
lean_inc(v_id_1547_);
v_code_1548_ = lean_ctor_get_uint8(v_t_1538_, sizeof(void*)*3);
v_message_1549_ = lean_ctor_get(v_t_1538_, 1);
lean_inc_ref(v_message_1549_);
v_data_x3f_1550_ = lean_ctor_get(v_t_1538_, 2);
lean_inc(v_data_x3f_1550_);
lean_dec_ref_known(v_t_1538_, 3);
v___x_1551_ = lean_box(v_code_1548_);
v___x_1552_ = lean_apply_4(v_k_1539_, v_id_1547_, v___x_1551_, v_message_1549_, v_data_x3f_1550_);
return v___x_1552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim(lean_object* v_motive_1553_, lean_object* v_ctorIdx_1554_, lean_object* v_t_1555_, lean_object* v_h_1556_, lean_object* v_k_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1555_, v_k_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_ctorElim___boxed(lean_object* v_motive_1559_, lean_object* v_ctorIdx_1560_, lean_object* v_t_1561_, lean_object* v_h_1562_, lean_object* v_k_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_JsonRpc_MessageMetaData_ctorElim(v_motive_1559_, v_ctorIdx_1560_, v_t_1561_, v_h_1562_, v_k_1563_);
lean_dec(v_ctorIdx_1560_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim___redArg(lean_object* v_t_1565_, lean_object* v_request_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1565_, v_request_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_request_elim(lean_object* v_motive_1568_, lean_object* v_t_1569_, lean_object* v_h_1570_, lean_object* v_request_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1569_, v_request_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim___redArg(lean_object* v_t_1573_, lean_object* v_notification_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1573_, v_notification_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_notification_elim(lean_object* v_motive_1576_, lean_object* v_t_1577_, lean_object* v_h_1578_, lean_object* v_notification_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1577_, v_notification_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim___redArg(lean_object* v_t_1581_, lean_object* v_response_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1581_, v_response_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_response_elim(lean_object* v_motive_1584_, lean_object* v_t_1585_, lean_object* v_h_1586_, lean_object* v_response_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1585_, v_response_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim___redArg(lean_object* v_t_1589_, lean_object* v_responseError_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1589_, v_responseError_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_responseError_elim(lean_object* v_motive_1592_, lean_object* v_t_1593_, lean_object* v_h_1594_, lean_object* v_responseError_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_JsonRpc_MessageMetaData_ctorElim___redArg(v_t_1593_, v_responseError_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_Message_metaData(lean_object* v_x_1602_){
_start:
{
switch(lean_obj_tag(v_x_1602_))
{
case 0:
{
lean_object* v_id_1603_; lean_object* v_method_1604_; lean_object* v___x_1605_; 
v_id_1603_ = lean_ctor_get(v_x_1602_, 0);
lean_inc(v_id_1603_);
v_method_1604_ = lean_ctor_get(v_x_1602_, 1);
lean_inc_ref(v_method_1604_);
lean_dec_ref_known(v_x_1602_, 3);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v_id_1603_);
lean_ctor_set(v___x_1605_, 1, v_method_1604_);
return v___x_1605_;
}
case 1:
{
lean_object* v_method_1606_; lean_object* v___x_1607_; 
v_method_1606_ = lean_ctor_get(v_x_1602_, 0);
lean_inc_ref(v_method_1606_);
lean_dec_ref_known(v_x_1602_, 2);
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v_method_1606_);
return v___x_1607_;
}
case 2:
{
lean_object* v_id_1608_; lean_object* v___x_1609_; 
v_id_1608_ = lean_ctor_get(v_x_1602_, 0);
lean_inc(v_id_1608_);
lean_dec_ref_known(v_x_1602_, 2);
v___x_1609_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_id_1608_);
return v___x_1609_;
}
default: 
{
lean_object* v_id_1610_; uint8_t v_code_1611_; lean_object* v_message_1612_; lean_object* v_data_x3f_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_id_1610_ = lean_ctor_get(v_x_1602_, 0);
v_code_1611_ = lean_ctor_get_uint8(v_x_1602_, sizeof(void*)*3);
v_message_1612_ = lean_ctor_get(v_x_1602_, 1);
v_data_x3f_1613_ = lean_ctor_get(v_x_1602_, 2);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_x_1602_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v_x_1602_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_data_x3f_1613_);
lean_inc(v_message_1612_);
lean_inc(v_id_1610_);
lean_dec(v_x_1602_);
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
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageMetaData_toMessage(lean_object* v_x_1621_){
_start:
{
switch(lean_obj_tag(v_x_1621_))
{
case 0:
{
lean_object* v_id_1622_; lean_object* v_method_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_id_1622_ = lean_ctor_get(v_x_1621_, 0);
lean_inc(v_id_1622_);
v_method_1623_ = lean_ctor_get(v_x_1621_, 1);
lean_inc_ref(v_method_1623_);
lean_dec_ref_known(v_x_1621_, 2);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1625_, 0, v_id_1622_);
lean_ctor_set(v___x_1625_, 1, v_method_1623_);
lean_ctor_set(v___x_1625_, 2, v___x_1624_);
return v___x_1625_;
}
case 1:
{
lean_object* v_method_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_method_1626_ = lean_ctor_get(v_x_1621_, 0);
lean_inc_ref(v_method_1626_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1628_, 0, v_method_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
return v___x_1628_;
}
case 2:
{
lean_object* v_id_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v_id_1629_ = lean_ctor_get(v_x_1621_, 0);
lean_inc(v_id_1629_);
lean_dec_ref_known(v_x_1621_, 1);
v___x_1630_ = lean_box(0);
v___x_1631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1631_, 0, v_id_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
return v___x_1631_;
}
default: 
{
lean_object* v_id_1632_; uint8_t v_code_1633_; lean_object* v_message_1634_; lean_object* v_data_x3f_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
v_id_1632_ = lean_ctor_get(v_x_1621_, 0);
v_code_1633_ = lean_ctor_get_uint8(v_x_1621_, sizeof(void*)*3);
v_message_1634_ = lean_ctor_get(v_x_1621_, 1);
v_data_x3f_1635_ = lean_ctor_get(v_x_1621_, 2);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v_x_1621_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_data_x3f_1635_);
lean_inc(v_message_1634_);
lean_inc(v_id_1632_);
lean_dec(v_x_1621_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_id_1632_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_message_1634_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_data_x3f_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1641_, sizeof(void*)*3, v_code_1633_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(lean_object* v_a_1646_){
_start:
{
lean_object* v_fst_1647_; lean_object* v_snd_1648_; lean_object* v___x_1649_; uint8_t v_decide_1650_; 
v_fst_1647_ = lean_ctor_get(v_a_1646_, 0);
v_snd_1648_ = lean_ctor_get(v_a_1646_, 1);
v___x_1649_ = lean_string_utf8_byte_size(v_fst_1647_);
v_decide_1650_ = lean_nat_dec_eq(v_snd_1648_, v___x_1649_);
if (v_decide_1650_ == 0)
{
uint32_t v___x_1651_; uint32_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_string_utf8_get_fast(v_fst_1647_, v_snd_1648_);
v___x_1652_ = 34;
v___x_1653_ = lean_uint32_dec_eq(v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr___closed__1));
v___x_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1655_, 0, v_a_1646_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
return v___x_1655_;
}
else
{
lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1665_; 
lean_inc(v_snd_1648_);
lean_inc(v_fst_1647_);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_a_1646_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; lean_object* v_unused_1667_; 
v_unused_1666_ = lean_ctor_get(v_a_1646_, 1);
lean_dec(v_unused_1666_);
v_unused_1667_ = lean_ctor_get(v_a_1646_, 0);
lean_dec(v_unused_1667_);
v___x_1657_ = v_a_1646_;
v_isShared_1658_ = v_isSharedCheck_1665_;
goto v_resetjp_1656_;
}
else
{
lean_dec(v_a_1646_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1665_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = lean_string_utf8_next_fast(v_fst_1647_, v_snd_1648_);
lean_dec(v_snd_1648_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_fst_1647_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Lean_JsonRpc_instInhabitedRequestID_default___closed__0));
v___x_1663_ = l_Lean_Json_Parser_strCore(v___x_1662_, v___x_1661_);
return v___x_1663_;
}
}
}
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = lean_box(0);
v___x_1669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1669_, 0, v_a_1646_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(lean_object* v_a_1670_){
_start:
{
lean_object* v___x_1671_; 
lean_inc_ref(v_a_1670_);
v___x_1671_ = l_Lean_Json_Parser_num(v_a_1670_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_pos_1672_; lean_object* v_res_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1681_; 
lean_dec_ref(v_a_1670_);
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
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
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
lean_object* v_pos_1682_; lean_object* v_err_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1736_; 
v_pos_1682_ = lean_ctor_get(v___x_1671_, 0);
v_err_1683_ = lean_ctor_get(v___x_1671_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1685_ = v___x_1671_;
v_isShared_1686_ = v_isSharedCheck_1736_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_err_1683_);
lean_inc(v_pos_1682_);
lean_dec(v___x_1671_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1736_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_snd_1687_; lean_object* v_snd_1688_; uint8_t v_decide_1689_; 
v_snd_1687_ = lean_ctor_get(v_a_1670_, 1);
lean_inc(v_snd_1687_);
lean_dec_ref(v_a_1670_);
v_snd_1688_ = lean_ctor_get(v_pos_1682_, 1);
v_decide_1689_ = lean_nat_dec_eq(v_snd_1687_, v_snd_1688_);
lean_dec(v_snd_1687_);
if (v_decide_1689_ == 0)
{
lean_object* v___x_1691_; 
if (v_isShared_1686_ == 0)
{
v___x_1691_ = v___x_1685_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_pos_1682_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_err_1683_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
else
{
lean_object* v___x_1693_; 
lean_inc(v_snd_1688_);
lean_del_object(v___x_1685_);
lean_dec(v_err_1683_);
v___x_1693_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v_pos_1682_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_pos_1694_; lean_object* v_res_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_snd_1688_);
v_pos_1694_ = lean_ctor_get(v___x_1693_, 0);
v_res_1695_ = lean_ctor_get(v___x_1693_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1697_ = v___x_1693_;
v_isShared_1698_ = v_isSharedCheck_1703_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_res_1695_);
lean_inc(v_pos_1694_);
lean_dec(v___x_1693_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1703_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v_res_1695_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v___x_1699_);
v___x_1701_ = v___x_1697_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_pos_1694_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
else
{
lean_object* v_pos_1704_; lean_object* v_err_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1735_; 
v_pos_1704_ = lean_ctor_get(v___x_1693_, 0);
v_err_1705_ = lean_ctor_get(v___x_1693_, 1);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1707_ = v___x_1693_;
v_isShared_1708_ = v_isSharedCheck_1735_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_err_1705_);
lean_inc(v_pos_1704_);
lean_dec(v___x_1693_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1735_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_snd_1709_; uint8_t v_decide_1710_; 
v_snd_1709_ = lean_ctor_get(v_pos_1704_, 1);
v_decide_1710_ = lean_nat_dec_eq(v_snd_1688_, v_snd_1709_);
lean_dec(v_snd_1688_);
if (v_decide_1710_ == 0)
{
lean_object* v___x_1712_; 
if (v_isShared_1708_ == 0)
{
v___x_1712_ = v___x_1707_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_pos_1704_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_err_1705_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_del_object(v___x_1707_);
lean_dec(v_err_1705_);
v___x_1714_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___x_1715_ = l_Std_Internal_Parsec_String_pstring(v___x_1714_, v_pos_1704_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_pos_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1724_; 
v_pos_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v___x_1715_, 1);
lean_dec(v_unused_1725_);
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_pos_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1724_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1720_ = lean_box(2);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 1, v___x_1720_);
v___x_1722_ = v___x_1718_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_pos_1716_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
lean_object* v_pos_1726_; lean_object* v_err_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_pos_1726_ = lean_ctor_get(v___x_1715_, 0);
v_err_1727_ = lean_ctor_get(v___x_1715_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1715_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_err_1727_);
lean_inc(v_pos_1726_);
lean_dec(v___x_1715_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_pos_1726_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_err_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(lean_object* v_j_1737_, lean_object* v_k_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Json_getObjValD(v_j_1737_, v_k_1738_);
switch(lean_obj_tag(v___x_1739_))
{
case 3:
{
lean_object* v_s_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1748_; 
v_s_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_s_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set_tag(v___x_1742_, 0);
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_s_1740_);
v___x_1745_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
}
case 2:
{
lean_object* v_n_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1757_; 
v_n_1749_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1751_ = v___x_1739_;
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_n_1749_);
lean_dec(v___x_1739_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set_tag(v___x_1751_, 1);
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_n_1749_);
v___x_1754_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
}
default: 
{
lean_object* v___x_1758_; 
lean_dec(v___x_1739_);
v___x_1758_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonRequestID___lam__0___closed__1));
return v___x_1758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0___boxed(lean_object* v_j_1759_, lean_object* v_k_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_j_1759_, v_k_1760_);
lean_dec_ref(v_k_1760_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(lean_object* v_j_1762_, lean_object* v_k_1763_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Json_getObjValD(v_j_1762_, v_k_1763_);
if (lean_obj_tag(v___x_1766_) == 2)
{
lean_object* v_n_1767_; lean_object* v_mantissa_1768_; lean_object* v_exponent_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v_n_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc_ref(v_n_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v_mantissa_1768_ = lean_ctor_get(v_n_1767_, 0);
lean_inc(v_mantissa_1768_);
v_exponent_1769_ = lean_ctor_get(v_n_1767_, 1);
lean_inc(v_exponent_1769_);
lean_dec_ref(v_n_1767_);
v___x_1770_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__3);
v___x_1771_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__5);
v___x_1773_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__7);
v___x_1775_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__9);
v___x_1777_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__11);
v___x_1779_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1778_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__13);
v___x_1781_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__15);
v___x_1783_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__17);
v___x_1785_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__19);
v___x_1787_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__21);
v___x_1789_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__23);
v___x_1791_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_obj_once(&l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25, &l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25_once, _init_l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__25);
v___x_1793_ = lean_int_dec_eq(v_mantissa_1768_, v___x_1792_);
lean_dec(v_mantissa_1768_);
if (v___x_1793_ == 0)
{
lean_dec(v_exponent_1769_);
goto v___jp_1764_;
}
else
{
lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1794_);
lean_dec(v_exponent_1769_);
if (v___x_1795_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1796_; 
v___x_1796_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__26));
return v___x_1796_;
}
}
}
else
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
lean_dec(v_mantissa_1768_);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1797_);
lean_dec(v_exponent_1769_);
if (v___x_1798_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1799_; 
v___x_1799_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__27));
return v___x_1799_;
}
}
}
else
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
lean_dec(v_mantissa_1768_);
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1800_);
lean_dec(v_exponent_1769_);
if (v___x_1801_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1802_; 
v___x_1802_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__28));
return v___x_1802_;
}
}
}
else
{
lean_object* v___x_1803_; uint8_t v___x_1804_; 
lean_dec(v_mantissa_1768_);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1803_);
lean_dec(v_exponent_1769_);
if (v___x_1804_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1805_; 
v___x_1805_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__29));
return v___x_1805_;
}
}
}
else
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
lean_dec(v_mantissa_1768_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1806_);
lean_dec(v_exponent_1769_);
if (v___x_1807_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1808_; 
v___x_1808_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__30));
return v___x_1808_;
}
}
}
else
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
lean_dec(v_mantissa_1768_);
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1809_);
lean_dec(v_exponent_1769_);
if (v___x_1810_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1811_; 
v___x_1811_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__31));
return v___x_1811_;
}
}
}
else
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
lean_dec(v_mantissa_1768_);
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1812_);
lean_dec(v_exponent_1769_);
if (v___x_1813_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1814_; 
v___x_1814_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__32));
return v___x_1814_;
}
}
}
else
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
lean_dec(v_mantissa_1768_);
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1815_);
lean_dec(v_exponent_1769_);
if (v___x_1816_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1817_; 
v___x_1817_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__33));
return v___x_1817_;
}
}
}
else
{
lean_object* v___x_1818_; uint8_t v___x_1819_; 
lean_dec(v_mantissa_1768_);
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1819_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1818_);
lean_dec(v_exponent_1769_);
if (v___x_1819_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1820_; 
v___x_1820_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__34));
return v___x_1820_;
}
}
}
else
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
lean_dec(v_mantissa_1768_);
v___x_1821_ = lean_unsigned_to_nat(0u);
v___x_1822_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1821_);
lean_dec(v_exponent_1769_);
if (v___x_1822_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1823_; 
v___x_1823_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__35));
return v___x_1823_;
}
}
}
else
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
lean_dec(v_mantissa_1768_);
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1824_);
lean_dec(v_exponent_1769_);
if (v___x_1825_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1826_; 
v___x_1826_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__36));
return v___x_1826_;
}
}
}
else
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
lean_dec(v_mantissa_1768_);
v___x_1827_ = lean_unsigned_to_nat(0u);
v___x_1828_ = lean_nat_dec_eq(v_exponent_1769_, v___x_1827_);
lean_dec(v_exponent_1769_);
if (v___x_1828_ == 0)
{
goto v___jp_1764_;
}
else
{
lean_object* v___x_1829_; 
v___x_1829_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__37));
return v___x_1829_;
}
}
}
else
{
lean_dec(v___x_1766_);
goto v___jp_1764_;
}
v___jp_1764_:
{
lean_object* v___x_1765_; 
v___x_1765_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonErrorCode___lam__0___closed__1));
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1___boxed(lean_object* v_j_1830_, lean_object* v_k_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_j_1830_, v_k_1831_);
lean_dec_ref(v_k_1831_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(lean_object* v_j_1833_, lean_object* v_k_1834_){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = l_Lean_Json_getObjValD(v_j_1833_, v_k_1834_);
v___x_1836_ = l_Lean_Json_getStr_x3f(v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2___boxed(lean_object* v_j_1837_, lean_object* v_k_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_j_1837_, v_k_1838_);
lean_dec_ref(v_k_1838_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser(lean_object* v_input_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v_fst_1876_; lean_object* v_snd_1877_; lean_object* v___x_1878_; uint8_t v_decide_1879_; 
v_fst_1876_ = lean_ctor_get(v_a_1850_, 0);
v_snd_1877_ = lean_ctor_get(v_a_1850_, 1);
v___x_1878_ = lean_string_utf8_byte_size(v_fst_1876_);
v_decide_1879_ = lean_nat_dec_eq(v_snd_1877_, v___x_1878_);
if (v_decide_1879_ == 0)
{
lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_2229_; 
lean_inc(v_snd_1877_);
lean_inc(v_fst_1876_);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_a_1850_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; lean_object* v_unused_2231_; 
v_unused_2230_ = lean_ctor_get(v_a_1850_, 1);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_a_1850_, 0);
lean_dec(v_unused_2231_);
v___x_1881_ = v_a_1850_;
v_isShared_1882_ = v_isSharedCheck_2229_;
goto v_resetjp_1880_;
}
else
{
lean_dec(v_a_1850_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_2229_;
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
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_fst_1876_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_2228_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; 
v___x_1886_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1885_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_pos_1887_; lean_object* v_res_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_2218_; 
v_pos_1887_ = lean_ctor_get(v___x_1886_, 0);
v_res_1888_ = lean_ctor_get(v___x_1886_, 1);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_1890_ = v___x_1886_;
v_isShared_1891_ = v_isSharedCheck_2218_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_res_1888_);
lean_inc(v_pos_1887_);
lean_dec(v___x_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_2218_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_fst_1892_; lean_object* v_snd_1893_; lean_object* v___x_1894_; uint8_t v_decide_1895_; 
v_fst_1892_ = lean_ctor_get(v_pos_1887_, 0);
v_snd_1893_ = lean_ctor_get(v_pos_1887_, 1);
v___x_1894_ = lean_string_utf8_byte_size(v_fst_1892_);
v_decide_1895_ = lean_nat_dec_eq(v_snd_1893_, v___x_1894_);
if (v_decide_1895_ == 0)
{
lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_2211_; 
lean_inc(v_snd_1893_);
lean_inc(v_fst_1892_);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_pos_1887_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; lean_object* v_unused_2213_; 
v_unused_2212_ = lean_ctor_get(v_pos_1887_, 1);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_pos_1887_, 0);
lean_dec(v_unused_2213_);
v___x_1897_ = v_pos_1887_;
v_isShared_1898_ = v_isSharedCheck_2211_;
goto v_resetjp_1896_;
}
else
{
lean_dec(v_pos_1887_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_2211_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = lean_string_utf8_next_fast(v_fst_1892_, v_snd_1893_);
lean_dec(v_snd_1893_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v___x_1899_);
v___x_1901_ = v___x_1897_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_fst_1892_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_2210_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v_id_1903_; uint8_t v_code_1904_; lean_object* v_message_1905_; lean_object* v_data_x3f_1906_; lean_object* v_a_1915_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
v___x_1921_ = lean_string_dec_eq(v_res_1888_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
v___x_1923_ = lean_string_dec_eq(v_res_1888_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1924_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_1925_ = lean_string_dec_eq(v_res_1888_, v___x_1924_);
lean_dec(v_res_1888_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
lean_del_object(v___x_1890_);
lean_dec_ref(v_input_1849_);
v___x_1926_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__3));
v___x_1927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1901_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; 
v___x_1928_ = l_Lean_Json_parse(v_input_1849_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1937_; 
lean_del_object(v___x_1890_);
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1937_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1901_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
return v___x_1935_;
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1939_; 
v_a_1938_ = lean_ctor_get(v___x_1928_, 0);
lean_inc_n(v_a_1938_, 2);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1939_ = l_Lean_Json_getObjVal_x3f(v_a_1938_, v___x_1922_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; 
lean_dec(v_a_1938_);
lean_del_object(v___x_1890_);
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v_a_1915_ = v_a_1940_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_1941_; 
v_a_1941_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1939_, 1);
if (lean_obj_tag(v_a_1941_) == 3)
{
lean_object* v_s_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v_s_1942_ = lean_ctor_get(v_a_1941_, 0);
lean_inc_ref(v_s_1942_);
lean_dec_ref_known(v_a_1941_, 1);
v___x_1943_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_1944_ = lean_string_dec_eq(v_s_1942_, v___x_1943_);
lean_dec_ref(v_s_1942_);
if (v___x_1944_ == 0)
{
lean_dec(v_a_1938_);
lean_del_object(v___x_1890_);
goto v___jp_1918_;
}
else
{
lean_object* v___x_1945_; 
lean_inc(v_a_1938_);
v___x_1945_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_1938_, v___x_1920_);
if (lean_obj_tag(v___x_1945_) == 0)
{
goto v___jp_1973_;
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1938_);
v___x_1979_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1938_, v___x_1978_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_dec_ref_known(v___x_1979_, 1);
goto v___jp_1973_;
}
else
{
lean_dec_ref_known(v___x_1979_, 1);
lean_dec_ref_known(v___x_1945_, 1);
lean_dec(v_a_1938_);
lean_del_object(v___x_1890_);
goto v___jp_1911_;
}
}
v___jp_1946_:
{
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1947_; 
lean_dec(v_a_1938_);
lean_del_object(v___x_1890_);
v_a_1947_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1945_, 1);
v_a_1915_ = v_a_1947_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1949_; 
v_a_1948_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1945_, 1);
v___x_1949_ = l_Lean_Json_getObjVal_x3f(v_a_1938_, v___x_1924_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; 
lean_dec(v_a_1948_);
lean_del_object(v___x_1890_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v_a_1915_ = v_a_1950_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_a_1951_ = lean_ctor_get(v___x_1949_, 0);
lean_inc_n(v_a_1951_, 2);
lean_dec_ref_known(v___x_1949_, 1);
v___x_1952_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_1953_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_1951_, v___x_1952_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; 
lean_dec(v_a_1951_);
lean_dec(v_a_1948_);
lean_del_object(v___x_1890_);
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v_a_1915_ = v_a_1954_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v_a_1955_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1956_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_1951_);
v___x_1957_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1951_, v___x_1956_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; 
lean_dec(v_a_1955_);
lean_dec(v_a_1951_);
lean_dec(v_a_1948_);
lean_del_object(v___x_1890_);
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v_a_1915_ = v_a_1958_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v_a_1959_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1960_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_1961_ = l_Lean_Json_getObjVal_x3f(v_a_1951_, v___x_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
lean_dec_ref_known(v___x_1961_, 1);
v___x_1962_ = lean_box(0);
v___x_1963_ = lean_unbox(v_a_1955_);
lean_dec(v_a_1955_);
v_id_1903_ = v_a_1948_;
v_code_1904_ = v___x_1963_;
v_message_1905_ = v_a_1959_;
v_data_x3f_1906_ = v___x_1962_;
goto v___jp_1902_;
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_a_1964_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1966_ = v___x_1961_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1961_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_unbox(v_a_1955_);
lean_dec(v_a_1955_);
v_id_1903_ = v_a_1948_;
v_code_1904_ = v___x_1970_;
v_message_1905_ = v_a_1959_;
v_data_x3f_1906_ = v___x_1969_;
goto v___jp_1902_;
}
}
}
}
}
}
}
}
v___jp_1973_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_1938_);
v___x_1975_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_1938_, v___x_1974_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_dec_ref_known(v___x_1975_, 1);
if (lean_obj_tag(v___x_1945_) == 0)
{
goto v___jp_1946_;
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_1938_);
v___x_1977_ = l_Lean_Json_getObjVal_x3f(v_a_1938_, v___x_1976_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_dec_ref_known(v___x_1977_, 1);
goto v___jp_1946_;
}
else
{
lean_dec_ref_known(v___x_1977_, 1);
lean_dec_ref_known(v___x_1945_, 1);
lean_dec(v_a_1938_);
lean_del_object(v___x_1890_);
goto v___jp_1911_;
}
}
}
else
{
lean_dec_ref_known(v___x_1975_, 1);
lean_dec_ref(v___x_1945_);
lean_dec(v_a_1938_);
lean_del_object(v___x_1890_);
goto v___jp_1911_;
}
}
}
}
else
{
lean_dec(v_a_1941_);
lean_dec(v_a_1938_);
lean_del_object(v___x_1890_);
goto v___jp_1918_;
}
}
}
}
}
else
{
lean_object* v___x_1980_; 
lean_del_object(v___x_1890_);
lean_dec(v_res_1888_);
lean_dec_ref(v_input_1849_);
v___x_1980_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1901_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_pos_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2029_; 
v_pos_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v___x_1980_, 1);
lean_dec(v_unused_2030_);
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_2029_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_pos_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2029_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_fst_1985_; lean_object* v_snd_1986_; uint8_t v___y_1988_; lean_object* v___x_2027_; uint8_t v_decide_2028_; 
v_fst_1985_ = lean_ctor_get(v_pos_1981_, 0);
v_snd_1986_ = lean_ctor_get(v_pos_1981_, 1);
v___x_2027_ = lean_string_utf8_byte_size(v_fst_1985_);
v_decide_2028_ = lean_nat_dec_eq(v_snd_1986_, v___x_2027_);
if (v_decide_2028_ == 0)
{
v___y_1988_ = v___x_1923_;
goto v___jp_1987_;
}
else
{
v___y_1988_ = v___x_1921_;
goto v___jp_1987_;
}
v___jp_1987_:
{
if (v___y_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1989_ = lean_box(0);
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 1);
lean_ctor_set(v___x_1983_, 1, v___x_1989_);
v___x_1991_ = v___x_1983_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_pos_1981_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
else
{
lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2024_; 
lean_inc(v_snd_1986_);
lean_inc(v_fst_1985_);
lean_del_object(v___x_1983_);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_pos_1981_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; lean_object* v_unused_2026_; 
v_unused_2025_ = lean_ctor_get(v_pos_1981_, 1);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_pos_1981_, 0);
lean_dec(v_unused_2026_);
v___x_1994_ = v_pos_1981_;
v_isShared_1995_ = v_isSharedCheck_2024_;
goto v_resetjp_1993_;
}
else
{
lean_dec(v_pos_1981_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2024_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1996_ = lean_string_utf8_next_fast(v_fst_1985_, v_snd_1986_);
lean_dec(v_snd_1986_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 1, v___x_1996_);
v___x_1998_ = v___x_1994_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_fst_1985_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_2023_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_1999_; 
v___x_1999_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1998_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_pos_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2012_; 
v_pos_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v___x_1999_, 1);
lean_dec(v_unused_2013_);
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2012_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_pos_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2012_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___x_2006_; uint8_t v_decide_2007_; 
v_fst_2004_ = lean_ctor_get(v_pos_2000_, 0);
v_snd_2005_ = lean_ctor_get(v_pos_2000_, 1);
v___x_2006_ = lean_string_utf8_byte_size(v_fst_2004_);
v_decide_2007_ = lean_nat_dec_eq(v_snd_2005_, v___x_2006_);
if (v_decide_2007_ == 0)
{
lean_inc(v_snd_2005_);
lean_inc(v_fst_2004_);
lean_del_object(v___x_2002_);
lean_dec(v_pos_2000_);
v___y_1852_ = v_snd_2005_;
v___y_1853_ = v_fst_2004_;
goto v___jp_1851_;
}
else
{
if (v___x_1921_ == 0)
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = lean_box(0);
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 1);
lean_ctor_set(v___x_2002_, 1, v___x_2008_);
v___x_2010_ = v___x_2002_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_pos_2000_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
else
{
lean_inc(v_snd_2005_);
lean_inc(v_fst_2004_);
lean_del_object(v___x_2002_);
lean_dec(v_pos_2000_);
v___y_1852_ = v_snd_2005_;
v___y_1853_ = v_fst_2004_;
goto v___jp_1851_;
}
}
}
}
else
{
lean_object* v_pos_2014_; lean_object* v_err_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
v_pos_2014_ = lean_ctor_get(v___x_1999_, 0);
v_err_2015_ = lean_ctor_get(v___x_1999_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1999_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_err_2015_);
lean_inc(v_pos_2014_);
lean_dec(v___x_1999_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_pos_2014_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_err_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
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
lean_object* v_pos_2031_; lean_object* v_err_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
v_pos_2031_ = lean_ctor_get(v___x_1980_, 0);
v_err_2032_ = lean_ctor_get(v___x_1980_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1980_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_err_2032_);
lean_inc(v_pos_2031_);
lean_dec(v___x_1980_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_pos_2031_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_err_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
else
{
lean_object* v___x_2040_; 
lean_del_object(v___x_1890_);
lean_dec(v_res_1888_);
lean_dec_ref(v_input_1849_);
v___x_2040_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseRequestID(v___x_1901_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_pos_2041_; lean_object* v_res_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2200_; 
v_pos_2041_ = lean_ctor_get(v___x_2040_, 0);
v_res_2042_ = lean_ctor_get(v___x_2040_, 1);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2044_ = v___x_2040_;
v_isShared_2045_ = v_isSharedCheck_2200_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_res_2042_);
lean_inc(v_pos_2041_);
lean_dec(v___x_2040_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2200_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v___x_2053_; uint8_t v_decide_2054_; 
v_fst_2051_ = lean_ctor_get(v_pos_2041_, 0);
v_snd_2052_ = lean_ctor_get(v_pos_2041_, 1);
v___x_2053_ = lean_string_utf8_byte_size(v_fst_2051_);
v_decide_2054_ = lean_nat_dec_eq(v_snd_2052_, v___x_2053_);
if (v_decide_2054_ == 0)
{
if (v___x_1921_ == 0)
{
lean_dec(v_res_2042_);
goto v___jp_2046_;
}
else
{
lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2197_; 
lean_inc(v_snd_2052_);
lean_inc(v_fst_2051_);
lean_del_object(v___x_2044_);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_pos_2041_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; lean_object* v_unused_2199_; 
v_unused_2198_ = lean_ctor_get(v_pos_2041_, 1);
lean_dec(v_unused_2198_);
v_unused_2199_ = lean_ctor_get(v_pos_2041_, 0);
lean_dec(v_unused_2199_);
v___x_2056_ = v_pos_2041_;
v_isShared_2057_ = v_isSharedCheck_2197_;
goto v_resetjp_2055_;
}
else
{
lean_dec(v_pos_2041_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2197_;
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
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_fst_2051_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; 
v___x_2061_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2060_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_pos_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2185_; 
v_pos_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; 
v_unused_2186_ = lean_ctor_get(v___x_2061_, 1);
lean_dec(v_unused_2186_);
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2185_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_pos_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2185_;
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
lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2178_; 
lean_inc(v_snd_2067_);
lean_inc(v_fst_2066_);
lean_del_object(v___x_2064_);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_pos_2062_);
if (v_isSharedCheck_2178_ == 0)
{
lean_object* v_unused_2179_; lean_object* v_unused_2180_; 
v_unused_2179_ = lean_ctor_get(v_pos_2062_, 1);
lean_dec(v_unused_2179_);
v_unused_2180_ = lean_ctor_get(v_pos_2062_, 0);
lean_dec(v_unused_2180_);
v___x_2071_ = v_pos_2062_;
v_isShared_2072_ = v_isSharedCheck_2178_;
goto v_resetjp_2070_;
}
else
{
lean_dec(v_pos_2062_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2178_;
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
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_fst_2066_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; 
v___x_2076_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2075_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_pos_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2166_; 
v_pos_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2166_ == 0)
{
lean_object* v_unused_2167_; 
v_unused_2167_ = lean_ctor_get(v___x_2076_, 1);
lean_dec(v_unused_2167_);
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2166_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_pos_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2166_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v_fst_2081_; lean_object* v_snd_2082_; lean_object* v___x_2083_; uint8_t v_decide_2084_; 
v_fst_2081_ = lean_ctor_get(v_pos_2077_, 0);
v_snd_2082_ = lean_ctor_get(v_pos_2077_, 1);
v___x_2083_ = lean_string_utf8_byte_size(v_fst_2081_);
v_decide_2084_ = lean_nat_dec_eq(v_snd_2082_, v___x_2083_);
if (v_decide_2084_ == 0)
{
lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2159_; 
lean_inc(v_snd_2082_);
lean_inc(v_fst_2081_);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_pos_2077_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; lean_object* v_unused_2161_; 
v_unused_2160_ = lean_ctor_get(v_pos_2077_, 1);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_pos_2077_, 0);
lean_dec(v_unused_2161_);
v___x_2086_ = v_pos_2077_;
v_isShared_2087_ = v_isSharedCheck_2159_;
goto v_resetjp_2085_;
}
else
{
lean_dec(v_pos_2077_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2159_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2088_ = lean_string_utf8_next_fast(v_fst_2081_, v_snd_2082_);
lean_dec(v_snd_2082_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 1, v___x_2088_);
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_fst_2081_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; 
v___x_2091_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2090_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_pos_2092_; lean_object* v_res_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2148_; 
v_pos_2092_ = lean_ctor_get(v___x_2091_, 0);
v_res_2093_ = lean_ctor_get(v___x_2091_, 1);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2095_ = v___x_2091_;
v_isShared_2096_ = v_isSharedCheck_2148_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_res_2093_);
lean_inc(v_pos_2092_);
lean_dec(v___x_2091_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2148_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2103_ = lean_string_dec_eq(v_res_2093_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; uint8_t v___x_2105_; 
lean_del_object(v___x_2095_);
v___x_2104_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2105_ = lean_string_dec_eq(v_res_2093_, v___x_2104_);
lean_dec(v_res_2093_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
lean_dec(v_res_2042_);
v___x_2106_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__5));
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 1);
lean_ctor_set(v___x_2079_, 1, v___x_2106_);
lean_ctor_set(v___x_2079_, 0, v_pos_2092_);
v___x_2108_ = v___x_2079_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_pos_2092_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_res_2042_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v___x_2110_);
lean_ctor_set(v___x_2079_, 0, v_pos_2092_);
v___x_2112_ = v___x_2079_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_pos_2092_);
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
lean_object* v_fst_2114_; lean_object* v_snd_2115_; lean_object* v___x_2116_; uint8_t v_decide_2117_; 
lean_dec(v_res_2093_);
lean_del_object(v___x_2079_);
v_fst_2114_ = lean_ctor_get(v_pos_2092_, 0);
v_snd_2115_ = lean_ctor_get(v_pos_2092_, 1);
v___x_2116_ = lean_string_utf8_byte_size(v_fst_2114_);
v_decide_2117_ = lean_nat_dec_eq(v_snd_2115_, v___x_2116_);
if (v_decide_2117_ == 0)
{
if (v___x_2103_ == 0)
{
lean_dec(v_res_2042_);
goto v___jp_2097_;
}
else
{
lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2145_; 
lean_inc(v_snd_2115_);
lean_inc(v_fst_2114_);
lean_del_object(v___x_2095_);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_pos_2092_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; lean_object* v_unused_2147_; 
v_unused_2146_ = lean_ctor_get(v_pos_2092_, 1);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_pos_2092_, 0);
lean_dec(v_unused_2147_);
v___x_2119_ = v_pos_2092_;
v_isShared_2120_ = v_isSharedCheck_2145_;
goto v_resetjp_2118_;
}
else
{
lean_dec(v_pos_2092_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2145_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
v___x_2121_ = lean_string_utf8_next_fast(v_fst_2114_, v_snd_2115_);
lean_dec(v_snd_2115_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v___x_2121_);
v___x_2123_ = v___x_2119_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_fst_2114_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2124_; 
v___x_2124_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_2123_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_pos_2125_; lean_object* v_res_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2134_; 
v_pos_2125_ = lean_ctor_get(v___x_2124_, 0);
v_res_2126_ = lean_ctor_get(v___x_2124_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2128_ = v___x_2124_;
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_res_2126_);
lean_inc(v_pos_2125_);
lean_dec(v___x_2124_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_res_2042_);
lean_ctor_set(v___x_2130_, 1, v_res_2126_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v___x_2130_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_pos_2125_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
else
{
lean_object* v_pos_2135_; lean_object* v_err_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_res_2042_);
v_pos_2135_ = lean_ctor_get(v___x_2124_, 0);
v_err_2136_ = lean_ctor_get(v___x_2124_, 1);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2124_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_err_2136_);
lean_inc(v_pos_2135_);
lean_dec(v___x_2124_);
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
}
else
{
lean_dec(v_res_2042_);
goto v___jp_2097_;
}
}
v___jp_2097_:
{
lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2098_ = lean_box(0);
if (v_isShared_2096_ == 0)
{
lean_ctor_set_tag(v___x_2095_, 1);
lean_ctor_set(v___x_2095_, 1, v___x_2098_);
v___x_2100_ = v___x_2095_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_pos_2092_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_pos_2149_; lean_object* v_err_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_del_object(v___x_2079_);
lean_dec(v_res_2042_);
v_pos_2149_ = lean_ctor_get(v___x_2091_, 0);
v_err_2150_ = lean_ctor_get(v___x_2091_, 1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2091_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_err_2150_);
lean_inc(v_pos_2149_);
lean_dec(v___x_2091_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_pos_2149_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_err_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
lean_dec(v_res_2042_);
v___x_2162_ = lean_box(0);
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 1);
lean_ctor_set(v___x_2079_, 1, v___x_2162_);
v___x_2164_ = v___x_2079_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_pos_2077_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v_pos_2168_; lean_object* v_err_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_res_2042_);
v_pos_2168_ = lean_ctor_get(v___x_2076_, 0);
v_err_2169_ = lean_ctor_get(v___x_2076_, 1);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2076_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_err_2169_);
lean_inc(v_pos_2168_);
lean_dec(v___x_2076_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_pos_2168_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_err_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
lean_dec(v_res_2042_);
v___x_2181_ = lean_box(0);
if (v_isShared_2065_ == 0)
{
lean_ctor_set_tag(v___x_2064_, 1);
lean_ctor_set(v___x_2064_, 1, v___x_2181_);
v___x_2183_ = v___x_2064_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_pos_2062_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_pos_2187_; lean_object* v_err_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_res_2042_);
v_pos_2187_ = lean_ctor_get(v___x_2061_, 0);
v_err_2188_ = lean_ctor_get(v___x_2061_, 1);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2061_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_err_2188_);
lean_inc(v_pos_2187_);
lean_dec(v___x_2061_);
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
}
}
}
else
{
lean_dec(v_res_2042_);
goto v___jp_2046_;
}
v___jp_2046_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = lean_box(0);
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 1);
lean_ctor_set(v___x_2044_, 1, v___x_2047_);
v___x_2049_ = v___x_2044_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_pos_2041_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_pos_2201_; lean_object* v_err_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
v_pos_2201_ = lean_ctor_get(v___x_2040_, 0);
v_err_2202_ = lean_ctor_get(v___x_2040_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2040_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_err_2202_);
lean_inc(v_pos_2201_);
lean_dec(v___x_2040_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_pos_2201_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_err_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
v___jp_1902_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_1907_, 0, v_id_1903_);
lean_ctor_set(v___x_1907_, 1, v_message_1905_);
lean_ctor_set(v___x_1907_, 2, v_data_x3f_1906_);
lean_ctor_set_uint8(v___x_1907_, sizeof(void*)*3, v_code_1904_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v___x_1907_);
lean_ctor_set(v___x_1890_, 0, v___x_1901_);
v___x_1909_ = v___x_1890_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
v___jp_1911_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = ((lean_object*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser___closed__1));
v___x_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1901_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
return v___x_1913_;
}
v___jp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_a_1915_);
v___x_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1901_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
return v___x_1917_;
}
v___jp_1918_:
{
lean_object* v___x_1919_; 
v___x_1919_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_1915_ = v___x_1919_;
goto v___jp_1914_;
}
}
}
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
lean_dec(v_res_1888_);
lean_dec_ref(v_input_1849_);
v___x_2214_ = lean_box(0);
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 1);
lean_ctor_set(v___x_1890_, 1, v___x_2214_);
v___x_2216_ = v___x_1890_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_pos_1887_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
lean_object* v_pos_2219_; lean_object* v_err_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec_ref(v_input_1849_);
v_pos_2219_ = lean_ctor_get(v___x_1886_, 0);
v_err_2220_ = lean_ctor_get(v___x_1886_, 1);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_1886_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_err_2220_);
lean_inc(v_pos_2219_);
lean_dec(v___x_1886_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_pos_2219_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_err_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec_ref(v_input_1849_);
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_a_1850_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
return v___x_2233_;
}
v___jp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = lean_string_utf8_next_fast(v___y_1853_, v___y_1852_);
lean_dec(v___y_1852_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___y_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_parseStr(v___x_1855_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_pos_1857_; lean_object* v_res_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1866_; 
v_pos_1857_ = lean_ctor_get(v___x_1856_, 0);
v_res_1858_ = lean_ctor_get(v___x_1856_, 1);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1860_ = v___x_1856_;
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_res_1858_);
lean_inc(v_pos_1857_);
lean_dec(v___x_1856_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1866_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_res_1858_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 1, v___x_1862_);
v___x_1864_ = v___x_1860_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_pos_1857_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
else
{
lean_object* v_pos_1867_; lean_object* v_err_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_pos_1867_ = lean_ctor_get(v___x_1856_, 0);
v_err_1868_ = lean_ctor_get(v___x_1856_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1856_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_err_1868_);
lean_inc(v_pos_1867_);
lean_dec(v___x_1856_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_pos_1867_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_err_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_parseMessageMetaData(lean_object* v_input_2234_){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_inc_ref(v_input_2234_);
v___x_2235_ = lean_alloc_closure((void*)(l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser), 2, 1);
lean_closure_set(v___x_2235_, 0, v_input_2234_);
v___x_2236_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v___x_2235_, v_input_2234_);
return v___x_2236_;
}
}
lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___impl(uint8_t v_x_2237_){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_box(v_x_2237_);
v___x_2239_ = lean_obj_tag_nat(v___x_2238_);
lean_dec(v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_MessageDirection_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2237_ = stack[0].m_num;
lean_object* v_res_2240_;
v_res_2240_ = l_Lean_JsonRpc_MessageDirection_ctorIdx___impl(v_x_2237_);
stack->m_obj
 = v_res_2240_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorIdx___impl___boxed(lean_object* v_x_2241_){
_start:
{
uint8_t v_x_4__boxed_2242_; lean_object* v_res_2243_; 
v_x_4__boxed_2242_ = lean_unbox(v_x_2241_);
v_res_2243_ = l_Lean_JsonRpc_MessageDirection_ctorIdx___impl(v_x_4__boxed_2242_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(lean_object* v_k_2244_){
_start:
{
lean_inc(v_k_2244_);
return v_k_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___redArg___boxed(lean_object* v_k_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_JsonRpc_MessageDirection_ctorElim___redArg(v_k_2245_);
lean_dec(v_k_2245_);
return v_res_2246_;
}
}
lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim(lean_object* v_motive_2247_, lean_object* v_ctorIdx_2248_, uint8_t v_t_2249_, lean_object* v_h_2250_, lean_object* v_k_2251_){
_start:
{
lean_inc(v_k_2251_);
return v_k_2251_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_MessageDirection_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_2248_ = stack[1].m_obj;
uint8_t v_t_2249_ = stack[2].m_num;
lean_object* v_k_2251_ = stack[4].m_obj;
lean_object* v_res_2252_;
v_res_2252_ = l_Lean_JsonRpc_MessageDirection_ctorElim(lean_box(0), v_ctorIdx_2248_, v_t_2249_, lean_box(0), v_k_2251_);
stack->m_obj
 = v_res_2252_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_ctorElim___boxed(lean_object* v_motive_2253_, lean_object* v_ctorIdx_2254_, lean_object* v_t_2255_, lean_object* v_h_2256_, lean_object* v_k_2257_){
_start:
{
uint8_t v_t_boxed_2258_; lean_object* v_res_2259_; 
v_t_boxed_2258_ = lean_unbox(v_t_2255_);
v_res_2259_ = l_Lean_JsonRpc_MessageDirection_ctorElim(v_motive_2253_, v_ctorIdx_2254_, v_t_boxed_2258_, v_h_2256_, v_k_2257_);
lean_dec(v_k_2257_);
lean_dec(v_ctorIdx_2254_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(lean_object* v_clientToServer_2260_){
_start:
{
lean_inc(v_clientToServer_2260_);
return v_clientToServer_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg___boxed(lean_object* v_clientToServer_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim___redArg(v_clientToServer_2261_);
lean_dec(v_clientToServer_2261_);
return v_res_2262_;
}
}
lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_object* v_motive_2263_, uint8_t v_t_2264_, lean_object* v_h_2265_, lean_object* v_clientToServer_2266_){
_start:
{
lean_inc(v_clientToServer_2266_);
return v_clientToServer_2266_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_MessageDirection_clientToServer_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2264_ = stack[1].m_num;
lean_object* v_clientToServer_2266_ = stack[3].m_obj;
lean_object* v_res_2267_;
v_res_2267_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(lean_box(0), v_t_2264_, lean_box(0), v_clientToServer_2266_);
stack->m_obj
 = v_res_2267_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_clientToServer_elim___boxed(lean_object* v_motive_2268_, lean_object* v_t_2269_, lean_object* v_h_2270_, lean_object* v_clientToServer_2271_){
_start:
{
uint8_t v_t_boxed_2272_; lean_object* v_res_2273_; 
v_t_boxed_2272_ = lean_unbox(v_t_2269_);
v_res_2273_ = l_Lean_JsonRpc_MessageDirection_clientToServer_elim(v_motive_2268_, v_t_boxed_2272_, v_h_2270_, v_clientToServer_2271_);
lean_dec(v_clientToServer_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(lean_object* v_serverToClient_2274_){
_start:
{
lean_inc(v_serverToClient_2274_);
return v_serverToClient_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg___boxed(lean_object* v_serverToClient_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim___redArg(v_serverToClient_2275_);
lean_dec(v_serverToClient_2275_);
return v_res_2276_;
}
}
lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_object* v_motive_2277_, uint8_t v_t_2278_, lean_object* v_h_2279_, lean_object* v_serverToClient_2280_){
_start:
{
lean_inc(v_serverToClient_2280_);
return v_serverToClient_2280_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_MessageDirection_serverToClient_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2278_ = stack[1].m_num;
lean_object* v_serverToClient_2280_ = stack[3].m_obj;
lean_object* v_res_2281_;
v_res_2281_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(lean_box(0), v_t_2278_, lean_box(0), v_serverToClient_2280_);
stack->m_obj
 = v_res_2281_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageDirection_serverToClient_elim___boxed(lean_object* v_motive_2282_, lean_object* v_t_2283_, lean_object* v_h_2284_, lean_object* v_serverToClient_2285_){
_start:
{
uint8_t v_t_boxed_2286_; lean_object* v_res_2287_; 
v_t_boxed_2286_ = lean_unbox(v_t_2283_);
v_res_2287_ = l_Lean_JsonRpc_MessageDirection_serverToClient_elim(v_motive_2282_, v_t_boxed_2286_, v_h_2284_, v_serverToClient_2285_);
lean_dec(v_serverToClient_2285_);
return v_res_2287_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection_default(void){
_start:
{
uint8_t v___x_2288_; 
v___x_2288_ = 0;
return v___x_2288_;
}
}
static uint8_t _init_l_Lean_JsonRpc_instInhabitedMessageDirection(void){
_start:
{
uint8_t v___x_2289_; 
v___x_2289_ = 0;
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson(lean_object* v_json_2304_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_Json_getTag_x3f(v_json_2304_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v___x_2306_; 
v___x_2306_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__1));
return v___x_2306_;
}
else
{
lean_object* v_val_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v_val_2307_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_val_2307_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2308_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__2));
v___x_2309_ = lean_string_dec_eq(v_val_2307_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__3));
v___x_2311_ = lean_string_dec_eq(v_val_2307_, v___x_2310_);
lean_dec(v_val_2307_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; 
v___x_2312_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__5));
return v___x_2312_;
}
else
{
lean_object* v___x_2313_; 
v___x_2313_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__6));
return v___x_2313_;
}
}
else
{
lean_object* v___x_2314_; 
lean_dec(v_val_2307_);
v___x_2314_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageDirection_fromJson___closed__7));
return v___x_2314_;
}
}
}
}
lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson(uint8_t v_x_2321_){
_start:
{
if (v_x_2321_ == 0)
{
lean_object* v___x_2322_; 
v___x_2322_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__0));
return v___x_2322_;
}
else
{
lean_object* v___x_2323_; 
v___x_2323_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageDirection_toJson___closed__1));
return v___x_2323_;
}
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instToJsonMessageDirection_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2321_ = stack[0].m_num;
lean_object* v_res_2324_;
v_res_2324_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_x_2321_);
stack->m_obj
 = v_res_2324_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageDirection_toJson___boxed(lean_object* v_x_2325_){
_start:
{
uint8_t v_x_44__boxed_2326_; lean_object* v_res_2327_; 
v_x_44__boxed_2326_ = lean_unbox(v_x_2325_);
v_res_2327_ = l_Lean_JsonRpc_instToJsonMessageDirection_toJson(v_x_44__boxed_2326_);
return v_res_2327_;
}
}
lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___impl(uint8_t v_x_2330_){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_box(v_x_2330_);
v___x_2332_ = lean_obj_tag_nat(v___x_2331_);
lean_dec(v___x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_MessageKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2330_ = stack[0].m_num;
lean_object* v_res_2333_;
v_res_2333_ = l_Lean_JsonRpc_MessageKind_ctorIdx___impl(v_x_2330_);
stack->m_obj
 = v_res_2333_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorIdx___impl___boxed(lean_object* v_x_2334_){
_start:
{
uint8_t v_x_4__boxed_2335_; lean_object* v_res_2336_; 
v_x_4__boxed_2335_ = lean_unbox(v_x_2334_);
v_res_2336_ = l_Lean_JsonRpc_MessageKind_ctorIdx___impl(v_x_4__boxed_2335_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg(lean_object* v_k_2337_){
_start:
{
lean_inc(v_k_2337_);
return v_k_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___redArg___boxed(lean_object* v_k_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_JsonRpc_MessageKind_ctorElim___redArg(v_k_2338_);
lean_dec(v_k_2338_);
return v_res_2339_;
}
}
lean_object* l_Lean_JsonRpc_MessageKind_ctorElim(lean_object* v_motive_2340_, lean_object* v_ctorIdx_2341_, uint8_t v_t_2342_, lean_object* v_h_2343_, lean_object* v_k_2344_){
_start:
{
lean_inc(v_k_2344_);
return v_k_2344_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_MessageKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_2341_ = stack[1].m_obj;
uint8_t v_t_2342_ = stack[2].m_num;
lean_object* v_k_2344_ = stack[4].m_obj;
lean_object* v_res_2345_;
v_res_2345_ = l_Lean_JsonRpc_MessageKind_ctorElim(lean_box(0), v_ctorIdx_2341_, v_t_2342_, lean_box(0), v_k_2344_);
stack->m_obj
 = v_res_2345_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ctorElim___boxed(lean_object* v_motive_2346_, lean_object* v_ctorIdx_2347_, lean_object* v_t_2348_, lean_object* v_h_2349_, lean_object* v_k_2350_){
_start:
{
uint8_t v_t_boxed_2351_; lean_object* v_res_2352_; 
v_t_boxed_2351_ = lean_unbox(v_t_2348_);
v_res_2352_ = l_Lean_JsonRpc_MessageKind_ctorElim(v_motive_2346_, v_ctorIdx_2347_, v_t_boxed_2351_, v_h_2349_, v_k_2350_);
lean_dec(v_k_2350_);
lean_dec(v_ctorIdx_2347_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg(lean_object* v_request_2353_){
_start:
{
lean_inc(v_request_2353_);
return v_request_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___redArg___boxed(lean_object* v_request_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_JsonRpc_MessageKind_request_elim___redArg(v_request_2354_);
lean_dec(v_request_2354_);
return v_res_2355_;
}
}
lean_object* l_Lean_JsonRpc_MessageKind_request_elim(lean_object* v_motive_2356_, uint8_t v_t_2357_, lean_object* v_h_2358_, lean_object* v_request_2359_){
_start:
{
lean_inc(v_request_2359_);
return v_request_2359_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_MessageKind_request_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2357_ = stack[1].m_num;
lean_object* v_request_2359_ = stack[3].m_obj;
lean_object* v_res_2360_;
v_res_2360_ = l_Lean_JsonRpc_MessageKind_request_elim(lean_box(0), v_t_2357_, lean_box(0), v_request_2359_);
stack->m_obj
 = v_res_2360_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_request_elim___boxed(lean_object* v_motive_2361_, lean_object* v_t_2362_, lean_object* v_h_2363_, lean_object* v_request_2364_){
_start:
{
uint8_t v_t_boxed_2365_; lean_object* v_res_2366_; 
v_t_boxed_2365_ = lean_unbox(v_t_2362_);
v_res_2366_ = l_Lean_JsonRpc_MessageKind_request_elim(v_motive_2361_, v_t_boxed_2365_, v_h_2363_, v_request_2364_);
lean_dec(v_request_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg(lean_object* v_notification_2367_){
_start:
{
lean_inc(v_notification_2367_);
return v_notification_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___redArg___boxed(lean_object* v_notification_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_JsonRpc_MessageKind_notification_elim___redArg(v_notification_2368_);
lean_dec(v_notification_2368_);
return v_res_2369_;
}
}
lean_object* l_Lean_JsonRpc_MessageKind_notification_elim(lean_object* v_motive_2370_, uint8_t v_t_2371_, lean_object* v_h_2372_, lean_object* v_notification_2373_){
_start:
{
lean_inc(v_notification_2373_);
return v_notification_2373_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_MessageKind_notification_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2371_ = stack[1].m_num;
lean_object* v_notification_2373_ = stack[3].m_obj;
lean_object* v_res_2374_;
v_res_2374_ = l_Lean_JsonRpc_MessageKind_notification_elim(lean_box(0), v_t_2371_, lean_box(0), v_notification_2373_);
stack->m_obj
 = v_res_2374_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_notification_elim___boxed(lean_object* v_motive_2375_, lean_object* v_t_2376_, lean_object* v_h_2377_, lean_object* v_notification_2378_){
_start:
{
uint8_t v_t_boxed_2379_; lean_object* v_res_2380_; 
v_t_boxed_2379_ = lean_unbox(v_t_2376_);
v_res_2380_ = l_Lean_JsonRpc_MessageKind_notification_elim(v_motive_2375_, v_t_boxed_2379_, v_h_2377_, v_notification_2378_);
lean_dec(v_notification_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg(lean_object* v_response_2381_){
_start:
{
lean_inc(v_response_2381_);
return v_response_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___redArg___boxed(lean_object* v_response_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_JsonRpc_MessageKind_response_elim___redArg(v_response_2382_);
lean_dec(v_response_2382_);
return v_res_2383_;
}
}
lean_object* l_Lean_JsonRpc_MessageKind_response_elim(lean_object* v_motive_2384_, uint8_t v_t_2385_, lean_object* v_h_2386_, lean_object* v_response_2387_){
_start:
{
lean_inc(v_response_2387_);
return v_response_2387_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_MessageKind_response_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2385_ = stack[1].m_num;
lean_object* v_response_2387_ = stack[3].m_obj;
lean_object* v_res_2388_;
v_res_2388_ = l_Lean_JsonRpc_MessageKind_response_elim(lean_box(0), v_t_2385_, lean_box(0), v_response_2387_);
stack->m_obj
 = v_res_2388_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_response_elim___boxed(lean_object* v_motive_2389_, lean_object* v_t_2390_, lean_object* v_h_2391_, lean_object* v_response_2392_){
_start:
{
uint8_t v_t_boxed_2393_; lean_object* v_res_2394_; 
v_t_boxed_2393_ = lean_unbox(v_t_2390_);
v_res_2394_ = l_Lean_JsonRpc_MessageKind_response_elim(v_motive_2389_, v_t_boxed_2393_, v_h_2391_, v_response_2392_);
lean_dec(v_response_2392_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(lean_object* v_responseError_2395_){
_start:
{
lean_inc(v_responseError_2395_);
return v_responseError_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___redArg___boxed(lean_object* v_responseError_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_JsonRpc_MessageKind_responseError_elim___redArg(v_responseError_2396_);
lean_dec(v_responseError_2396_);
return v_res_2397_;
}
}
lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim(lean_object* v_motive_2398_, uint8_t v_t_2399_, lean_object* v_h_2400_, lean_object* v_responseError_2401_){
_start:
{
lean_inc(v_responseError_2401_);
return v_responseError_2401_;
}
}
LEAN_EXPORT void l_Lean_JsonRpc_MessageKind_responseError_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_2399_ = stack[1].m_num;
lean_object* v_responseError_2401_ = stack[3].m_obj;
lean_object* v_res_2402_;
v_res_2402_ = l_Lean_JsonRpc_MessageKind_responseError_elim(lean_box(0), v_t_2399_, lean_box(0), v_responseError_2401_);
stack->m_obj
 = v_res_2402_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_responseError_elim___boxed(lean_object* v_motive_2403_, lean_object* v_t_2404_, lean_object* v_h_2405_, lean_object* v_responseError_2406_){
_start:
{
uint8_t v_t_boxed_2407_; lean_object* v_res_2408_; 
v_t_boxed_2407_ = lean_unbox(v_t_2404_);
v_res_2408_ = l_Lean_JsonRpc_MessageKind_responseError_elim(v_motive_2403_, v_t_boxed_2407_, v_h_2405_, v_responseError_2406_);
lean_dec(v_responseError_2406_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instFromJsonMessageKind_fromJson(lean_object* v_json_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_Json_getTag_x3f(v_json_2429_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v___x_2431_; 
v___x_2431_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__0));
return v___x_2431_;
}
else
{
lean_object* v_val_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v_val_2432_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_val_2432_);
lean_dec_ref_known(v___x_2430_, 1);
v___x_2433_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__1));
v___x_2434_ = lean_string_dec_eq(v_val_2432_, v___x_2433_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; uint8_t v___x_2436_; 
v___x_2435_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__2));
v___x_2436_ = lean_string_dec_eq(v_val_2432_, v___x_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2437_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__3));
v___x_2438_ = lean_string_dec_eq(v_val_2432_, v___x_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2439_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__4));
v___x_2440_ = lean_string_dec_eq(v_val_2432_, v___x_2439_);
lean_dec(v_val_2432_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; 
v___x_2441_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__5));
return v___x_2441_;
}
else
{
lean_object* v___x_2442_; 
v___x_2442_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__6));
return v___x_2442_;
}
}
else
{
lean_object* v___x_2443_; 
lean_dec(v_val_2432_);
v___x_2443_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__7));
return v___x_2443_;
}
}
else
{
lean_object* v___x_2444_; 
lean_dec(v_val_2432_);
v___x_2444_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__8));
return v___x_2444_;
}
}
else
{
lean_object* v___x_2445_; 
lean_dec(v_val_2432_);
v___x_2445_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessageKind_fromJson___closed__9));
return v___x_2445_;
}
}
}
}
lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson(uint8_t v_x_2456_){
_start:
{
switch(v_x_2456_)
{
case 0:
{
lean_object* v___x_2457_; 
v___x_2457_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__0));
return v___x_2457_;
}
case 1:
{
lean_object* v___x_2458_; 
v___x_2458_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__1));
return v___x_2458_;
}
case 2:
{
lean_object* v___x_2459_; 
v___x_2459_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__2));
return v___x_2459_;
}
default: 
{
lean_object* v___x_2460_; 
v___x_2460_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessageKind_toJson___closed__3));
return v___x_2460_;
}
}
}
}
LEAN_EXPORT void l_Lean_JsonRpc_instToJsonMessageKind_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2456_ = stack[0].m_num;
lean_object* v_res_2461_;
v_res_2461_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_x_2456_);
stack->m_obj
 = v_res_2461_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_instToJsonMessageKind_toJson___boxed(lean_object* v_x_2462_){
_start:
{
uint8_t v_x_84__boxed_2463_; lean_object* v_res_2464_; 
v_x_84__boxed_2463_ = lean_unbox(v_x_2462_);
v_res_2464_ = l_Lean_JsonRpc_instToJsonMessageKind_toJson(v_x_84__boxed_2463_);
return v_res_2464_;
}
}
uint8_t l_Lean_JsonRpc_MessageKind_ofMessage(lean_object* v_x_2467_){
_start:
{
switch(lean_obj_tag(v_x_2467_))
{
case 0:
{
uint8_t v___x_2468_; 
v___x_2468_ = 0;
return v___x_2468_;
}
case 1:
{
uint8_t v___x_2469_; 
v___x_2469_ = 1;
return v___x_2469_;
}
case 2:
{
uint8_t v___x_2470_; 
v___x_2470_ = 2;
return v___x_2470_;
}
default: 
{
uint8_t v___x_2471_; 
v___x_2471_ = 3;
return v___x_2471_;
}
}
}
}
LEAN_EXPORT void l_Lean_JsonRpc_MessageKind_ofMessage_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2467_ = stack[0].m_obj;
uint8_t v_res_2472_;
v_res_2472_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_x_2467_);
stack->m_num = v_res_2472_;
}
LEAN_EXPORT lean_object* l_Lean_JsonRpc_MessageKind_ofMessage___boxed(lean_object* v_x_2473_){
_start:
{
uint8_t v_res_2474_; lean_object* v_r_2475_; 
v_res_2474_ = l_Lean_JsonRpc_MessageKind_ofMessage(v_x_2473_);
lean_dec_ref(v_x_2473_);
v_r_2475_ = lean_box(v_res_2474_);
return v_r_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(lean_object* v_j_2476_, lean_object* v_k_2477_){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = l_Lean_Json_getObjValD(v_j_2476_, v_k_2477_);
v___x_2479_ = l_Lean_Json_Structured_fromJson_x3f(v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0___boxed(lean_object* v_j_2480_, lean_object* v_k_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_j_2480_, v_k_2481_);
lean_dec_ref(v_k_2481_);
return v_res_2482_;
}
}
lean_object* l_Lean_IO_FS_Stream_readMessage(lean_object* v_h_2485_, lean_object* v_nBytes_2486_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Lean_IO_FS_Stream_readJson(v_h_2485_, v_nBytes_2486_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2608_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2608_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2608_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
uint8_t v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v_a_2508_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__0));
lean_inc(v_a_2489_);
v___x_2520_ = l_Lean_Json_getObjVal_x3f(v_a_2489_, v___x_2519_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; 
lean_del_object(v___x_2491_);
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v_a_2508_ = v_a_2521_;
goto v___jp_2507_;
}
else
{
lean_object* v_a_2522_; 
v_a_2522_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___x_2520_, 1);
if (lean_obj_tag(v_a_2522_) == 3)
{
lean_object* v_s_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v_s_2523_ = lean_ctor_get(v_a_2522_, 0);
lean_inc_ref(v_s_2523_);
lean_dec_ref_known(v_a_2522_, 1);
v___x_2524_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__1));
v___x_2525_ = lean_string_dec_eq(v_s_2523_, v___x_2524_);
lean_dec_ref(v_s_2523_);
if (v___x_2525_ == 0)
{
lean_del_object(v___x_2491_);
goto v___jp_2517_;
}
else
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
lean_inc(v_a_2489_);
v___x_2527_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__0(v_a_2489_, v___x_2526_);
if (lean_obj_tag(v___x_2527_) == 0)
{
goto v___jp_2556_;
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v_a_2583_ = lean_ctor_get(v___x_2527_, 0);
v___x_2584_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2489_);
v___x_2585_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2489_, v___x_2584_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_dec_ref_known(v___x_2585_, 1);
goto v___jp_2556_;
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2607_; 
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2527_, 1);
lean_del_object(v___x_2491_);
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2607_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2607_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___y_2591_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2597_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2489_, v___x_2596_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v___x_2598_; 
lean_dec_ref_known(v___x_2597_, 1);
v___x_2598_ = lean_box(0);
v___y_2591_ = v___x_2598_;
goto v___jp_2590_;
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
v_a_2599_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2597_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2597_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
v___y_2591_ = v___x_2604_;
goto v___jp_2590_;
}
}
}
v___jp_2590_:
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2592_, 0, v_a_2583_);
lean_ctor_set(v___x_2592_, 1, v_a_2586_);
lean_ctor_set(v___x_2592_, 2, v___y_2591_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2592_);
v___x_2594_ = v___x_2588_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
v___jp_2528_:
{
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2529_; 
lean_del_object(v___x_2491_);
v_a_2529_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2527_, 1);
v_a_2508_ = v_a_2529_;
goto v___jp_2507_;
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v_a_2530_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2531_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
lean_inc(v_a_2489_);
v___x_2532_ = l_Lean_Json_getObjVal_x3f(v_a_2489_, v___x_2531_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; 
lean_dec(v_a_2530_);
lean_del_object(v___x_2491_);
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v_a_2508_ = v_a_2533_;
goto v___jp_2507_;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_a_2534_ = lean_ctor_get(v___x_2532_, 0);
lean_inc_n(v_a_2534_, 2);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2535_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
v___x_2536_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__1(v_a_2534_, v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; 
lean_dec(v_a_2534_);
lean_dec(v_a_2530_);
lean_del_object(v___x_2491_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v_a_2508_ = v_a_2537_;
goto v___jp_2507_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v_a_2538_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2536_, 1);
v___x_2539_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
lean_inc(v_a_2534_);
v___x_2540_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2534_, v___x_2539_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; 
lean_dec(v_a_2538_);
lean_dec(v_a_2534_);
lean_dec(v_a_2530_);
lean_del_object(v___x_2491_);
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2540_, 1);
v_a_2508_ = v_a_2541_;
goto v___jp_2507_;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec(v_a_2489_);
v_a_2542_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2540_, 1);
v___x_2543_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2544_ = l_Lean_Json_getObjVal_x3f(v_a_2534_, v___x_2543_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v___x_2545_; uint8_t v___x_2546_; 
lean_dec_ref_known(v___x_2544_, 1);
v___x_2545_ = lean_box(0);
v___x_2546_ = lean_unbox(v_a_2538_);
lean_dec(v_a_2538_);
v___y_2494_ = v___x_2546_;
v___y_2495_ = v_a_2530_;
v___y_2496_ = v_a_2542_;
v___y_2497_ = v___x_2545_;
goto v___jp_2493_;
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2555_; 
v_a_2547_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2549_ = v___x_2544_;
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2544_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
uint8_t v___x_2553_; 
v___x_2553_ = lean_unbox(v_a_2538_);
lean_dec(v_a_2538_);
v___y_2494_ = v___x_2553_;
v___y_2495_ = v_a_2530_;
v___y_2496_ = v_a_2542_;
v___y_2497_ = v___x_2552_;
goto v___jp_2493_;
}
}
}
}
}
}
}
}
v___jp_2556_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
lean_inc(v_a_2489_);
v___x_2558_ = l_Lean_Json_getObjValAs_x3f___at___00__private_Lean_Data_JsonRpc_0__Lean_JsonRpc_messageMetaDataParser_spec__2(v_a_2489_, v___x_2557_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_dec_ref_known(v___x_2558_, 1);
if (lean_obj_tag(v___x_2527_) == 0)
{
goto v___jp_2528_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v_a_2559_ = lean_ctor_get(v___x_2527_, 0);
v___x_2560_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
lean_inc(v_a_2489_);
v___x_2561_ = l_Lean_Json_getObjVal_x3f(v_a_2489_, v___x_2560_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_dec_ref_known(v___x_2561_, 1);
goto v___jp_2528_;
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2570_; 
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2527_, 1);
lean_del_object(v___x_2491_);
lean_dec(v_a_2489_);
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2570_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2566_, 0, v_a_2559_);
lean_ctor_set(v___x_2566_, 1, v_a_2562_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set_tag(v___x_2564_, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2566_);
v___x_2568_ = v___x_2564_;
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
else
{
lean_object* v_a_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_dec_ref(v___x_2527_);
lean_del_object(v___x_2491_);
v_a_2571_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2572_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2573_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_IO_FS_Stream_readMessage_spec__0(v_a_2489_, v___x_2572_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v___x_2574_; 
lean_dec_ref_known(v___x_2573_, 1);
v___x_2574_ = lean_box(0);
v___y_2503_ = v_a_2571_;
v___y_2504_ = v___x_2574_;
goto v___jp_2502_;
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_a_2575_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2573_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2573_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
v___y_2503_ = v_a_2571_;
v___y_2504_ = v___x_2580_;
goto v___jp_2502_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2522_);
lean_del_object(v___x_2491_);
goto v___jp_2517_;
}
}
v___jp_2493_:
{
lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2498_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_2498_, 0, v___y_2495_);
lean_ctor_set(v___x_2498_, 1, v___y_2496_);
lean_ctor_set(v___x_2498_, 2, v___y_2497_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3, v___y_2494_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v___x_2498_);
v___x_2500_ = v___x_2491_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
v___jp_2502_:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___y_2503_);
lean_ctor_set(v___x_2505_, 1, v___y_2504_);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
return v___x_2506_;
}
v___jp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2509_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__0));
v___x_2510_ = l_Lean_Json_compress(v_a_2489_);
v___x_2511_ = lean_string_append(v___x_2509_, v___x_2510_);
lean_dec_ref(v___x_2510_);
v___x_2512_ = ((lean_object*)(l_Lean_IO_FS_Stream_readMessage___closed__1));
v___x_2513_ = lean_string_append(v___x_2511_, v___x_2512_);
v___x_2514_ = lean_string_append(v___x_2513_, v_a_2508_);
lean_dec_ref(v_a_2508_);
v___x_2515_ = lean_mk_io_user_error(v___x_2514_);
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
return v___x_2516_;
}
v___jp_2517_:
{
lean_object* v___x_2518_; 
v___x_2518_ = ((lean_object*)(l_Lean_JsonRpc_instFromJsonMessage___lam__0___closed__0));
v_a_2508_ = v___x_2518_;
goto v___jp_2507_;
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_a_2609_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2488_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2488_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readMessage_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2485_ = stack[0].m_obj;
lean_object* v_nBytes_2486_ = stack[1].m_obj;
lean_object* v_res_2617_;
v_res_2617_ = l_Lean_IO_FS_Stream_readMessage(v_h_2485_, v_nBytes_2486_);
stack->m_obj
 = v_res_2617_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readMessage___boxed(lean_object* v_h_2618_, lean_object* v_nBytes_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_IO_FS_Stream_readMessage(v_h_2618_, v_nBytes_2619_);
lean_dec(v_nBytes_2619_);
return v_res_2621_;
}
}
lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg(lean_object* v_h_2629_, lean_object* v_nBytes_2630_, lean_object* v_expectedMethod_2631_, lean_object* v_inst_2632_){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2635_ = l_Lean_IO_FS_Stream_readMessage(v_h_2629_, v_nBytes_2630_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2821_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2821_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2821_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
if (lean_obj_tag(v_a_2636_) == 0)
{
lean_object* v_id_2640_; lean_object* v_method_2641_; lean_object* v_params_x3f_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2681_; 
v_id_2640_ = lean_ctor_get(v_a_2636_, 0);
v_method_2641_ = lean_ctor_get(v_a_2636_, 1);
v_params_x3f_2642_ = lean_ctor_get(v_a_2636_, 2);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_a_2636_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2644_ = v_a_2636_;
v_isShared_2645_ = v_isSharedCheck_2681_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_params_x3f_2642_);
lean_inc(v_method_2641_);
lean_inc(v_id_2640_);
lean_dec(v_a_2636_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2681_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
uint8_t v___x_2646_; 
v___x_2646_ = lean_string_dec_eq(v_method_2641_, v_expectedMethod_2631_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; 
lean_del_object(v___x_2644_);
lean_dec(v_params_x3f_2642_);
lean_dec(v_id_2640_);
lean_dec_ref(v_inst_2632_);
v___x_2647_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2648_ = lean_string_append(v___x_2647_, v_expectedMethod_2631_);
lean_dec_ref(v_expectedMethod_2631_);
v___x_2649_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2650_ = lean_string_append(v___x_2648_, v___x_2649_);
v___x_2651_ = lean_string_append(v___x_2650_, v_method_2641_);
lean_dec_ref(v_method_2641_);
v___x_2652_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2653_ = lean_string_append(v___x_2651_, v___x_2652_);
v___x_2654_ = lean_mk_io_user_error(v___x_2653_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set_tag(v___x_2638_, 1);
lean_ctor_set(v___x_2638_, 0, v___x_2654_);
v___x_2656_ = v___x_2638_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec_ref(v_method_2641_);
v___x_2658_ = l_Lean_Option_toJson___redArg(v___x_2634_, v_params_x3f_2642_);
lean_inc(v___x_2658_);
v___x_2659_ = lean_apply_1(v_inst_2632_, v___x_2658_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
lean_del_object(v___x_2644_);
lean_dec(v_id_2640_);
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2662_ = l_Lean_Json_compress(v___x_2658_);
v___x_2663_ = lean_string_append(v___x_2661_, v___x_2662_);
lean_dec_ref(v___x_2662_);
v___x_2664_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2665_ = lean_string_append(v___x_2663_, v___x_2664_);
v___x_2666_ = lean_string_append(v___x_2665_, v_expectedMethod_2631_);
lean_dec_ref(v_expectedMethod_2631_);
v___x_2667_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2668_ = lean_string_append(v___x_2666_, v___x_2667_);
v___x_2669_ = lean_string_append(v___x_2668_, v_a_2660_);
lean_dec(v_a_2660_);
v___x_2670_ = lean_mk_io_user_error(v___x_2669_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set_tag(v___x_2638_, 1);
lean_ctor_set(v___x_2638_, 0, v___x_2670_);
v___x_2672_ = v___x_2638_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; 
lean_dec(v___x_2658_);
v_a_2674_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2659_, 1);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 2, v_a_2674_);
lean_ctor_set(v___x_2644_, 1, v_expectedMethod_2631_);
v___x_2676_ = v___x_2644_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_id_2640_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_expectedMethod_2631_);
lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_a_2674_);
v___x_2676_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2678_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2676_);
v___x_2678_ = v___x_2638_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___y_2685_; 
lean_dec_ref(v_inst_2632_);
lean_dec_ref(v_expectedMethod_2631_);
v___x_2682_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__6));
v___x_2683_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2636_))
{
case 0:
{
lean_object* v_id_2696_; lean_object* v_method_2697_; lean_object* v_params_x3f_2698_; lean_object* v___x_2699_; lean_object* v___y_2701_; 
v_id_2696_ = lean_ctor_get(v_a_2636_, 0);
lean_inc(v_id_2696_);
v_method_2697_ = lean_ctor_get(v_a_2636_, 1);
lean_inc_ref(v_method_2697_);
v_params_x3f_2698_ = lean_ctor_get(v_a_2636_, 2);
lean_inc(v_params_x3f_2698_);
lean_dec_ref_known(v_a_2636_, 3);
v___x_2699_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2696_) == 0)
{
lean_object* v_s_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
v_s_2712_ = lean_ctor_get(v_id_2696_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_id_2696_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v_id_2696_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_s_2712_);
lean_dec(v_id_2696_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
lean_ctor_set_tag(v___x_2714_, 3);
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_s_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
v___y_2701_ = v___x_2717_;
goto v___jp_2700_;
}
}
}
else
{
lean_object* v_n_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
v_n_2720_ = lean_ctor_get(v_id_2696_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_id_2696_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v_id_2696_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_n_2720_);
lean_dec(v_id_2696_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set_tag(v___x_2722_, 2);
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_n_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
v___y_2701_ = v___x_2725_;
goto v___jp_2700_;
}
}
}
v___jp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2699_);
lean_ctor_set(v___x_2702_, 1, v___y_2701_);
v___x_2703_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2704_, 0, v_method_2697_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_box(0);
v___x_2707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2702_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2710_ = l_Lean_Json_opt___redArg(v___x_2634_, v___x_2709_, v_params_x3f_2698_);
v___x_2711_ = l_List_appendTR___redArg(v___x_2708_, v___x_2710_);
v___y_2685_ = v___x_2711_;
goto v___jp_2684_;
}
}
case 1:
{
lean_object* v_method_2728_; lean_object* v_params_x3f_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_method_2728_ = lean_ctor_get(v_a_2636_, 0);
lean_inc_ref(v_method_2728_);
v_params_x3f_2729_ = lean_ctor_get(v_a_2636_, 1);
lean_inc(v_params_x3f_2729_);
lean_dec_ref_known(v_a_2636_, 2);
v___x_2730_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2731_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_method_2728_);
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2730_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2734_ = l_Lean_Json_opt___redArg(v___x_2634_, v___x_2733_, v_params_x3f_2729_);
v___x_2735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2732_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v___y_2685_ = v___x_2735_;
goto v___jp_2684_;
}
case 2:
{
lean_object* v_id_2736_; lean_object* v_result_2737_; lean_object* v___x_2738_; lean_object* v___y_2740_; 
v_id_2736_ = lean_ctor_get(v_a_2636_, 0);
lean_inc(v_id_2736_);
v_result_2737_ = lean_ctor_get(v_a_2636_, 1);
lean_inc(v_result_2737_);
lean_dec_ref_known(v_a_2636_, 2);
v___x_2738_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2736_) == 0)
{
lean_object* v_s_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
v_s_2747_ = lean_ctor_get(v_id_2736_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_id_2736_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v_id_2736_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_s_2747_);
lean_dec(v_id_2736_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set_tag(v___x_2749_, 3);
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_s_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
v___y_2740_ = v___x_2752_;
goto v___jp_2739_;
}
}
}
else
{
lean_object* v_n_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
v_n_2755_ = lean_ctor_get(v_id_2736_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_id_2736_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v_id_2736_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_n_2755_);
lean_dec(v_id_2736_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set_tag(v___x_2757_, 2);
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_n_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
v___y_2740_ = v___x_2760_;
goto v___jp_2739_;
}
}
}
v___jp_2739_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2738_);
lean_ctor_set(v___x_2741_, 1, v___y_2740_);
v___x_2742_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2742_);
lean_ctor_set(v___x_2743_, 1, v_result_2737_);
v___x_2744_ = lean_box(0);
v___x_2745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2741_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___y_2685_ = v___x_2746_;
goto v___jp_2684_;
}
}
default: 
{
lean_object* v_id_2763_; uint8_t v_code_2764_; lean_object* v_message_2765_; lean_object* v_data_x3f_2766_; lean_object* v___x_2767_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___x_2787_; lean_object* v___y_2789_; 
v_id_2763_ = lean_ctor_get(v_a_2636_, 0);
lean_inc(v_id_2763_);
v_code_2764_ = lean_ctor_get_uint8(v_a_2636_, sizeof(void*)*3);
v_message_2765_ = lean_ctor_get(v_a_2636_, 1);
lean_inc_ref(v_message_2765_);
v_data_x3f_2766_ = lean_ctor_get(v_a_2636_, 2);
lean_inc(v_data_x3f_2766_);
lean_dec_ref_known(v_a_2636_, 3);
v___x_2767_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_2787_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2763_) == 0)
{
lean_object* v_s_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
v_s_2805_ = lean_ctor_get(v_id_2763_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v_id_2763_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v_id_2763_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_s_2805_);
lean_dec(v_id_2763_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set_tag(v___x_2807_, 3);
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_s_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
v___y_2789_ = v___x_2810_;
goto v___jp_2788_;
}
}
}
else
{
lean_object* v_n_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_n_2813_ = lean_ctor_get(v_id_2763_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_id_2763_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v_id_2763_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_n_2813_);
lean_dec(v_id_2763_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 2);
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_n_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
v___y_2789_ = v___x_2818_;
goto v___jp_2788_;
}
}
}
v___jp_2768_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_inc(v___y_2772_);
lean_inc_ref(v___y_2771_);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___y_2771_);
lean_ctor_set(v___x_2773_, 1, v___y_2772_);
v___x_2774_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2775_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2775_, 0, v_message_2765_);
v___x_2776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = lean_box(0);
v___x_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2773_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_2781_ = l_Lean_Json_opt___redArg(v___x_2767_, v___x_2780_, v_data_x3f_2766_);
v___x_2782_ = l_List_appendTR___redArg(v___x_2779_, v___x_2781_);
v___x_2783_ = l_Lean_Json_mkObj(v___x_2782_);
lean_dec(v___x_2782_);
lean_inc_ref(v___y_2769_);
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___y_2769_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
lean_ctor_set(v___x_2785_, 1, v___x_2777_);
v___x_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___y_2770_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___y_2685_ = v___x_2786_;
goto v___jp_2684_;
}
v___jp_2788_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2787_);
lean_ctor_set(v___x_2790_, 1, v___y_2789_);
v___x_2791_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_2792_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2764_)
{
case 0:
{
lean_object* v___x_2793_; 
v___x_2793_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2793_;
goto v___jp_2768_;
}
case 1:
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2794_;
goto v___jp_2768_;
}
case 2:
{
lean_object* v___x_2795_; 
v___x_2795_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2795_;
goto v___jp_2768_;
}
case 3:
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2796_;
goto v___jp_2768_;
}
case 4:
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2797_;
goto v___jp_2768_;
}
case 5:
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2798_;
goto v___jp_2768_;
}
case 6:
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2799_;
goto v___jp_2768_;
}
case 7:
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2800_;
goto v___jp_2768_;
}
case 8:
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2801_;
goto v___jp_2768_;
}
case 9:
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2802_;
goto v___jp_2768_;
}
case 10:
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2803_;
goto v___jp_2768_;
}
default: 
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2769_ = v___x_2791_;
v___y_2770_ = v___x_2790_;
v___y_2771_ = v___x_2792_;
v___y_2772_ = v___x_2804_;
goto v___jp_2768_;
}
}
}
}
}
v___jp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2683_);
lean_ctor_set(v___x_2686_, 1, v___y_2685_);
v___x_2687_ = l_Lean_Json_mkObj(v___x_2686_);
lean_dec_ref_known(v___x_2686_, 2);
v___x_2688_ = l_Lean_Json_compress(v___x_2687_);
v___x_2689_ = lean_string_append(v___x_2682_, v___x_2688_);
lean_dec_ref(v___x_2688_);
v___x_2690_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2691_ = lean_string_append(v___x_2689_, v___x_2690_);
v___x_2692_ = lean_mk_io_user_error(v___x_2691_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set_tag(v___x_2638_, 1);
lean_ctor_set(v___x_2638_, 0, v___x_2692_);
v___x_2694_ = v___x_2638_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec_ref(v_inst_2632_);
lean_dec_ref(v_expectedMethod_2631_);
v_a_2822_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2635_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2635_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readRequestAs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2629_ = stack[0].m_obj;
lean_object* v_nBytes_2630_ = stack[1].m_obj;
lean_object* v_expectedMethod_2631_ = stack[2].m_obj;
lean_object* v_inst_2632_ = stack[3].m_obj;
lean_object* v_res_2830_;
v_res_2830_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2629_, v_nBytes_2630_, v_expectedMethod_2631_, v_inst_2632_);
stack->m_obj
 = v_res_2830_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg___boxed(lean_object* v_h_2831_, lean_object* v_nBytes_2832_, lean_object* v_expectedMethod_2833_, lean_object* v_inst_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2831_, v_nBytes_2832_, v_expectedMethod_2833_, v_inst_2834_);
lean_dec(v_nBytes_2832_);
return v_res_2836_;
}
}
lean_object* l_Lean_IO_FS_Stream_readRequestAs(lean_object* v_h_2837_, lean_object* v_nBytes_2838_, lean_object* v_expectedMethod_2839_, lean_object* v_00_u03b1_2840_, lean_object* v_inst_2841_){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_2837_, v_nBytes_2838_, v_expectedMethod_2839_, v_inst_2841_);
return v___x_2843_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readRequestAs_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2837_ = stack[0].m_obj;
lean_object* v_nBytes_2838_ = stack[1].m_obj;
lean_object* v_expectedMethod_2839_ = stack[2].m_obj;
lean_object* v_inst_2841_ = stack[4].m_obj;
lean_object* v_res_2844_;
v_res_2844_ = l_Lean_IO_FS_Stream_readRequestAs(v_h_2837_, v_nBytes_2838_, v_expectedMethod_2839_, lean_box(0), v_inst_2841_);
stack->m_obj
 = v_res_2844_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readRequestAs___boxed(lean_object* v_h_2845_, lean_object* v_nBytes_2846_, lean_object* v_expectedMethod_2847_, lean_object* v_00_u03b1_2848_, lean_object* v_inst_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_IO_FS_Stream_readRequestAs(v_h_2845_, v_nBytes_2846_, v_expectedMethod_2847_, v_00_u03b1_2848_, v_inst_2849_);
lean_dec(v_nBytes_2846_);
return v_res_2851_;
}
}
lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg(lean_object* v_h_2853_, lean_object* v_nBytes_2854_, lean_object* v_expectedMethod_2855_, lean_object* v_inst_2856_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_2859_ = l_Lean_IO_FS_Stream_readMessage(v_h_2853_, v_nBytes_2854_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_3044_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_3044_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_3044_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
if (lean_obj_tag(v_a_2860_) == 1)
{
lean_object* v_method_2864_; lean_object* v_params_x3f_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2904_; 
v_method_2864_ = lean_ctor_get(v_a_2860_, 0);
v_params_x3f_2865_ = lean_ctor_get(v_a_2860_, 1);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_a_2860_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2867_ = v_a_2860_;
v_isShared_2868_ = v_isSharedCheck_2904_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_params_x3f_2865_);
lean_inc(v_method_2864_);
lean_dec(v_a_2860_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2904_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
uint8_t v___x_2869_; 
v___x_2869_ = lean_string_dec_eq(v_method_2864_, v_expectedMethod_2855_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; 
lean_del_object(v___x_2867_);
lean_dec(v_params_x3f_2865_);
lean_dec_ref(v_inst_2856_);
v___x_2870_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__0));
v___x_2871_ = lean_string_append(v___x_2870_, v_expectedMethod_2855_);
lean_dec_ref(v_expectedMethod_2855_);
v___x_2872_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__1));
v___x_2873_ = lean_string_append(v___x_2871_, v___x_2872_);
v___x_2874_ = lean_string_append(v___x_2873_, v_method_2864_);
lean_dec_ref(v_method_2864_);
v___x_2875_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2876_ = lean_string_append(v___x_2874_, v___x_2875_);
v___x_2877_ = lean_mk_io_user_error(v___x_2876_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set_tag(v___x_2862_, 1);
lean_ctor_set(v___x_2862_, 0, v___x_2877_);
v___x_2879_ = v___x_2862_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_dec_ref(v_method_2864_);
v___x_2881_ = l_Lean_Option_toJson___redArg(v___x_2858_, v_params_x3f_2865_);
lean_inc(v___x_2881_);
v___x_2882_ = lean_apply_1(v_inst_2856_, v___x_2881_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
lean_del_object(v___x_2867_);
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
v___x_2884_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__3));
v___x_2885_ = l_Lean_Json_compress(v___x_2881_);
v___x_2886_ = lean_string_append(v___x_2884_, v___x_2885_);
lean_dec_ref(v___x_2885_);
v___x_2887_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__4));
v___x_2888_ = lean_string_append(v___x_2886_, v___x_2887_);
v___x_2889_ = lean_string_append(v___x_2888_, v_expectedMethod_2855_);
lean_dec_ref(v_expectedMethod_2855_);
v___x_2890_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_2891_ = lean_string_append(v___x_2889_, v___x_2890_);
v___x_2892_ = lean_string_append(v___x_2891_, v_a_2883_);
lean_dec(v_a_2883_);
v___x_2893_ = lean_mk_io_user_error(v___x_2892_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set_tag(v___x_2862_, 1);
lean_ctor_set(v___x_2862_, 0, v___x_2893_);
v___x_2895_ = v___x_2862_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; 
lean_dec(v___x_2881_);
v_a_2897_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___x_2882_, 1);
if (v_isShared_2868_ == 0)
{
lean_ctor_set_tag(v___x_2867_, 0);
lean_ctor_set(v___x_2867_, 1, v_a_2897_);
lean_ctor_set(v___x_2867_, 0, v_expectedMethod_2855_);
v___x_2899_ = v___x_2867_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_expectedMethod_2855_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_a_2897_);
v___x_2899_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2901_; 
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2899_);
v___x_2901_ = v___x_2862_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2899_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___y_2908_; 
lean_dec_ref(v_inst_2856_);
lean_dec_ref(v_expectedMethod_2855_);
v___x_2905_ = ((lean_object*)(l_Lean_IO_FS_Stream_readNotificationAs___redArg___closed__0));
v___x_2906_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_2860_))
{
case 0:
{
lean_object* v_id_2919_; lean_object* v_method_2920_; lean_object* v_params_x3f_2921_; lean_object* v___x_2922_; lean_object* v___y_2924_; 
v_id_2919_ = lean_ctor_get(v_a_2860_, 0);
lean_inc(v_id_2919_);
v_method_2920_ = lean_ctor_get(v_a_2860_, 1);
lean_inc_ref(v_method_2920_);
v_params_x3f_2921_ = lean_ctor_get(v_a_2860_, 2);
lean_inc(v_params_x3f_2921_);
lean_dec_ref_known(v_a_2860_, 3);
v___x_2922_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2919_) == 0)
{
lean_object* v_s_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
v_s_2935_ = lean_ctor_get(v_id_2919_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_id_2919_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v_id_2919_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_s_2935_);
lean_dec(v_id_2919_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set_tag(v___x_2937_, 3);
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_s_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
v___y_2924_ = v___x_2940_;
goto v___jp_2923_;
}
}
}
else
{
lean_object* v_n_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
v_n_2943_ = lean_ctor_get(v_id_2919_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_id_2919_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v_id_2919_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_n_2943_);
lean_dec(v_id_2919_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 2);
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_n_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
v___y_2924_ = v___x_2948_;
goto v___jp_2923_;
}
}
}
v___jp_2923_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2922_);
lean_ctor_set(v___x_2925_, 1, v___y_2924_);
v___x_2926_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2927_, 0, v_method_2920_);
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2926_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = lean_box(0);
v___x_2930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2928_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2925_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2933_ = l_Lean_Json_opt___redArg(v___x_2858_, v___x_2932_, v_params_x3f_2921_);
v___x_2934_ = l_List_appendTR___redArg(v___x_2931_, v___x_2933_);
v___y_2908_ = v___x_2934_;
goto v___jp_2907_;
}
}
case 1:
{
lean_object* v_method_2951_; lean_object* v_params_x3f_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_method_2951_ = lean_ctor_get(v_a_2860_, 0);
lean_inc_ref(v_method_2951_);
v_params_x3f_2952_ = lean_ctor_get(v_a_2860_, 1);
lean_inc(v_params_x3f_2952_);
lean_dec_ref_known(v_a_2860_, 2);
v___x_2953_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_2954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2954_, 0, v_method_2951_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_2957_ = l_Lean_Json_opt___redArg(v___x_2858_, v___x_2956_, v_params_x3f_2952_);
v___x_2958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2955_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___y_2908_ = v___x_2958_;
goto v___jp_2907_;
}
case 2:
{
lean_object* v_id_2959_; lean_object* v_result_2960_; lean_object* v___x_2961_; lean_object* v___y_2963_; 
v_id_2959_ = lean_ctor_get(v_a_2860_, 0);
lean_inc(v_id_2959_);
v_result_2960_ = lean_ctor_get(v_a_2860_, 1);
lean_inc(v_result_2960_);
lean_dec_ref_known(v_a_2860_, 2);
v___x_2961_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2959_) == 0)
{
lean_object* v_s_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
v_s_2970_ = lean_ctor_get(v_id_2959_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_id_2959_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v_id_2959_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_s_2970_);
lean_dec(v_id_2959_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set_tag(v___x_2972_, 3);
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_s_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
v___y_2963_ = v___x_2975_;
goto v___jp_2962_;
}
}
}
else
{
lean_object* v_n_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
v_n_2978_ = lean_ctor_get(v_id_2959_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_id_2959_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v_id_2959_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_n_2978_);
lean_dec(v_id_2959_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
lean_ctor_set_tag(v___x_2980_, 2);
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_n_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
v___y_2963_ = v___x_2983_;
goto v___jp_2962_;
}
}
}
v___jp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2961_);
lean_ctor_set(v___x_2964_, 1, v___y_2963_);
v___x_2965_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v_result_2960_);
v___x_2967_ = lean_box(0);
v___x_2968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2966_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2964_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___y_2908_ = v___x_2969_;
goto v___jp_2907_;
}
}
default: 
{
lean_object* v_id_2986_; uint8_t v_code_2987_; lean_object* v_message_2988_; lean_object* v_data_x3f_2989_; lean_object* v___x_2990_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___x_3010_; lean_object* v___y_3012_; 
v_id_2986_ = lean_ctor_get(v_a_2860_, 0);
lean_inc(v_id_2986_);
v_code_2987_ = lean_ctor_get_uint8(v_a_2860_, sizeof(void*)*3);
v_message_2988_ = lean_ctor_get(v_a_2860_, 1);
lean_inc_ref(v_message_2988_);
v_data_x3f_2989_ = lean_ctor_get(v_a_2860_, 2);
lean_inc(v_data_x3f_2989_);
lean_dec_ref_known(v_a_2860_, 3);
v___x_2990_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_3010_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_2986_) == 0)
{
lean_object* v_s_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
v_s_3028_ = lean_ctor_get(v_id_2986_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_id_2986_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v_id_2986_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_s_3028_);
lean_dec(v_id_2986_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
lean_ctor_set_tag(v___x_3030_, 3);
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_s_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
v___y_3012_ = v___x_3033_;
goto v___jp_3011_;
}
}
}
else
{
lean_object* v_n_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
v_n_3036_ = lean_ctor_get(v_id_2986_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_id_2986_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v_id_2986_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_n_3036_);
lean_dec(v_id_2986_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set_tag(v___x_3038_, 2);
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_n_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
v___y_3012_ = v___x_3041_;
goto v___jp_3011_;
}
}
}
v___jp_2991_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_inc(v___y_2995_);
lean_inc_ref(v___y_2993_);
v___x_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___y_2993_);
lean_ctor_set(v___x_2996_, 1, v___y_2995_);
v___x_2997_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_2998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_message_2988_);
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = lean_box(0);
v___x_3001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
v___x_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_2996_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3004_ = l_Lean_Json_opt___redArg(v___x_2990_, v___x_3003_, v_data_x3f_2989_);
v___x_3005_ = l_List_appendTR___redArg(v___x_3002_, v___x_3004_);
v___x_3006_ = l_Lean_Json_mkObj(v___x_3005_);
lean_dec(v___x_3005_);
lean_inc_ref(v___y_2994_);
v___x_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___y_2994_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v___x_3000_);
v___x_3009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___y_2992_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___y_2908_ = v___x_3009_;
goto v___jp_2907_;
}
v___jp_3011_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3010_);
lean_ctor_set(v___x_3013_, 1, v___y_3012_);
v___x_3014_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3015_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_2987_)
{
case 0:
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3016_;
goto v___jp_2991_;
}
case 1:
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3017_;
goto v___jp_2991_;
}
case 2:
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3018_;
goto v___jp_2991_;
}
case 3:
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3019_;
goto v___jp_2991_;
}
case 4:
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3020_;
goto v___jp_2991_;
}
case 5:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3021_;
goto v___jp_2991_;
}
case 6:
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3022_;
goto v___jp_2991_;
}
case 7:
{
lean_object* v___x_3023_; 
v___x_3023_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3023_;
goto v___jp_2991_;
}
case 8:
{
lean_object* v___x_3024_; 
v___x_3024_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3024_;
goto v___jp_2991_;
}
case 9:
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3025_;
goto v___jp_2991_;
}
case 10:
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3026_;
goto v___jp_2991_;
}
default: 
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_2992_ = v___x_3013_;
v___y_2993_ = v___x_3015_;
v___y_2994_ = v___x_3014_;
v___y_2995_ = v___x_3027_;
goto v___jp_2991_;
}
}
}
}
}
v___jp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2906_);
lean_ctor_set(v___x_2909_, 1, v___y_2908_);
v___x_2910_ = l_Lean_Json_mkObj(v___x_2909_);
lean_dec_ref_known(v___x_2909_, 2);
v___x_2911_ = l_Lean_Json_compress(v___x_2910_);
v___x_2912_ = lean_string_append(v___x_2905_, v___x_2911_);
lean_dec_ref(v___x_2911_);
v___x_2913_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_2914_ = lean_string_append(v___x_2912_, v___x_2913_);
v___x_2915_ = lean_mk_io_user_error(v___x_2914_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set_tag(v___x_2862_, 1);
lean_ctor_set(v___x_2862_, 0, v___x_2915_);
v___x_2917_ = v___x_2862_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec_ref(v_inst_2856_);
lean_dec_ref(v_expectedMethod_2855_);
v_a_3045_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_2859_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_2859_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readNotificationAs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2853_ = stack[0].m_obj;
lean_object* v_nBytes_2854_ = stack[1].m_obj;
lean_object* v_expectedMethod_2855_ = stack[2].m_obj;
lean_object* v_inst_2856_ = stack[3].m_obj;
lean_object* v_res_3053_;
v_res_3053_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_2853_, v_nBytes_2854_, v_expectedMethod_2855_, v_inst_2856_);
stack->m_obj
 = v_res_3053_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg___boxed(lean_object* v_h_3054_, lean_object* v_nBytes_3055_, lean_object* v_expectedMethod_3056_, lean_object* v_inst_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3054_, v_nBytes_3055_, v_expectedMethod_3056_, v_inst_3057_);
lean_dec(v_nBytes_3055_);
return v_res_3059_;
}
}
lean_object* l_Lean_IO_FS_Stream_readNotificationAs(lean_object* v_h_3060_, lean_object* v_nBytes_3061_, lean_object* v_expectedMethod_3062_, lean_object* v_00_u03b1_3063_, lean_object* v_inst_3064_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_3060_, v_nBytes_3061_, v_expectedMethod_3062_, v_inst_3064_);
return v___x_3066_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readNotificationAs_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3060_ = stack[0].m_obj;
lean_object* v_nBytes_3061_ = stack[1].m_obj;
lean_object* v_expectedMethod_3062_ = stack[2].m_obj;
lean_object* v_inst_3064_ = stack[4].m_obj;
lean_object* v_res_3067_;
v_res_3067_ = l_Lean_IO_FS_Stream_readNotificationAs(v_h_3060_, v_nBytes_3061_, v_expectedMethod_3062_, lean_box(0), v_inst_3064_);
stack->m_obj
 = v_res_3067_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readNotificationAs___boxed(lean_object* v_h_3068_, lean_object* v_nBytes_3069_, lean_object* v_expectedMethod_3070_, lean_object* v_00_u03b1_3071_, lean_object* v_inst_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_IO_FS_Stream_readNotificationAs(v_h_3068_, v_nBytes_3069_, v_expectedMethod_3070_, v_00_u03b1_3071_, v_inst_3072_);
lean_dec(v_nBytes_3069_);
return v_res_3074_;
}
}
lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg(lean_object* v_h_3079_, lean_object* v_nBytes_3080_, lean_object* v_expectedID_3081_, lean_object* v_inst_3082_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_IO_FS_Stream_readMessage(v_h_3079_, v_nBytes_3080_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3288_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3288_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3288_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___y_3090_; lean_object* v___y_3091_; 
if (lean_obj_tag(v_a_3085_) == 2)
{
lean_object* v_id_3097_; lean_object* v_result_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3149_; 
v_id_3097_ = lean_ctor_get(v_a_3085_, 0);
v_result_3098_ = lean_ctor_get(v_a_3085_, 1);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_a_3085_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3100_ = v_a_3085_;
v_isShared_3101_ = v_isSharedCheck_3149_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_result_3098_);
lean_inc(v_id_3097_);
lean_dec(v_a_3085_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3149_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
uint8_t v___x_3102_; 
v___x_3102_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_id_3097_, v_expectedID_3081_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; lean_object* v___y_3105_; 
lean_del_object(v___x_3100_);
lean_dec(v_result_3098_);
lean_dec_ref(v_inst_3082_);
v___x_3103_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__0));
switch(lean_obj_tag(v_expectedID_3081_))
{
case 0:
{
lean_object* v_s_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v_s_3115_ = lean_ctor_get(v_expectedID_3081_, 0);
lean_inc_ref(v_s_3115_);
lean_dec_ref_known(v_expectedID_3081_, 1);
v___x_3116_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3117_ = lean_string_append(v___x_3116_, v_s_3115_);
lean_dec_ref(v_s_3115_);
v___x_3118_ = lean_string_append(v___x_3117_, v___x_3116_);
v___y_3105_ = v___x_3118_;
goto v___jp_3104_;
}
case 1:
{
lean_object* v_n_3119_; lean_object* v___x_3120_; 
v_n_3119_ = lean_ctor_get(v_expectedID_3081_, 0);
lean_inc_ref(v_n_3119_);
lean_dec_ref_known(v_expectedID_3081_, 1);
v___x_3120_ = l_Lean_JsonNumber_toString(v_n_3119_);
v___y_3105_ = v___x_3120_;
goto v___jp_3104_;
}
default: 
{
lean_object* v___x_3121_; 
v___x_3121_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__1));
v___y_3105_ = v___x_3121_;
goto v___jp_3104_;
}
}
v___jp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = lean_string_append(v___x_3103_, v___y_3105_);
lean_dec_ref(v___y_3105_);
v___x_3107_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__1));
v___x_3108_ = lean_string_append(v___x_3106_, v___x_3107_);
if (lean_obj_tag(v_id_3097_) == 0)
{
lean_object* v_s_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v_s_3109_ = lean_ctor_get(v_id_3097_, 0);
lean_inc_ref(v_s_3109_);
lean_dec_ref_known(v_id_3097_, 1);
v___x_3110_ = ((lean_object*)(l_Lean_JsonRpc_instToStringRequestID___lam__0___closed__0));
v___x_3111_ = lean_string_append(v___x_3110_, v_s_3109_);
lean_dec_ref(v_s_3109_);
v___x_3112_ = lean_string_append(v___x_3111_, v___x_3110_);
v___y_3090_ = v___x_3108_;
v___y_3091_ = v___x_3112_;
goto v___jp_3089_;
}
else
{
lean_object* v_n_3113_; lean_object* v___x_3114_; 
v_n_3113_ = lean_ctor_get(v_id_3097_, 0);
lean_inc_ref(v_n_3113_);
lean_dec_ref_known(v_id_3097_, 1);
v___x_3114_ = l_Lean_JsonNumber_toString(v_n_3113_);
v___y_3090_ = v___x_3108_;
v___y_3091_ = v___x_3114_;
goto v___jp_3089_;
}
}
}
else
{
lean_object* v___x_3122_; 
lean_dec(v_id_3097_);
lean_del_object(v___x_3087_);
lean_inc(v_result_3098_);
v___x_3122_ = lean_apply_1(v_inst_3082_, v_result_3098_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3137_; 
lean_del_object(v___x_3100_);
lean_dec(v_expectedID_3081_);
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3137_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3137_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3127_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__2));
v___x_3128_ = l_Lean_Json_compress(v_result_3098_);
v___x_3129_ = lean_string_append(v___x_3127_, v___x_3128_);
lean_dec_ref(v___x_3128_);
v___x_3130_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__5));
v___x_3131_ = lean_string_append(v___x_3129_, v___x_3130_);
v___x_3132_ = lean_string_append(v___x_3131_, v_a_3123_);
lean_dec(v_a_3123_);
v___x_3133_ = lean_mk_io_user_error(v___x_3132_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set_tag(v___x_3125_, 1);
lean_ctor_set(v___x_3125_, 0, v___x_3133_);
v___x_3135_ = v___x_3125_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3148_; 
lean_dec(v_result_3098_);
v_a_3138_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3140_ = v___x_3122_;
v_isShared_3141_ = v_isSharedCheck_3148_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3122_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3148_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set_tag(v___x_3100_, 0);
lean_ctor_set(v___x_3100_, 1, v_a_3138_);
lean_ctor_set(v___x_3100_, 0, v_expectedID_3081_);
v___x_3143_ = v___x_3100_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_expectedID_3081_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
lean_object* v___x_3145_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set_tag(v___x_3140_, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3143_);
v___x_3145_ = v___x_3140_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___y_3154_; 
lean_del_object(v___x_3087_);
lean_dec_ref(v_inst_3082_);
lean_dec(v_expectedID_3081_);
v___x_3150_ = ((lean_object*)(l_Lean_IO_FS_Stream_readResponseAs___redArg___closed__3));
v___x_3151_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__0));
v___x_3152_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_a_3085_))
{
case 0:
{
lean_object* v_id_3163_; lean_object* v_method_3164_; lean_object* v_params_x3f_3165_; lean_object* v___x_3166_; lean_object* v___y_3168_; 
v_id_3163_ = lean_ctor_get(v_a_3085_, 0);
lean_inc(v_id_3163_);
v_method_3164_ = lean_ctor_get(v_a_3085_, 1);
lean_inc_ref(v_method_3164_);
v_params_x3f_3165_ = lean_ctor_get(v_a_3085_, 2);
lean_inc(v_params_x3f_3165_);
lean_dec_ref_known(v_a_3085_, 3);
v___x_3166_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3163_) == 0)
{
lean_object* v_s_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
v_s_3179_ = lean_ctor_get(v_id_3163_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_id_3163_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v_id_3163_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_s_3179_);
lean_dec(v_id_3163_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set_tag(v___x_3181_, 3);
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_s_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
v___y_3168_ = v___x_3184_;
goto v___jp_3167_;
}
}
}
else
{
lean_object* v_n_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
v_n_3187_ = lean_ctor_get(v_id_3163_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_id_3163_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v_id_3163_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_n_3187_);
lean_dec(v_id_3163_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set_tag(v___x_3189_, 2);
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_n_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
v___y_3168_ = v___x_3192_;
goto v___jp_3167_;
}
}
}
v___jp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3166_);
lean_ctor_set(v___x_3169_, 1, v___y_3168_);
v___x_3170_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3171_, 0, v_method_3164_);
v___x_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3170_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = lean_box(0);
v___x_3174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3172_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3169_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3177_ = l_Lean_Json_opt___redArg(v___x_3151_, v___x_3176_, v_params_x3f_3165_);
v___x_3178_ = l_List_appendTR___redArg(v___x_3175_, v___x_3177_);
v___y_3154_ = v___x_3178_;
goto v___jp_3153_;
}
}
case 1:
{
lean_object* v_method_3195_; lean_object* v_params_x3f_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v_method_3195_ = lean_ctor_get(v_a_3085_, 0);
lean_inc_ref(v_method_3195_);
v_params_x3f_3196_ = lean_ctor_get(v_a_3085_, 1);
lean_inc(v_params_x3f_3196_);
lean_dec_ref_known(v_a_3085_, 2);
v___x_3197_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3198_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3198_, 0, v_method_3195_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3197_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3201_ = l_Lean_Json_opt___redArg(v___x_3151_, v___x_3200_, v_params_x3f_3196_);
v___x_3202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3199_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
v___y_3154_ = v___x_3202_;
goto v___jp_3153_;
}
case 2:
{
lean_object* v_id_3203_; lean_object* v_result_3204_; lean_object* v___x_3205_; lean_object* v___y_3207_; 
v_id_3203_ = lean_ctor_get(v_a_3085_, 0);
lean_inc(v_id_3203_);
v_result_3204_ = lean_ctor_get(v_a_3085_, 1);
lean_inc(v_result_3204_);
lean_dec_ref_known(v_a_3085_, 2);
v___x_3205_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3203_) == 0)
{
lean_object* v_s_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
v_s_3214_ = lean_ctor_get(v_id_3203_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_id_3203_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v_id_3203_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_s_3214_);
lean_dec(v_id_3203_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
lean_ctor_set_tag(v___x_3216_, 3);
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_s_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
v___y_3207_ = v___x_3219_;
goto v___jp_3206_;
}
}
}
else
{
lean_object* v_n_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
v_n_3222_ = lean_ctor_get(v_id_3203_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_id_3203_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v_id_3203_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_n_3222_);
lean_dec(v_id_3203_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set_tag(v___x_3224_, 2);
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_n_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
v___y_3207_ = v___x_3227_;
goto v___jp_3206_;
}
}
}
v___jp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3205_);
lean_ctor_set(v___x_3208_, 1, v___y_3207_);
v___x_3209_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v_result_3204_);
v___x_3211_ = lean_box(0);
v___x_3212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3208_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___y_3154_ = v___x_3213_;
goto v___jp_3153_;
}
}
default: 
{
lean_object* v_id_3230_; uint8_t v_code_3231_; lean_object* v_message_3232_; lean_object* v_data_x3f_3233_; lean_object* v___x_3234_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___x_3254_; lean_object* v___y_3256_; 
v_id_3230_ = lean_ctor_get(v_a_3085_, 0);
lean_inc(v_id_3230_);
v_code_3231_ = lean_ctor_get_uint8(v_a_3085_, sizeof(void*)*3);
v_message_3232_ = lean_ctor_get(v_a_3085_, 1);
lean_inc_ref(v_message_3232_);
v_data_x3f_3233_ = lean_ctor_get(v_a_3085_, 2);
lean_inc(v_data_x3f_3233_);
lean_dec_ref_known(v_a_3085_, 3);
v___x_3234_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___closed__1));
v___x_3254_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
if (lean_obj_tag(v_id_3230_) == 0)
{
lean_object* v_s_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
v_s_3272_ = lean_ctor_get(v_id_3230_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v_id_3230_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v_id_3230_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_s_3272_);
lean_dec(v_id_3230_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
lean_ctor_set_tag(v___x_3274_, 3);
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_s_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
v___y_3256_ = v___x_3277_;
goto v___jp_3255_;
}
}
}
else
{
lean_object* v_n_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
v_n_3280_ = lean_ctor_get(v_id_3230_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v_id_3230_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v_id_3230_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_n_3280_);
lean_dec(v_id_3230_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
lean_ctor_set_tag(v___x_3282_, 2);
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_n_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
v___y_3256_ = v___x_3285_;
goto v___jp_3255_;
}
}
}
v___jp_3235_:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_inc(v___y_3239_);
lean_inc_ref(v___y_3236_);
v___x_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___y_3236_);
lean_ctor_set(v___x_3240_, 1, v___y_3239_);
v___x_3241_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3242_, 0, v_message_3232_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = lean_box(0);
v___x_3245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3240_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3248_ = l_Lean_Json_opt___redArg(v___x_3234_, v___x_3247_, v_data_x3f_3233_);
v___x_3249_ = l_List_appendTR___redArg(v___x_3246_, v___x_3248_);
v___x_3250_ = l_Lean_Json_mkObj(v___x_3249_);
lean_dec(v___x_3249_);
lean_inc_ref(v___y_3237_);
v___x_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___y_3237_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
lean_ctor_set(v___x_3252_, 1, v___x_3244_);
v___x_3253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___y_3238_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___y_3154_ = v___x_3253_;
goto v___jp_3153_;
}
v___jp_3255_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3254_);
lean_ctor_set(v___x_3257_, 1, v___y_3256_);
v___x_3258_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3259_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3231_)
{
case 0:
{
lean_object* v___x_3260_; 
v___x_3260_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3260_;
goto v___jp_3235_;
}
case 1:
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3261_;
goto v___jp_3235_;
}
case 2:
{
lean_object* v___x_3262_; 
v___x_3262_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3262_;
goto v___jp_3235_;
}
case 3:
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3263_;
goto v___jp_3235_;
}
case 4:
{
lean_object* v___x_3264_; 
v___x_3264_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3264_;
goto v___jp_3235_;
}
case 5:
{
lean_object* v___x_3265_; 
v___x_3265_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3265_;
goto v___jp_3235_;
}
case 6:
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3266_;
goto v___jp_3235_;
}
case 7:
{
lean_object* v___x_3267_; 
v___x_3267_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3267_;
goto v___jp_3235_;
}
case 8:
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3268_;
goto v___jp_3235_;
}
case 9:
{
lean_object* v___x_3269_; 
v___x_3269_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3269_;
goto v___jp_3235_;
}
case 10:
{
lean_object* v___x_3270_; 
v___x_3270_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3270_;
goto v___jp_3235_;
}
default: 
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3236_ = v___x_3259_;
v___y_3237_ = v___x_3258_;
v___y_3238_ = v___x_3257_;
v___y_3239_ = v___x_3271_;
goto v___jp_3235_;
}
}
}
}
}
v___jp_3153_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3152_);
lean_ctor_set(v___x_3155_, 1, v___y_3154_);
v___x_3156_ = l_Lean_Json_mkObj(v___x_3155_);
lean_dec_ref_known(v___x_3155_, 2);
v___x_3157_ = l_Lean_Json_compress(v___x_3156_);
v___x_3158_ = lean_string_append(v___x_3150_, v___x_3157_);
lean_dec_ref(v___x_3157_);
v___x_3159_ = ((lean_object*)(l_Lean_IO_FS_Stream_readRequestAs___redArg___closed__2));
v___x_3160_ = lean_string_append(v___x_3158_, v___x_3159_);
v___x_3161_ = lean_mk_io_user_error(v___x_3160_);
v___x_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
return v___x_3162_;
}
}
v___jp_3089_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3092_ = lean_string_append(v___y_3090_, v___y_3091_);
lean_dec_ref(v___y_3091_);
v___x_3093_ = lean_mk_io_user_error(v___x_3092_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set_tag(v___x_3087_, 1);
lean_ctor_set(v___x_3087_, 0, v___x_3093_);
v___x_3095_ = v___x_3087_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec_ref(v_inst_3082_);
lean_dec(v_expectedID_3081_);
v_a_3289_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3084_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3084_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readResponseAs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3079_ = stack[0].m_obj;
lean_object* v_nBytes_3080_ = stack[1].m_obj;
lean_object* v_expectedID_3081_ = stack[2].m_obj;
lean_object* v_inst_3082_ = stack[3].m_obj;
lean_object* v_res_3297_;
v_res_3297_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3079_, v_nBytes_3080_, v_expectedID_3081_, v_inst_3082_);
stack->m_obj
 = v_res_3297_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg___boxed(lean_object* v_h_3298_, lean_object* v_nBytes_3299_, lean_object* v_expectedID_3300_, lean_object* v_inst_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3298_, v_nBytes_3299_, v_expectedID_3300_, v_inst_3301_);
lean_dec(v_nBytes_3299_);
return v_res_3303_;
}
}
lean_object* l_Lean_IO_FS_Stream_readResponseAs(lean_object* v_h_3304_, lean_object* v_nBytes_3305_, lean_object* v_expectedID_3306_, lean_object* v_00_u03b1_3307_, lean_object* v_inst_3308_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_3304_, v_nBytes_3305_, v_expectedID_3306_, v_inst_3308_);
return v___x_3310_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readResponseAs_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3304_ = stack[0].m_obj;
lean_object* v_nBytes_3305_ = stack[1].m_obj;
lean_object* v_expectedID_3306_ = stack[2].m_obj;
lean_object* v_inst_3308_ = stack[4].m_obj;
lean_object* v_res_3311_;
v_res_3311_ = l_Lean_IO_FS_Stream_readResponseAs(v_h_3304_, v_nBytes_3305_, v_expectedID_3306_, lean_box(0), v_inst_3308_);
stack->m_obj
 = v_res_3311_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readResponseAs___boxed(lean_object* v_h_3312_, lean_object* v_nBytes_3313_, lean_object* v_expectedID_3314_, lean_object* v_00_u03b1_3315_, lean_object* v_inst_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_IO_FS_Stream_readResponseAs(v_h_3312_, v_nBytes_3313_, v_expectedID_3314_, v_00_u03b1_3315_, v_inst_3316_);
lean_dec(v_nBytes_3313_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(lean_object* v_k_3319_, lean_object* v_x_3320_){
_start:
{
if (lean_obj_tag(v_x_3320_) == 0)
{
lean_object* v___x_3321_; 
lean_dec_ref(v_k_3319_);
v___x_3321_ = lean_box(0);
return v___x_3321_;
}
else
{
lean_object* v_val_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v_val_3322_ = lean_ctor_get(v_x_3320_, 0);
lean_inc(v_val_3322_);
lean_dec_ref_known(v_x_3320_, 1);
v___x_3323_ = l_Lean_Json_Structured_toJson(v_val_3322_);
v___x_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3324_, 0, v_k_3319_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = lean_box(0);
v___x_3326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3324_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
return v___x_3326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(lean_object* v_k_3327_, lean_object* v_x_3328_){
_start:
{
if (lean_obj_tag(v_x_3328_) == 0)
{
lean_object* v___x_3329_; 
lean_dec_ref(v_k_3327_);
v___x_3329_ = lean_box(0);
return v___x_3329_;
}
else
{
lean_object* v_val_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_val_3330_ = lean_ctor_get(v_x_3328_, 0);
lean_inc(v_val_3330_);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v_k_3327_);
lean_ctor_set(v___x_3331_, 1, v_val_3330_);
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3331_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
return v___x_3333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1___boxed(lean_object* v_k_3334_, lean_object* v_x_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v_k_3334_, v_x_3335_);
lean_dec(v_x_3335_);
return v_res_3336_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeMessage(lean_object* v_h_3337_, lean_object* v_m_3338_){
_start:
{
lean_object* v___x_3340_; lean_object* v___y_3342_; 
v___x_3340_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__3));
switch(lean_obj_tag(v_m_3338_))
{
case 0:
{
lean_object* v_id_3346_; lean_object* v_method_3347_; lean_object* v_params_x3f_3348_; lean_object* v___x_3349_; lean_object* v___y_3351_; 
v_id_3346_ = lean_ctor_get(v_m_3338_, 0);
lean_inc(v_id_3346_);
v_method_3347_ = lean_ctor_get(v_m_3338_, 1);
lean_inc_ref(v_method_3347_);
v_params_x3f_3348_ = lean_ctor_get(v_m_3338_, 2);
lean_inc(v_params_x3f_3348_);
lean_dec_ref_known(v_m_3338_, 3);
v___x_3349_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3346_))
{
case 0:
{
lean_object* v_s_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
v_s_3362_ = lean_ctor_get(v_id_3346_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_id_3346_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v_id_3346_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_s_3362_);
lean_dec(v_id_3346_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set_tag(v___x_3364_, 3);
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_s_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
v___y_3351_ = v___x_3367_;
goto v___jp_3350_;
}
}
}
case 1:
{
lean_object* v_n_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
v_n_3370_ = lean_ctor_get(v_id_3346_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v_id_3346_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v_id_3346_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_n_3370_);
lean_dec(v_id_3346_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set_tag(v___x_3372_, 2);
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_n_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
v___y_3351_ = v___x_3375_;
goto v___jp_3350_;
}
}
}
default: 
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_box(0);
v___y_3351_ = v___x_3378_;
goto v___jp_3350_;
}
}
v___jp_3350_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3349_);
lean_ctor_set(v___x_3352_, 1, v___y_3351_);
v___x_3353_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_method_3347_);
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = lean_box(0);
v___x_3357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3352_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3360_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3359_, v_params_x3f_3348_);
v___x_3361_ = l_List_appendTR___redArg(v___x_3358_, v___x_3360_);
v___y_3342_ = v___x_3361_;
goto v___jp_3341_;
}
}
case 1:
{
lean_object* v_method_3379_; lean_object* v_params_x3f_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3392_; 
v_method_3379_ = lean_ctor_get(v_m_3338_, 0);
v_params_x3f_3380_ = lean_ctor_get(v_m_3338_, 1);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_m_3338_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3382_ = v_m_3338_;
v_isShared_3383_ = v_isSharedCheck_3392_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_params_x3f_3380_);
lean_inc(v_method_3379_);
lean_dec(v_m_3338_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3392_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; 
v___x_3384_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__5));
v___x_3385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3385_, 0, v_method_3379_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set_tag(v___x_3382_, 0);
lean_ctor_set(v___x_3382_, 1, v___x_3385_);
lean_ctor_set(v___x_3382_, 0, v___x_3384_);
v___x_3387_ = v___x_3382_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__6));
v___x_3389_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__0(v___x_3388_, v_params_x3f_3380_);
v___x_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3387_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___y_3342_ = v___x_3390_;
goto v___jp_3341_;
}
}
}
case 2:
{
lean_object* v_id_3393_; lean_object* v_result_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3426_; 
v_id_3393_ = lean_ctor_get(v_m_3338_, 0);
v_result_3394_ = lean_ctor_get(v_m_3338_, 1);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_m_3338_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3396_ = v_m_3338_;
v_isShared_3397_ = v_isSharedCheck_3426_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_result_3394_);
lean_inc(v_id_3393_);
lean_dec(v_m_3338_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3426_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3398_; lean_object* v___y_3400_; 
v___x_3398_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3393_))
{
case 0:
{
lean_object* v_s_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
v_s_3409_ = lean_ctor_get(v_id_3393_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_id_3393_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v_id_3393_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_s_3409_);
lean_dec(v_id_3393_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 3);
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_s_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
v___y_3400_ = v___x_3414_;
goto v___jp_3399_;
}
}
}
case 1:
{
lean_object* v_n_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
v_n_3417_ = lean_ctor_get(v_id_3393_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_id_3393_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v_id_3393_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_n_3417_);
lean_dec(v_id_3393_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set_tag(v___x_3419_, 2);
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_n_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
v___y_3400_ = v___x_3422_;
goto v___jp_3399_;
}
}
}
default: 
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_box(0);
v___y_3400_ = v___x_3425_;
goto v___jp_3399_;
}
}
v___jp_3399_:
{
lean_object* v___x_3402_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set_tag(v___x_3396_, 0);
lean_ctor_set(v___x_3396_, 1, v___y_3400_);
lean_ctor_set(v___x_3396_, 0, v___x_3398_);
v___x_3402_ = v___x_3396_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v___y_3400_);
v___x_3402_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3403_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__7));
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
lean_ctor_set(v___x_3404_, 1, v_result_3394_);
v___x_3405_ = lean_box(0);
v___x_3406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3402_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___y_3342_ = v___x_3407_;
goto v___jp_3341_;
}
}
}
}
default: 
{
lean_object* v_id_3427_; uint8_t v_code_3428_; lean_object* v_message_3429_; lean_object* v_data_x3f_3430_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___x_3450_; lean_object* v___y_3452_; 
v_id_3427_ = lean_ctor_get(v_m_3338_, 0);
lean_inc(v_id_3427_);
v_code_3428_ = lean_ctor_get_uint8(v_m_3338_, sizeof(void*)*3);
v_message_3429_ = lean_ctor_get(v_m_3338_, 1);
lean_inc_ref(v_message_3429_);
v_data_x3f_3430_ = lean_ctor_get(v_m_3338_, 2);
lean_inc(v_data_x3f_3430_);
lean_dec_ref_known(v_m_3338_, 3);
v___x_3450_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__4));
switch(lean_obj_tag(v_id_3427_))
{
case 0:
{
lean_object* v_s_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
v_s_3468_ = lean_ctor_get(v_id_3427_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_id_3427_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v_id_3427_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_s_3468_);
lean_dec(v_id_3427_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set_tag(v___x_3470_, 3);
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_s_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
v___y_3452_ = v___x_3473_;
goto v___jp_3451_;
}
}
}
case 1:
{
lean_object* v_n_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
v_n_3476_ = lean_ctor_get(v_id_3427_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_id_3427_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v_id_3427_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_n_3476_);
lean_dec(v_id_3427_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
lean_ctor_set_tag(v___x_3478_, 2);
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_n_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
v___y_3452_ = v___x_3481_;
goto v___jp_3451_;
}
}
}
default: 
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_box(0);
v___y_3452_ = v___x_3484_;
goto v___jp_3451_;
}
}
v___jp_3431_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3433_);
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___y_3433_);
lean_ctor_set(v___x_3436_, 1, v___y_3435_);
v___x_3437_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__8));
v___x_3438_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3438_, 0, v_message_3429_);
v___x_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3437_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = lean_box(0);
v___x_3441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3439_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3436_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___x_3443_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__9));
v___x_3444_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeMessage_spec__1(v___x_3443_, v_data_x3f_3430_);
lean_dec(v_data_x3f_3430_);
v___x_3445_ = l_List_appendTR___redArg(v___x_3442_, v___x_3444_);
v___x_3446_ = l_Lean_Json_mkObj(v___x_3445_);
lean_dec(v___x_3445_);
lean_inc_ref(v___y_3434_);
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___y_3434_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
lean_ctor_set(v___x_3448_, 1, v___x_3440_);
v___x_3449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___y_3432_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___y_3342_ = v___x_3449_;
goto v___jp_3341_;
}
v___jp_3451_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3450_);
lean_ctor_set(v___x_3453_, 1, v___y_3452_);
v___x_3454_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__10));
v___x_3455_ = ((lean_object*)(l_Lean_JsonRpc_instToJsonMessage___lam__0___closed__11));
switch(v_code_3428_)
{
case 0:
{
lean_object* v___x_3456_; 
v___x_3456_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__1);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3456_;
goto v___jp_3431_;
}
case 1:
{
lean_object* v___x_3457_; 
v___x_3457_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__3);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3457_;
goto v___jp_3431_;
}
case 2:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__5);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3458_;
goto v___jp_3431_;
}
case 3:
{
lean_object* v___x_3459_; 
v___x_3459_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__7);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3459_;
goto v___jp_3431_;
}
case 4:
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__9);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3460_;
goto v___jp_3431_;
}
case 5:
{
lean_object* v___x_3461_; 
v___x_3461_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__11);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3461_;
goto v___jp_3431_;
}
case 6:
{
lean_object* v___x_3462_; 
v___x_3462_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__13);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3462_;
goto v___jp_3431_;
}
case 7:
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__15);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3463_;
goto v___jp_3431_;
}
case 8:
{
lean_object* v___x_3464_; 
v___x_3464_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__17);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3464_;
goto v___jp_3431_;
}
case 9:
{
lean_object* v___x_3465_; 
v___x_3465_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__19);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3465_;
goto v___jp_3431_;
}
case 10:
{
lean_object* v___x_3466_; 
v___x_3466_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__21);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3466_;
goto v___jp_3431_;
}
default: 
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_obj_once(&l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23, &l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23_once, _init_l_Lean_JsonRpc_instToJsonErrorCode___lam__0___closed__23);
v___y_3432_ = v___x_3453_;
v___y_3433_ = v___x_3455_;
v___y_3434_ = v___x_3454_;
v___y_3435_ = v___x_3467_;
goto v___jp_3431_;
}
}
}
}
}
v___jp_3341_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3340_);
lean_ctor_set(v___x_3343_, 1, v___y_3342_);
v___x_3344_ = l_Lean_Json_mkObj(v___x_3343_);
lean_dec_ref_known(v___x_3343_, 2);
v___x_3345_ = l_Lean_IO_FS_Stream_writeJson(v_h_3337_, v___x_3344_);
return v___x_3345_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeMessage_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3337_ = stack[0].m_obj;
lean_object* v_m_3338_ = stack[1].m_obj;
lean_object* v_res_3485_;
v_res_3485_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3337_, v_m_3338_);
stack->m_obj
 = v_res_3485_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeMessage___boxed(lean_object* v_h_3486_, lean_object* v_m_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3486_, v_m_3487_);
return v_res_3489_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg(lean_object* v_inst_3490_, lean_object* v_h_3491_, lean_object* v_r_3492_){
_start:
{
lean_object* v_id_3494_; lean_object* v_method_3495_; lean_object* v_param_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3516_; 
v_id_3494_ = lean_ctor_get(v_r_3492_, 0);
v_method_3495_ = lean_ctor_get(v_r_3492_, 1);
v_param_3496_ = lean_ctor_get(v_r_3492_, 2);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_r_3492_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3498_ = v_r_3492_;
v_isShared_3499_ = v_isSharedCheck_3516_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_param_3496_);
lean_inc(v_method_3495_);
lean_inc(v_id_3494_);
lean_dec(v_r_3492_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3516_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___y_3501_; lean_object* v___x_3506_; 
v___x_3506_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3490_, v_param_3496_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v___x_3507_; 
lean_dec_ref_known(v___x_3506_, 1);
v___x_3507_ = lean_box(0);
v___y_3501_ = v___x_3507_;
goto v___jp_3500_;
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
v_a_3508_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3506_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3506_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
v___y_3501_ = v___x_3513_;
goto v___jp_3500_;
}
}
}
v___jp_3500_:
{
lean_object* v___x_3503_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 2, v___y_3501_);
v___x_3503_ = v___x_3498_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_id_3494_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_method_3495_);
lean_ctor_set(v_reuseFailAlloc_3505_, 2, v___y_3501_);
v___x_3503_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3491_, v___x_3503_);
return v___x_3504_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeRequest___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3490_ = stack[0].m_obj;
lean_object* v_h_3491_ = stack[1].m_obj;
lean_object* v_r_3492_ = stack[2].m_obj;
lean_object* v_res_3517_;
v_res_3517_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3490_, v_h_3491_, v_r_3492_);
stack->m_obj
 = v_res_3517_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___redArg___boxed(lean_object* v_inst_3518_, lean_object* v_h_3519_, lean_object* v_r_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3518_, v_h_3519_, v_r_3520_);
return v_res_3522_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeRequest(lean_object* v_00_u03b1_3523_, lean_object* v_inst_3524_, lean_object* v_h_3525_, lean_object* v_r_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_IO_FS_Stream_writeRequest___redArg(v_inst_3524_, v_h_3525_, v_r_3526_);
return v___x_3528_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3524_ = stack[1].m_obj;
lean_object* v_h_3525_ = stack[2].m_obj;
lean_object* v_r_3526_ = stack[3].m_obj;
lean_object* v_res_3529_;
v_res_3529_ = l_Lean_IO_FS_Stream_writeRequest(lean_box(0), v_inst_3524_, v_h_3525_, v_r_3526_);
stack->m_obj
 = v_res_3529_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeRequest___boxed(lean_object* v_00_u03b1_3530_, lean_object* v_inst_3531_, lean_object* v_h_3532_, lean_object* v_r_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_IO_FS_Stream_writeRequest(v_00_u03b1_3530_, v_inst_3531_, v_h_3532_, v_r_3533_);
return v_res_3535_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg(lean_object* v_inst_3536_, lean_object* v_h_3537_, lean_object* v_n_3538_){
_start:
{
lean_object* v_method_3540_; lean_object* v_param_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3561_; 
v_method_3540_ = lean_ctor_get(v_n_3538_, 0);
v_param_3541_ = lean_ctor_get(v_n_3538_, 1);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_n_3538_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3543_ = v_n_3538_;
v_isShared_3544_ = v_isSharedCheck_3561_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_param_3541_);
lean_inc(v_method_3540_);
lean_dec(v_n_3538_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3561_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___y_3546_; lean_object* v___x_3551_; 
v___x_3551_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_3536_, v_param_3541_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v___x_3552_; 
lean_dec_ref_known(v___x_3551_, 1);
v___x_3552_ = lean_box(0);
v___y_3546_ = v___x_3552_;
goto v___jp_3545_;
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
v_a_3553_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3551_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3551_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
v___y_3546_ = v___x_3558_;
goto v___jp_3545_;
}
}
}
v___jp_3545_:
{
lean_object* v___x_3548_; 
if (v_isShared_3544_ == 0)
{
lean_ctor_set_tag(v___x_3543_, 1);
lean_ctor_set(v___x_3543_, 1, v___y_3546_);
v___x_3548_ = v___x_3543_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_method_3540_);
lean_ctor_set(v_reuseFailAlloc_3550_, 1, v___y_3546_);
v___x_3548_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3537_, v___x_3548_);
return v___x_3549_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeNotification___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3536_ = stack[0].m_obj;
lean_object* v_h_3537_ = stack[1].m_obj;
lean_object* v_n_3538_ = stack[2].m_obj;
lean_object* v_res_3562_;
v_res_3562_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3536_, v_h_3537_, v_n_3538_);
stack->m_obj
 = v_res_3562_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___redArg___boxed(lean_object* v_inst_3563_, lean_object* v_h_3564_, lean_object* v_n_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3563_, v_h_3564_, v_n_3565_);
return v_res_3567_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeNotification(lean_object* v_00_u03b1_3568_, lean_object* v_inst_3569_, lean_object* v_h_3570_, lean_object* v_n_3571_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_IO_FS_Stream_writeNotification___redArg(v_inst_3569_, v_h_3570_, v_n_3571_);
return v___x_3573_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeNotification_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3569_ = stack[1].m_obj;
lean_object* v_h_3570_ = stack[2].m_obj;
lean_object* v_n_3571_ = stack[3].m_obj;
lean_object* v_res_3574_;
v_res_3574_ = l_Lean_IO_FS_Stream_writeNotification(lean_box(0), v_inst_3569_, v_h_3570_, v_n_3571_);
stack->m_obj
 = v_res_3574_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeNotification___boxed(lean_object* v_00_u03b1_3575_, lean_object* v_inst_3576_, lean_object* v_h_3577_, lean_object* v_n_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_IO_FS_Stream_writeNotification(v_00_u03b1_3575_, v_inst_3576_, v_h_3577_, v_n_3578_);
return v_res_3580_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg(lean_object* v_inst_3581_, lean_object* v_h_3582_, lean_object* v_r_3583_){
_start:
{
lean_object* v_id_3585_; lean_object* v_result_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3595_; 
v_id_3585_ = lean_ctor_get(v_r_3583_, 0);
v_result_3586_ = lean_ctor_get(v_r_3583_, 1);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_r_3583_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3588_ = v_r_3583_;
v_isShared_3589_ = v_isSharedCheck_3595_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_result_3586_);
lean_inc(v_id_3585_);
lean_dec(v_r_3583_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3595_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3590_ = lean_apply_1(v_inst_3581_, v_result_3586_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set_tag(v___x_3588_, 2);
lean_ctor_set(v___x_3588_, 1, v___x_3590_);
v___x_3592_ = v___x_3588_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_id_3585_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3593_; 
v___x_3593_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3582_, v___x_3592_);
return v___x_3593_;
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeResponse___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3581_ = stack[0].m_obj;
lean_object* v_h_3582_ = stack[1].m_obj;
lean_object* v_r_3583_ = stack[2].m_obj;
lean_object* v_res_3596_;
v_res_3596_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3581_, v_h_3582_, v_r_3583_);
stack->m_obj
 = v_res_3596_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___redArg___boxed(lean_object* v_inst_3597_, lean_object* v_h_3598_, lean_object* v_r_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3597_, v_h_3598_, v_r_3599_);
return v_res_3601_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeResponse(lean_object* v_00_u03b1_3602_, lean_object* v_inst_3603_, lean_object* v_h_3604_, lean_object* v_r_3605_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Lean_IO_FS_Stream_writeResponse___redArg(v_inst_3603_, v_h_3604_, v_r_3605_);
return v___x_3607_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeResponse_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3603_ = stack[1].m_obj;
lean_object* v_h_3604_ = stack[2].m_obj;
lean_object* v_r_3605_ = stack[3].m_obj;
lean_object* v_res_3608_;
v_res_3608_ = l_Lean_IO_FS_Stream_writeResponse(lean_box(0), v_inst_3603_, v_h_3604_, v_r_3605_);
stack->m_obj
 = v_res_3608_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponse___boxed(lean_object* v_00_u03b1_3609_, lean_object* v_inst_3610_, lean_object* v_h_3611_, lean_object* v_r_3612_, lean_object* v_a_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_IO_FS_Stream_writeResponse(v_00_u03b1_3609_, v_inst_3610_, v_h_3611_, v_r_3612_);
return v_res_3614_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeResponseError(lean_object* v_h_3615_, lean_object* v_e_3616_){
_start:
{
lean_object* v_id_3618_; uint8_t v_code_3619_; lean_object* v_message_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3629_; 
v_id_3618_ = lean_ctor_get(v_e_3616_, 0);
v_code_3619_ = lean_ctor_get_uint8(v_e_3616_, sizeof(void*)*3);
v_message_3620_ = lean_ctor_get(v_e_3616_, 1);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_e_3616_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_e_3616_, 2);
lean_dec(v_unused_3630_);
v___x_3622_ = v_e_3616_;
v_isShared_3623_ = v_isSharedCheck_3629_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_message_3620_);
lean_inc(v_id_3618_);
lean_dec(v_e_3616_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3629_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3624_; lean_object* v___x_3626_; 
v___x_3624_ = lean_box(0);
if (v_isShared_3623_ == 0)
{
lean_ctor_set_tag(v___x_3622_, 3);
lean_ctor_set(v___x_3622_, 2, v___x_3624_);
v___x_3626_ = v___x_3622_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_id_3618_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_message_3620_);
lean_ctor_set(v_reuseFailAlloc_3628_, 2, v___x_3624_);
lean_ctor_set_uint8(v_reuseFailAlloc_3628_, sizeof(void*)*3, v_code_3619_);
v___x_3626_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___x_3627_; 
v___x_3627_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3615_, v___x_3626_);
return v___x_3627_;
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeResponseError_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3615_ = stack[0].m_obj;
lean_object* v_e_3616_ = stack[1].m_obj;
lean_object* v_res_3631_;
v_res_3631_ = l_Lean_IO_FS_Stream_writeResponseError(v_h_3615_, v_e_3616_);
stack->m_obj
 = v_res_3631_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseError___boxed(lean_object* v_h_3632_, lean_object* v_e_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_IO_FS_Stream_writeResponseError(v_h_3632_, v_e_3633_);
return v_res_3635_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(lean_object* v_inst_3636_, lean_object* v_h_3637_, lean_object* v_e_3638_){
_start:
{
lean_object* v_id_3640_; uint8_t v_code_3641_; lean_object* v_message_3642_; lean_object* v_data_x3f_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3663_; 
v_id_3640_ = lean_ctor_get(v_e_3638_, 0);
v_code_3641_ = lean_ctor_get_uint8(v_e_3638_, sizeof(void*)*3);
v_message_3642_ = lean_ctor_get(v_e_3638_, 1);
v_data_x3f_3643_ = lean_ctor_get(v_e_3638_, 2);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_e_3638_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3645_ = v_e_3638_;
v_isShared_3646_ = v_isSharedCheck_3663_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_data_x3f_3643_);
lean_inc(v_message_3642_);
lean_inc(v_id_3640_);
lean_dec(v_e_3638_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3663_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___y_3648_; 
if (lean_obj_tag(v_data_x3f_3643_) == 0)
{
lean_object* v___x_3653_; 
lean_dec_ref(v_inst_3636_);
v___x_3653_ = lean_box(0);
v___y_3648_ = v___x_3653_;
goto v___jp_3647_;
}
else
{
lean_object* v_val_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3662_; 
v_val_3654_ = lean_ctor_get(v_data_x3f_3643_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_data_x3f_3643_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3656_ = v_data_x3f_3643_;
v_isShared_3657_ = v_isSharedCheck_3662_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_val_3654_);
lean_dec(v_data_x3f_3643_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3662_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3658_; lean_object* v___x_3660_; 
v___x_3658_ = lean_apply_1(v_inst_3636_, v_val_3654_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v___x_3658_);
v___x_3660_ = v___x_3656_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
v___y_3648_ = v___x_3660_;
goto v___jp_3647_;
}
}
}
v___jp_3647_:
{
lean_object* v___x_3650_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 3);
lean_ctor_set(v___x_3645_, 2, v___y_3648_);
v___x_3650_ = v___x_3645_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_id_3640_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_message_3642_);
lean_ctor_set(v_reuseFailAlloc_3652_, 2, v___y_3648_);
lean_ctor_set_uint8(v_reuseFailAlloc_3652_, sizeof(void*)*3, v_code_3641_);
v___x_3650_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_IO_FS_Stream_writeMessage(v_h_3637_, v___x_3650_);
return v___x_3651_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3636_ = stack[0].m_obj;
lean_object* v_h_3637_ = stack[1].m_obj;
lean_object* v_e_3638_ = stack[2].m_obj;
lean_object* v_res_3664_;
v_res_3664_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3636_, v_h_3637_, v_e_3638_);
stack->m_obj
 = v_res_3664_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg___boxed(lean_object* v_inst_3665_, lean_object* v_h_3666_, lean_object* v_e_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3665_, v_h_3666_, v_e_3667_);
return v_res_3669_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData(lean_object* v_00_u03b1_3670_, lean_object* v_inst_3671_, lean_object* v_h_3672_, lean_object* v_e_3673_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData___redArg(v_inst_3671_, v_h_3672_, v_e_3673_);
return v___x_3675_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeResponseErrorWithData_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3671_ = stack[1].m_obj;
lean_object* v_h_3672_ = stack[2].m_obj;
lean_object* v_e_3673_ = stack[3].m_obj;
lean_object* v_res_3676_;
v_res_3676_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData(lean_box(0), v_inst_3671_, v_h_3672_, v_e_3673_);
stack->m_obj
 = v_res_3676_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeResponseErrorWithData___boxed(lean_object* v_00_u03b1_3677_, lean_object* v_inst_3678_, lean_object* v_h_3679_, lean_object* v_e_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lean_IO_FS_Stream_writeResponseErrorWithData(v_00_u03b1_3677_, v_inst_3678_, v_h_3679_, v_e_3680_);
return v_res_3682_;
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
