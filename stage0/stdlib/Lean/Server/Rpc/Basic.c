// Lean compiler output
// Module: Lean.Server.Rpc.Basic
// Imports: public import Init.Dynamic public import Lean.Data.Json.FromToJson.Basic
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
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_USize_fromJson_x3f(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Array_toJson___redArg(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Prod_toJson___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
lean_object* l_Lean_Prod_fromJson_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfExceptTOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfMonadExceptOf___redArg(lean_object*);
lean_object* l_MonadExcept_ofExcept___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_USize_toUInt64___boxed(lean_object*);
lean_object* l_instDecidableEqUSize___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_bignumToJson(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Option_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Array_fromJson_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Option_toJson___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Lsp_instInhabitedRpcRef_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Lsp_instInhabitedRpcRef_default___closed__0;
LEAN_EXPORT size_t l_Lean_Lsp_instInhabitedRpcRef_default;
LEAN_EXPORT size_t l_Lean_Lsp_instInhabitedRpcRef;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqRpcRef_beq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRpcRef_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqRpcRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqRpcRef_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqRpcRef___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqRpcRef___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqRpcRef = (const lean_object*)&l_Lean_Lsp_instBEqRpcRef___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableRpcRef_hash(size_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRpcRef_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instHashableRpcRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instHashableRpcRef_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instHashableRpcRef___closed__0 = (const lean_object*)&l_Lean_Lsp_instHashableRpcRef___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instHashableRpcRef = (const lean_object*)&l_Lean_Lsp_instHashableRpcRef___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringRpcRef___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringRpcRef___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToStringRpcRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToStringRpcRef___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToStringRpcRef___closed__0 = (const lean_object*)&l_Lean_Lsp_instToStringRpcRef___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToStringRpcRef = (const lean_object*)&l_Lean_Lsp_instToStringRpcRef___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "v1"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "v0"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3_value;
static const lean_string_object l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__4_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonRpcWireFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat = (const lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3_value)}};
static const lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2_value)}};
static const lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonRpcWireFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRpcWireFormat_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonRpcWireFormat___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonRpcWireFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonRpcWireFormat = (const lean_object*)&l_Lean_Lsp_instToJsonRpcWireFormat___closed__0_value;
static const lean_string_object l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0 = (const lean_object*)&l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0_value;
static const lean_string_object l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "__rpcref"};
static const lean_object* l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1 = (const lean_object*)&l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_refFieldName(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_refFieldName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(1ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_freshWithRpcRefId;
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_rpcStoreRef___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_rpcStoreRef___redArg___closed__0 = (const lean_object*)&l_Lean_Server_rpcStoreRef___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Server_rpcStoreRef___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_rpcStoreRef___redArg___closed__1;
static const lean_string_object l_Lean_Server_rpcStoreRef___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.Rpc.Basic"};
static const lean_object* l_Lean_Server_rpcStoreRef___redArg___closed__2 = (const lean_object*)&l_Lean_Server_rpcStoreRef___redArg___closed__2_value;
static const lean_string_object l_Lean_Server_rpcStoreRef___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Server.rpcStoreRef"};
static const lean_object* l_Lean_Server_rpcStoreRef___redArg___closed__3 = (const lean_object*)&l_Lean_Server_rpcStoreRef___redArg___closed__3_value;
static const lean_string_object l_Lean_Server_rpcStoreRef___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Found object ID in `refsById` but not in `aliveRefs`."};
static const lean_object* l_Lean_Server_rpcStoreRef___redArg___closed__4 = (const lean_object*)&l_Lean_Server_rpcStoreRef___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Server_rpcStoreRef___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_rpcStoreRef___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_rpcGetRef___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "RPC call type mismatch in reference '"};
static const lean_object* l_Lean_Server_rpcGetRef___redArg___closed__0 = (const lean_object*)&l_Lean_Server_rpcGetRef___redArg___closed__0_value;
static const lean_string_object l_Lean_Server_rpcGetRef___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "'\nexpected '"};
static const lean_object* l_Lean_Server_rpcGetRef___redArg___closed__1 = (const lean_object*)&l_Lean_Server_rpcGetRef___redArg___closed__1_value;
static const lean_string_object l_Lean_Server_rpcGetRef___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "', "};
static const lean_object* l_Lean_Server_rpcGetRef___redArg___closed__2 = (const lean_object*)&l_Lean_Server_rpcGetRef___redArg___closed__2_value;
static const lean_string_object l_Lean_Server_rpcGetRef___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "got '"};
static const lean_object* l_Lean_Server_rpcGetRef___redArg___closed__3 = (const lean_object*)&l_Lean_Server_rpcGetRef___redArg___closed__3_value;
static const lean_string_object l_Lean_Server_rpcGetRef___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Server_rpcGetRef___redArg___closed__4 = (const lean_object*)&l_Lean_Server_rpcGetRef___redArg___closed__4_value;
static const lean_string_object l_Lean_Server_rpcGetRef___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "RPC reference '"};
static const lean_object* l_Lean_Server_rpcGetRef___redArg___closed__5 = (const lean_object*)&l_Lean_Server_rpcGetRef___redArg___closed__5_value;
static const lean_string_object l_Lean_Server_rpcGetRef___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "' is not valid"};
static const lean_object* l_Lean_Server_rpcGetRef___redArg___closed__6 = (const lean_object*)&l_Lean_Server_rpcGetRef___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(lean_object*, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__0 = (const lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__0_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__1 = (const lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__1_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__2 = (const lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__2_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__3 = (const lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__3_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__4 = (const lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__4_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__5 = (const lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__5_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__6 = (const lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__0_value),((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__1_value)}};
static const lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__7 = (const lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__7_value),((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__2_value),((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__3_value),((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__4_value),((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__5_value)}};
static const lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__8 = (const lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__8_value),((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__6_value)}};
static const lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9 = (const lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20;
static lean_once_cell_t l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21;
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instRpcEncodableOption___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Server_instRpcEncodableOption___redArg___closed__0 = (const lean_object*)&l_Lean_Server_instRpcEncodableOption___redArg___closed__0_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableOption___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instRpcEncodableOption___redArg___closed__1 = (const lean_object*)&l_Lean_Server_instRpcEncodableOption___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instRpcEncodableArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value)} };
static const lean_object* l_Lean_Server_instRpcEncodableArray___redArg___closed__0 = (const lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__0_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value)} };
static const lean_object* l_Lean_Server_instRpcEncodableArray___redArg___closed__1 = (const lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__1_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value)} };
static const lean_object* l_Lean_Server_instRpcEncodableArray___redArg___closed__2 = (const lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__2_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableArray___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value)} };
static const lean_object* l_Lean_Server_instRpcEncodableArray___redArg___closed__3 = (const lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__3_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableArray___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value)} };
static const lean_object* l_Lean_Server_instRpcEncodableArray___redArg___closed__4 = (const lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Server_instRpcEncodableArray___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__4_value),((lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__0_value)}};
static const lean_object* l_Lean_Server_instRpcEncodableArray___redArg___closed__5 = (const lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__5_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableArray___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value)} };
static const lean_object* l_Lean_Server_instRpcEncodableArray___redArg___closed__6 = (const lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Server_instRpcEncodableArray___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__5_value),((lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__6_value),((lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__1_value),((lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__2_value),((lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__3_value)}};
static const lean_object* l_Lean_Server_instRpcEncodableArray___redArg___closed__7 = (const lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__7_value;
static const lean_closure_object l_Lean_Server_instRpcEncodableArray___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9_value)} };
static const lean_object* l_Lean_Server_instRpcEncodableArray___redArg___closed__8 = (const lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Server_instRpcEncodableArray___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__7_value),((lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__8_value)}};
static const lean_object* l_Lean_Server_instRpcEncodableArray___redArg___closed__9 = (const lean_object*)&l_Lean_Server_instRpcEncodableArray___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_USize_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0 = (const lean_object*)&l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName(lean_object*, lean_object*);
static size_t _init_l_Lean_Lsp_instInhabitedRpcRef_default___closed__0(void){
_start:
{
lean_object* v___x_1_; size_t v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_usize_of_nat(v___x_1_);
return v___x_2_;
}
}
static size_t _init_l_Lean_Lsp_instInhabitedRpcRef_default(void){
_start:
{
size_t v___x_3_; 
v___x_3_ = lean_usize_once(&l_Lean_Lsp_instInhabitedRpcRef_default___closed__0, &l_Lean_Lsp_instInhabitedRpcRef_default___closed__0_once, _init_l_Lean_Lsp_instInhabitedRpcRef_default___closed__0);
return v___x_3_;
}
}
static size_t _init_l_Lean_Lsp_instInhabitedRpcRef(void){
_start:
{
size_t v___x_4_; 
v___x_4_ = l_Lean_Lsp_instInhabitedRpcRef_default;
return v___x_4_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqRpcRef_beq(size_t v_x_5_, size_t v_x_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_usize_dec_eq(v_x_5_, v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqRpcRef_beq___boxed(lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
size_t v_x_26__boxed_10_; size_t v_x_27__boxed_11_; uint8_t v_res_12_; lean_object* v_r_13_; 
v_x_26__boxed_10_ = lean_unbox_usize(v_x_8_);
lean_dec(v_x_8_);
v_x_27__boxed_11_ = lean_unbox_usize(v_x_9_);
lean_dec(v_x_9_);
v_res_12_ = l_Lean_Lsp_instBEqRpcRef_beq(v_x_26__boxed_10_, v_x_27__boxed_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint64_t l_Lean_Lsp_instHashableRpcRef_hash(size_t v_x_16_){
_start:
{
uint64_t v___x_17_; uint64_t v___x_18_; uint64_t v___x_19_; 
v___x_17_ = 0ULL;
v___x_18_ = lean_usize_to_uint64(v_x_16_);
v___x_19_ = lean_uint64_mix_hash(v___x_17_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instHashableRpcRef_hash___boxed(lean_object* v_x_20_){
_start:
{
size_t v_x_26__boxed_21_; uint64_t v_res_22_; lean_object* v_r_23_; 
v_x_26__boxed_21_ = lean_unbox_usize(v_x_20_);
lean_dec(v_x_20_);
v_res_22_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_26__boxed_21_);
v_r_23_ = lean_box_uint64(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringRpcRef___lam__0(size_t v_r_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_usize_to_nat(v_r_26_);
v___x_28_ = l_Nat_reprFast(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToStringRpcRef___lam__0___boxed(lean_object* v_r_29_){
_start:
{
size_t v_r_boxed_30_; lean_object* v_res_31_; 
v_r_boxed_30_ = lean_unbox_usize(v_r_29_);
lean_dec(v_r_29_);
v_res_31_ = l_Lean_Lsp_instToStringRpcRef___lam__0(v_r_boxed_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorIdx(uint8_t v_x_34_){
_start:
{
if (v_x_34_ == 0)
{
lean_object* v___x_35_; 
v___x_35_ = lean_unsigned_to_nat(0u);
return v___x_35_;
}
else
{
lean_object* v___x_36_; 
v___x_36_ = lean_unsigned_to_nat(1u);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorIdx___boxed(lean_object* v_x_37_){
_start:
{
uint8_t v_x_boxed_38_; lean_object* v_res_39_; 
v_x_boxed_38_ = lean_unbox(v_x_37_);
v_res_39_ = l_Lean_Lsp_RpcWireFormat_ctorIdx(v_x_boxed_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim___redArg(lean_object* v_k_40_){
_start:
{
lean_inc(v_k_40_);
return v_k_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim___redArg___boxed(lean_object* v_k_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Lsp_RpcWireFormat_ctorElim___redArg(v_k_41_);
lean_dec(v_k_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim(lean_object* v_motive_43_, lean_object* v_ctorIdx_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_k_47_){
_start:
{
lean_inc(v_k_47_);
return v_k_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_ctorElim___boxed(lean_object* v_motive_48_, lean_object* v_ctorIdx_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_k_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Lean_Lsp_RpcWireFormat_ctorElim(v_motive_48_, v_ctorIdx_49_, v_t_boxed_53_, v_h_51_, v_k_52_);
lean_dec(v_k_52_);
lean_dec(v_ctorIdx_49_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim___redArg(lean_object* v_v0_55_){
_start:
{
lean_inc(v_v0_55_);
return v_v0_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim___redArg___boxed(lean_object* v_v0_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Lsp_RpcWireFormat_v0_elim___redArg(v_v0_56_);
lean_dec(v_v0_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_v0_61_){
_start:
{
lean_inc(v_v0_61_);
return v_v0_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v0_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_v0_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = l_Lean_Lsp_RpcWireFormat_v0_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_v0_65_);
lean_dec(v_v0_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___redArg(lean_object* v_v1_68_){
_start:
{
lean_inc(v_v1_68_);
return v_v1_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___redArg___boxed(lean_object* v_v1_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Lsp_RpcWireFormat_v1_elim___redArg(v_v1_69_);
lean_dec(v_v1_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_v1_74_){
_start:
{
lean_inc(v_v1_74_);
return v_v1_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_v1_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_v1_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = l_Lean_Lsp_RpcWireFormat_v1_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_v1_78_);
lean_dec(v_v1_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(lean_object* v_json_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Json_getTag_x3f(v_json_95_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v___x_97_; 
v___x_97_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__1));
return v___x_97_;
}
else
{
lean_object* v_val_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_val_98_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_val_98_);
lean_dec_ref_known(v___x_96_, 1);
v___x_99_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__2));
v___x_100_ = lean_string_dec_eq(v_val_98_, v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__3));
v___x_102_ = lean_string_dec_eq(v_val_98_, v___x_101_);
lean_dec(v_val_98_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
v___x_103_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__5));
return v___x_103_;
}
else
{
lean_object* v___x_104_; 
v___x_104_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__6));
return v___x_104_;
}
}
else
{
lean_object* v___x_105_; 
lean_dec(v_val_98_);
v___x_105_ = ((lean_object*)(l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson___closed__7));
return v___x_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson(uint8_t v_x_112_){
_start:
{
if (v_x_112_ == 0)
{
lean_object* v___x_113_; 
v___x_113_ = ((lean_object*)(l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__0));
return v___x_113_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = ((lean_object*)(l_Lean_Lsp_instToJsonRpcWireFormat_toJson___closed__1));
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson___boxed(lean_object* v_x_115_){
_start:
{
uint8_t v_x_44__boxed_116_; lean_object* v_res_117_; 
v_x_44__boxed_116_ = lean_unbox(v_x_115_);
v_res_117_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v_x_44__boxed_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_refFieldName(uint8_t v_x_122_){
_start:
{
if (v_x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
return v___x_123_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_RpcWireFormat_refFieldName___boxed(lean_object* v_x_125_){
_start:
{
uint8_t v_x_22__boxed_126_; lean_object* v_res_127_; 
v_x_22__boxed_126_ = lean_unbox(v_x_125_);
v_res_127_ = l_Lean_Lsp_RpcWireFormat_refFieldName(v_x_22__boxed_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default___redArg(lean_object* v_inst_128_){
_start:
{
size_t v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_usize_once(&l_Lean_Lsp_instInhabitedRpcRef_default___closed__0, &l_Lean_Lsp_instInhabitedRpcRef_default___closed__0_once, _init_l_Lean_Lsp_instInhabitedRpcRef_default___closed__0);
v___x_130_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_130_, 0, v_inst_128_);
lean_ctor_set_usize(v___x_130_, 1, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef_default(lean_object* v_00_u03b1_131_, lean_object* v_inst_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef___redArg(lean_object* v_inst_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedWithRpcRef(lean_object* v_a_136_, lean_object* v_inst_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Server_instInhabitedWithRpcRef_default___redArg(v_inst_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = ((lean_object*)(l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn___boxed__const__1_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_));
v___x_143_ = lean_st_mk_ref(v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2____boxed(lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_();
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___redArg(lean_object* v_val_147_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; size_t v___x_151_; size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; size_t v___x_157_; 
v___x_149_ = l_Lean_Server_freshWithRpcRefId;
v___x_150_ = lean_st_ref_take(v___x_149_);
v___x_151_ = ((size_t)1ULL);
v___x_152_ = lean_unbox_usize(v___x_150_);
v___x_153_ = lean_usize_add(v___x_152_, v___x_151_);
v___x_154_ = lean_box_usize(v___x_153_);
v___x_155_ = lean_st_ref_set(v___x_149_, v___x_154_);
v___x_156_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_156_, 0, v_val_147_);
v___x_157_ = lean_unbox_usize(v___x_150_);
lean_dec(v___x_150_);
lean_ctor_set_usize(v___x_156_, 1, v___x_157_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___redArg___boxed(lean_object* v_val_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Server_WithRpcRef_mk___redArg(v_val_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk(lean_object* v_00_u03b1_161_, lean_object* v_val_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Server_WithRpcRef_mk___redArg(v_val_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_WithRpcRef_mk___boxed(lean_object* v_00_u03b1_165_, lean_object* v_val_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Server_WithRpcRef_mk(v_00_u03b1_165_, v_val_166_);
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___closed__1(void){
_start:
{
lean_object* v___x_170_; lean_object* v___f_171_; 
v___x_170_ = lean_alloc_closure((void*)(l_instDecidableEqUSize___boxed), 2, 0);
v___f_171_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_171_, 0, v___x_170_);
return v___f_171_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___closed__5(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_175_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__4));
v___x_176_ = lean_unsigned_to_nat(15u);
v___x_177_ = lean_unsigned_to_nat(132u);
v___x_178_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__3));
v___x_179_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__2));
v___x_180_ = l_mkPanicMessageWithDecl(v___x_179_, v___x_178_, v___x_177_, v___x_176_, v___x_175_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Server_rpcStoreRef___redArg___boxed__const__1(void){
_start:
{
size_t v___x_181_; lean_object* v___x_182_; 
v___x_181_ = l_Lean_Lsp_instInhabitedRpcRef_default;
v___x_182_ = lean_box_usize(v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___redArg(lean_object* v_inst_183_, lean_object* v_obj_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_aliveRefs_186_; lean_object* v_refsById_187_; size_t v_nextRef_188_; uint8_t v_wireFormat_189_; lean_object* v_val_190_; size_t v_id_191_; lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___f_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_aliveRefs_186_ = lean_ctor_get(v_a_185_, 0);
v_refsById_187_ = lean_ctor_get(v_a_185_, 1);
v_nextRef_188_ = lean_ctor_get_usize(v_a_185_, 2);
v_wireFormat_189_ = lean_ctor_get_uint8(v_a_185_, sizeof(void*)*3);
v_val_190_ = lean_ctor_get(v_obj_184_, 0);
v_id_191_ = lean_ctor_get_usize(v_obj_184_, 1);
v___f_192_ = ((lean_object*)(l_Lean_Server_rpcStoreRef___redArg___closed__0));
v___x_193_ = ((lean_object*)(l_Lean_Lsp_instBEqRpcRef___closed__0));
v___x_194_ = ((lean_object*)(l_Lean_Lsp_instHashableRpcRef___closed__0));
v___f_195_ = lean_obj_once(&l_Lean_Server_rpcStoreRef___redArg___closed__1, &l_Lean_Server_rpcStoreRef___redArg___closed__1_once, _init_l_Lean_Server_rpcStoreRef___redArg___closed__1);
v___x_196_ = lean_box_usize(v_id_191_);
v___x_197_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_195_, v___f_192_, v_refsById_187_, v___x_196_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_216_; 
lean_inc_ref(v_refsById_187_);
lean_inc_ref(v_aliveRefs_186_);
v_isSharedCheck_216_ = !lean_is_exclusive(v_a_185_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; lean_object* v_unused_218_; 
v_unused_217_ = lean_ctor_get(v_a_185_, 1);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_a_185_, 0);
lean_dec(v_unused_218_);
v___x_199_ = v_a_185_;
v_isShared_200_ = v_isSharedCheck_216_;
goto v_resetjp_198_;
}
else
{
lean_dec(v_a_185_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_216_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; size_t v___x_209_; size_t v___x_210_; lean_object* v___x_212_; 
lean_inc(v_val_190_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v_inst_183_);
lean_ctor_set(v___x_201_, 1, v_val_190_);
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
lean_ctor_set_usize(v___x_203_, 2, v_id_191_);
v___x_204_ = lean_box_usize(v_nextRef_188_);
v___x_205_ = l_Lean_PersistentHashMap_insert___redArg(v___x_193_, v___x_194_, v_aliveRefs_186_, v___x_204_, v___x_203_);
v___x_206_ = lean_box_usize(v_id_191_);
v___x_207_ = lean_box_usize(v_nextRef_188_);
v___x_208_ = l_Lean_PersistentHashMap_insert___redArg(v___f_195_, v___f_192_, v_refsById_187_, v___x_206_, v___x_207_);
v___x_209_ = ((size_t)1ULL);
v___x_210_ = lean_usize_add(v_nextRef_188_, v___x_209_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v___x_208_);
lean_ctor_set(v___x_199_, 0, v___x_205_);
v___x_212_ = v___x_199_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_215_, sizeof(void*)*3, v_wireFormat_189_);
v___x_212_ = v_reuseFailAlloc_215_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_ctor_set_usize(v___x_212_, 2, v___x_210_);
v___x_213_ = lean_box_usize(v_nextRef_188_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_212_);
return v___x_214_;
}
}
}
else
{
lean_object* v_val_219_; lean_object* v___x_220_; 
lean_dec(v_inst_183_);
v_val_219_ = lean_ctor_get(v___x_197_, 0);
lean_inc_n(v_val_219_, 2);
lean_dec_ref_known(v___x_197_, 1);
v___x_220_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_193_, v___x_194_, v_aliveRefs_186_, v_val_219_);
if (lean_obj_tag(v___x_220_) == 1)
{
lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_242_; 
lean_inc_ref(v_refsById_187_);
lean_inc_ref(v_aliveRefs_186_);
v_isSharedCheck_242_ = !lean_is_exclusive(v_a_185_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; lean_object* v_unused_244_; 
v_unused_243_ = lean_ctor_get(v_a_185_, 1);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_a_185_, 0);
lean_dec(v_unused_244_);
v___x_222_ = v_a_185_;
v_isShared_223_ = v_isSharedCheck_242_;
goto v_resetjp_221_;
}
else
{
lean_dec(v_a_185_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_242_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v_val_224_; lean_object* v_obj_225_; size_t v_id_226_; lean_object* v_rc_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_241_; 
v_val_224_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_220_, 1);
v_obj_225_ = lean_ctor_get(v_val_224_, 0);
v_id_226_ = lean_ctor_get_usize(v_val_224_, 2);
v_rc_227_ = lean_ctor_get(v_val_224_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_val_224_);
if (v_isSharedCheck_241_ == 0)
{
v___x_229_ = v_val_224_;
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_rc_227_);
lean_inc(v_obj_225_);
lean_dec(v_val_224_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_241_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_add(v_rc_227_, v___x_231_);
lean_dec(v_rc_227_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___x_232_);
v___x_234_ = v___x_229_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_obj_225_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_232_);
lean_ctor_set_usize(v_reuseFailAlloc_240_, 2, v_id_226_);
v___x_234_ = v_reuseFailAlloc_240_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
lean_inc(v_val_219_);
v___x_235_ = l_Lean_PersistentHashMap_insert___redArg(v___x_193_, v___x_194_, v_aliveRefs_186_, v_val_219_, v___x_234_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_235_);
v___x_237_ = v___x_222_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_refsById_187_);
lean_ctor_set_usize(v_reuseFailAlloc_239_, 2, v_nextRef_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, sizeof(void*)*3, v_wireFormat_189_);
v___x_237_ = v_reuseFailAlloc_239_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v_val_219_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
return v___x_238_;
}
}
}
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v___x_220_);
lean_dec(v_val_219_);
v___x_245_ = lean_obj_once(&l_Lean_Server_rpcStoreRef___redArg___closed__5, &l_Lean_Server_rpcStoreRef___redArg___closed__5_once, _init_l_Lean_Server_rpcStoreRef___redArg___closed__5);
v___x_246_ = l_Lean_Server_rpcStoreRef___redArg___boxed__const__1;
v___x_247_ = l_panic___redArg(v___x_246_, v___x_245_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_a_185_);
return v___x_248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___redArg___boxed(lean_object* v_inst_249_, lean_object* v_obj_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_249_, v_obj_250_, v_a_251_);
lean_dec_ref(v_obj_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef(lean_object* v_00_u03b1_253_, lean_object* v_inst_254_, lean_object* v_obj_255_, lean_object* v_a_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_254_, v_obj_255_, v_a_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcStoreRef___boxed(lean_object* v_00_u03b1_258_, lean_object* v_inst_259_, lean_object* v_obj_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Server_rpcStoreRef(v_00_u03b1_258_, v_inst_259_, v_obj_260_, v_a_261_);
lean_dec_ref(v_obj_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___redArg(lean_object* v_inst_270_, size_t v_r_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_aliveRefs_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_aliveRefs_273_ = lean_ctor_get(v_a_272_, 0);
v___x_274_ = ((lean_object*)(l_Lean_Lsp_instBEqRpcRef___closed__0));
v___x_275_ = ((lean_object*)(l_Lean_Lsp_instHashableRpcRef___closed__0));
v___x_276_ = lean_box_usize(v_r_271_);
v___x_277_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_274_, v___x_275_, v_aliveRefs_273_, v___x_276_);
if (lean_obj_tag(v___x_277_) == 1)
{
lean_object* v_val_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_315_; 
v_val_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_315_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_315_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_val_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_315_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_obj_282_; size_t v_id_283_; lean_object* v___x_284_; 
v_obj_282_ = lean_ctor_get(v_val_278_, 0);
lean_inc(v_obj_282_);
v_id_283_ = lean_ctor_get_usize(v_val_278_, 2);
lean_dec(v_val_278_);
v___x_284_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_obj_282_, v_inst_270_);
if (lean_obj_tag(v___x_284_) == 1)
{
lean_object* v_val_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
lean_dec(v_obj_282_);
lean_del_object(v___x_280_);
lean_dec(v_inst_270_);
v_val_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_293_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_val_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_289_, 0, v_val_285_);
lean_ctor_set_usize(v___x_289_, 1, v_id_283_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_289_);
v___x_291_ = v___x_287_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec(v___x_284_);
v___x_294_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__0));
v___x_295_ = lean_usize_to_nat(v_r_271_);
v___x_296_ = l_Nat_reprFast(v___x_295_);
v___x_297_ = lean_string_append(v___x_294_, v___x_296_);
lean_dec_ref(v___x_296_);
v___x_298_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__1));
v___x_299_ = lean_string_append(v___x_297_, v___x_298_);
v___x_300_ = 1;
v___x_301_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_inst_270_, v___x_300_);
v___x_302_ = lean_string_append(v___x_299_, v___x_301_);
lean_dec_ref(v___x_301_);
v___x_303_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__2));
v___x_304_ = lean_string_append(v___x_302_, v___x_303_);
v___x_305_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__3));
v___x_306_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_obj_282_);
lean_dec(v_obj_282_);
v___x_307_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_306_, v___x_300_);
v___x_308_ = lean_string_append(v___x_305_, v___x_307_);
lean_dec_ref(v___x_307_);
v___x_309_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__4));
v___x_310_ = lean_string_append(v___x_308_, v___x_309_);
v___x_311_ = lean_string_append(v___x_304_, v___x_310_);
lean_dec_ref(v___x_310_);
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 0);
lean_ctor_set(v___x_280_, 0, v___x_311_);
v___x_313_ = v___x_280_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v___x_277_);
lean_dec(v_inst_270_);
v___x_316_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__5));
v___x_317_ = lean_usize_to_nat(v_r_271_);
v___x_318_ = l_Nat_reprFast(v___x_317_);
v___x_319_ = lean_string_append(v___x_316_, v___x_318_);
lean_dec_ref(v___x_318_);
v___x_320_ = ((lean_object*)(l_Lean_Server_rpcGetRef___redArg___closed__6));
v___x_321_ = lean_string_append(v___x_319_, v___x_320_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___redArg___boxed(lean_object* v_inst_323_, lean_object* v_r_324_, lean_object* v_a_325_){
_start:
{
size_t v_r_boxed_326_; lean_object* v_res_327_; 
v_r_boxed_326_ = lean_unbox_usize(v_r_324_);
lean_dec(v_r_324_);
v_res_327_ = l_Lean_Server_rpcGetRef___redArg(v_inst_323_, v_r_boxed_326_, v_a_325_);
lean_dec_ref(v_a_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef(lean_object* v_00_u03b1_328_, lean_object* v_inst_329_, size_t v_r_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Server_rpcGetRef___redArg(v_inst_329_, v_r_330_, v_a_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcGetRef___boxed(lean_object* v_00_u03b1_333_, lean_object* v_inst_334_, lean_object* v_r_335_, lean_object* v_a_336_){
_start:
{
size_t v_r_boxed_337_; lean_object* v_res_338_; 
v_r_boxed_337_ = lean_unbox_usize(v_r_335_);
lean_dec(v_r_335_);
v_res_338_ = l_Lean_Server_rpcGetRef(v_00_u03b1_333_, v_inst_334_, v_r_boxed_337_, v_a_336_);
lean_dec_ref(v_a_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(lean_object* v_xs_339_, size_t v_v_340_, lean_object* v_i_341_){
_start:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_array_get_size(v_xs_339_);
v___x_343_ = lean_nat_dec_lt(v_i_341_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_dec(v_i_341_);
v___x_344_ = lean_box(0);
return v___x_344_;
}
else
{
lean_object* v___x_345_; size_t v___x_346_; uint8_t v___x_347_; 
v___x_345_ = lean_array_fget_borrowed(v_xs_339_, v_i_341_);
v___x_346_ = lean_unbox_usize(v___x_345_);
v___x_347_ = lean_usize_dec_eq(v___x_346_, v_v_340_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_i_341_, v___x_348_);
lean_dec(v_i_341_);
v_i_341_ = v___x_349_;
goto _start;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_i_341_);
return v___x_351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11___boxed(lean_object* v_xs_352_, lean_object* v_v_353_, lean_object* v_i_354_){
_start:
{
size_t v_v_boxed_355_; lean_object* v_res_356_; 
v_v_boxed_355_ = lean_unbox_usize(v_v_353_);
lean_dec(v_v_353_);
v_res_356_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(v_xs_352_, v_v_boxed_355_, v_i_354_);
lean_dec_ref(v_xs_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(lean_object* v_xs_357_, size_t v_v_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8_spec__11(v_xs_357_, v_v_358_, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8___boxed(lean_object* v_xs_361_, lean_object* v_v_362_){
_start:
{
size_t v_v_boxed_363_; lean_object* v_res_364_; 
v_v_boxed_363_ = lean_unbox_usize(v_v_362_);
lean_dec(v_v_362_);
v_res_364_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_xs_361_, v_v_boxed_363_);
lean_dec_ref(v_xs_361_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(lean_object* v_x_365_, size_t v_x_366_, size_t v_x_367_){
_start:
{
if (lean_obj_tag(v_x_365_) == 0)
{
lean_object* v_es_368_; lean_object* v___x_369_; size_t v___x_370_; size_t v___x_371_; lean_object* v_j_372_; lean_object* v_entry_373_; 
v_es_368_ = lean_ctor_get(v_x_365_, 0);
v___x_369_ = lean_box(2);
v___x_370_ = ((size_t)31ULL);
v___x_371_ = lean_usize_land(v_x_366_, v___x_370_);
v_j_372_ = lean_usize_to_nat(v___x_371_);
v_entry_373_ = lean_array_get(v___x_369_, v_es_368_, v_j_372_);
switch(lean_obj_tag(v_entry_373_))
{
case 0:
{
lean_object* v_key_374_; size_t v___x_375_; uint8_t v___x_376_; 
v_key_374_ = lean_ctor_get(v_entry_373_, 0);
lean_inc(v_key_374_);
lean_dec_ref_known(v_entry_373_, 2);
v___x_375_ = lean_unbox_usize(v_key_374_);
lean_dec(v_key_374_);
v___x_376_ = lean_usize_dec_eq(v_x_367_, v___x_375_);
if (v___x_376_ == 0)
{
lean_dec(v_j_372_);
return v_x_365_;
}
else
{
lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_384_; 
lean_inc_ref(v_es_368_);
v_isSharedCheck_384_ = !lean_is_exclusive(v_x_365_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v_x_365_, 0);
lean_dec(v_unused_385_);
v___x_378_ = v_x_365_;
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
else
{
lean_dec(v_x_365_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_384_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_380_ = lean_array_set(v_es_368_, v_j_372_, v___x_369_);
lean_dec(v_j_372_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_380_);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
case 1:
{
lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_420_; 
lean_inc_ref(v_es_368_);
v_isSharedCheck_420_ = !lean_is_exclusive(v_x_365_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v_x_365_, 0);
lean_dec(v_unused_421_);
v___x_387_ = v_x_365_;
v_isShared_388_ = v_isSharedCheck_420_;
goto v_resetjp_386_;
}
else
{
lean_dec(v_x_365_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_420_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_node_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_419_; 
v_node_389_ = lean_ctor_get(v_entry_373_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_entry_373_);
if (v_isSharedCheck_419_ == 0)
{
v___x_391_ = v_entry_373_;
v_isShared_392_ = v_isSharedCheck_419_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_node_389_);
lean_dec(v_entry_373_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_419_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
size_t v___x_393_; lean_object* v_entries_394_; size_t v___x_395_; lean_object* v_newNode_396_; lean_object* v___x_397_; 
v___x_393_ = ((size_t)5ULL);
v_entries_394_ = lean_array_set(v_es_368_, v_j_372_, v___x_369_);
v___x_395_ = lean_usize_shift_right(v_x_366_, v___x_393_);
v_newNode_396_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_node_389_, v___x_395_, v_x_367_);
lean_inc_ref(v_newNode_396_);
v___x_397_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_396_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v___x_399_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v_newNode_396_);
v___x_399_ = v___x_391_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_newNode_396_);
v___x_399_ = v_reuseFailAlloc_404_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_array_set(v_entries_394_, v_j_372_, v___x_399_);
lean_dec(v_j_372_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_400_);
v___x_402_ = v___x_387_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
else
{
lean_object* v_val_405_; lean_object* v_fst_406_; lean_object* v_snd_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_418_; 
lean_dec_ref(v_newNode_396_);
lean_del_object(v___x_391_);
v_val_405_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_val_405_);
lean_dec_ref_known(v___x_397_, 1);
v_fst_406_ = lean_ctor_get(v_val_405_, 0);
v_snd_407_ = lean_ctor_get(v_val_405_, 1);
v_isSharedCheck_418_ = !lean_is_exclusive(v_val_405_);
if (v_isSharedCheck_418_ == 0)
{
v___x_409_ = v_val_405_;
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_snd_407_);
lean_inc(v_fst_406_);
lean_dec(v_val_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_fst_406_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_snd_407_);
v___x_412_ = v_reuseFailAlloc_417_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = lean_array_set(v_entries_394_, v_j_372_, v___x_412_);
lean_dec(v_j_372_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_413_);
v___x_415_ = v___x_387_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_372_);
return v_x_365_;
}
}
}
else
{
lean_object* v_ks_422_; lean_object* v_vs_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_437_; 
v_ks_422_ = lean_ctor_get(v_x_365_, 0);
v_vs_423_ = lean_ctor_get(v_x_365_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_365_);
if (v_isSharedCheck_437_ == 0)
{
v___x_425_ = v_x_365_;
v_isShared_426_ = v_isSharedCheck_437_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_vs_423_);
lean_inc(v_ks_422_);
lean_dec(v_x_365_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_437_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; 
v___x_427_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4_spec__8(v_ks_422_, v_x_367_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v___x_429_; 
if (v_isShared_426_ == 0)
{
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_ks_422_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_vs_423_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
else
{
lean_object* v_val_431_; lean_object* v_keys_x27_432_; lean_object* v_vals_x27_433_; lean_object* v___x_435_; 
v_val_431_ = lean_ctor_get(v___x_427_, 0);
lean_inc_n(v_val_431_, 2);
lean_dec_ref_known(v___x_427_, 1);
v_keys_x27_432_ = l_Array_eraseIdx___redArg(v_ks_422_, v_val_431_);
v_vals_x27_433_ = l_Array_eraseIdx___redArg(v_vs_423_, v_val_431_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v_vals_x27_433_);
lean_ctor_set(v___x_425_, 0, v_keys_x27_432_);
v___x_435_ = v___x_425_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_keys_x27_432_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_vals_x27_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg___boxed(lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
size_t v_x_1696__boxed_441_; size_t v_x_1697__boxed_442_; lean_object* v_res_443_; 
v_x_1696__boxed_441_ = lean_unbox_usize(v_x_439_);
lean_dec(v_x_439_);
v_x_1697__boxed_442_ = lean_unbox_usize(v_x_440_);
lean_dec(v_x_440_);
v_res_443_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_438_, v_x_1696__boxed_441_, v_x_1697__boxed_442_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(lean_object* v_x_444_, size_t v_x_445_){
_start:
{
uint64_t v___x_446_; size_t v_h_447_; lean_object* v___x_448_; 
v___x_446_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_445_);
v_h_447_ = lean_uint64_to_usize(v___x_446_);
v___x_448_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_444_, v_h_447_, v_x_445_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg___boxed(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
size_t v_x_1834__boxed_451_; lean_object* v_res_452_; 
v_x_1834__boxed_451_ = lean_unbox_usize(v_x_450_);
lean_dec(v_x_450_);
v_res_452_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_449_, v_x_1834__boxed_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_453_, lean_object* v_vals_454_, lean_object* v_i_455_, size_t v_k_456_){
_start:
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_array_get_size(v_keys_453_);
v___x_458_ = lean_nat_dec_lt(v_i_455_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v_i_455_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v_k_x27_460_; size_t v___x_461_; uint8_t v___x_462_; 
v_k_x27_460_ = lean_array_fget_borrowed(v_keys_453_, v_i_455_);
v___x_461_ = lean_unbox_usize(v_k_x27_460_);
v___x_462_ = lean_usize_dec_eq(v_k_456_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(1u);
v___x_464_ = lean_nat_add(v_i_455_, v___x_463_);
lean_dec(v_i_455_);
v_i_455_ = v___x_464_;
goto _start;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_array_fget_borrowed(v_vals_454_, v_i_455_);
lean_dec(v_i_455_);
lean_inc(v___x_466_);
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_468_, lean_object* v_vals_469_, lean_object* v_i_470_, lean_object* v_k_471_){
_start:
{
size_t v_k_boxed_472_; lean_object* v_res_473_; 
v_k_boxed_472_ = lean_unbox_usize(v_k_471_);
lean_dec(v_k_471_);
v_res_473_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_468_, v_vals_469_, v_i_470_, v_k_boxed_472_);
lean_dec_ref(v_vals_469_);
lean_dec_ref(v_keys_468_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(lean_object* v_x_474_, size_t v_x_475_, size_t v_x_476_){
_start:
{
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v_es_477_; lean_object* v___x_478_; size_t v___x_479_; size_t v___x_480_; lean_object* v_j_481_; lean_object* v___x_482_; 
v_es_477_ = lean_ctor_get(v_x_474_, 0);
v___x_478_ = lean_box(2);
v___x_479_ = ((size_t)31ULL);
v___x_480_ = lean_usize_land(v_x_475_, v___x_479_);
v_j_481_ = lean_usize_to_nat(v___x_480_);
v___x_482_ = lean_array_get_borrowed(v___x_478_, v_es_477_, v_j_481_);
lean_dec(v_j_481_);
switch(lean_obj_tag(v___x_482_))
{
case 0:
{
lean_object* v_key_483_; lean_object* v_val_484_; size_t v___x_485_; uint8_t v___x_486_; 
v_key_483_ = lean_ctor_get(v___x_482_, 0);
v_val_484_ = lean_ctor_get(v___x_482_, 1);
v___x_485_ = lean_unbox_usize(v_key_483_);
v___x_486_ = lean_usize_dec_eq(v_x_476_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
v___x_487_ = lean_box(0);
return v___x_487_;
}
else
{
lean_object* v___x_488_; 
lean_inc(v_val_484_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v_val_484_);
return v___x_488_;
}
}
case 1:
{
lean_object* v_node_489_; size_t v___x_490_; size_t v___x_491_; 
v_node_489_ = lean_ctor_get(v___x_482_, 0);
v___x_490_ = ((size_t)5ULL);
v___x_491_ = lean_usize_shift_right(v_x_475_, v___x_490_);
v_x_474_ = v_node_489_;
v_x_475_ = v___x_491_;
goto _start;
}
default: 
{
lean_object* v___x_493_; 
v___x_493_ = lean_box(0);
return v___x_493_;
}
}
}
else
{
lean_object* v_ks_494_; lean_object* v_vs_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_ks_494_ = lean_ctor_get(v_x_474_, 0);
v_vs_495_ = lean_ctor_get(v_x_474_, 1);
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_ks_494_, v_vs_495_, v___x_496_, v_x_476_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg___boxed(lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_){
_start:
{
size_t v_x_1864__boxed_501_; size_t v_x_1865__boxed_502_; lean_object* v_res_503_; 
v_x_1864__boxed_501_ = lean_unbox_usize(v_x_499_);
lean_dec(v_x_499_);
v_x_1865__boxed_502_ = lean_unbox_usize(v_x_500_);
lean_dec(v_x_500_);
v_res_503_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_498_, v_x_1864__boxed_501_, v_x_1865__boxed_502_);
lean_dec_ref(v_x_498_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(lean_object* v_x_504_, size_t v_x_505_){
_start:
{
uint64_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; 
v___x_506_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_505_);
v___x_507_ = lean_uint64_to_usize(v___x_506_);
v___x_508_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_504_, v___x_507_, v_x_505_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg___boxed(lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
size_t v_x_1913__boxed_511_; lean_object* v_res_512_; 
v_x_1913__boxed_511_ = lean_unbox_usize(v_x_510_);
lean_dec(v_x_510_);
v_res_512_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_509_, v_x_1913__boxed_511_);
lean_dec_ref(v_x_509_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(lean_object* v_xs_513_, size_t v_v_514_, lean_object* v_i_515_){
_start:
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_array_get_size(v_xs_513_);
v___x_517_ = lean_nat_dec_lt(v_i_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
lean_dec(v_i_515_);
v___x_518_ = lean_box(0);
return v___x_518_;
}
else
{
lean_object* v___x_519_; size_t v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_array_fget_borrowed(v_xs_513_, v_i_515_);
v___x_520_ = lean_unbox_usize(v___x_519_);
v___x_521_ = lean_usize_dec_eq(v___x_520_, v_v_514_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_i_515_, v___x_522_);
lean_dec(v_i_515_);
v_i_515_ = v___x_523_;
goto _start;
}
else
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v_i_515_);
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14___boxed(lean_object* v_xs_526_, lean_object* v_v_527_, lean_object* v_i_528_){
_start:
{
size_t v_v_boxed_529_; lean_object* v_res_530_; 
v_v_boxed_529_ = lean_unbox_usize(v_v_527_);
lean_dec(v_v_527_);
v_res_530_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_526_, v_v_boxed_529_, v_i_528_);
lean_dec_ref(v_xs_526_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(lean_object* v_xs_531_, size_t v_v_532_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11_spec__14(v_xs_531_, v_v_532_, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11___boxed(lean_object* v_xs_535_, lean_object* v_v_536_){
_start:
{
size_t v_v_boxed_537_; lean_object* v_res_538_; 
v_v_boxed_537_ = lean_unbox_usize(v_v_536_);
lean_dec(v_v_536_);
v_res_538_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_xs_535_, v_v_boxed_537_);
lean_dec_ref(v_xs_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(lean_object* v_x_539_, size_t v_x_540_, size_t v_x_541_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v_es_542_; lean_object* v___x_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v_j_546_; lean_object* v_entry_547_; 
v_es_542_ = lean_ctor_get(v_x_539_, 0);
v___x_543_ = lean_box(2);
v___x_544_ = ((size_t)31ULL);
v___x_545_ = lean_usize_land(v_x_540_, v___x_544_);
v_j_546_ = lean_usize_to_nat(v___x_545_);
v_entry_547_ = lean_array_get(v___x_543_, v_es_542_, v_j_546_);
switch(lean_obj_tag(v_entry_547_))
{
case 0:
{
lean_object* v_key_548_; size_t v___x_549_; uint8_t v___x_550_; 
v_key_548_ = lean_ctor_get(v_entry_547_, 0);
lean_inc(v_key_548_);
lean_dec_ref_known(v_entry_547_, 2);
v___x_549_ = lean_unbox_usize(v_key_548_);
lean_dec(v_key_548_);
v___x_550_ = lean_usize_dec_eq(v_x_541_, v___x_549_);
if (v___x_550_ == 0)
{
lean_dec(v_j_546_);
return v_x_539_;
}
else
{
lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_558_; 
lean_inc_ref(v_es_542_);
v_isSharedCheck_558_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v_x_539_, 0);
lean_dec(v_unused_559_);
v___x_552_ = v_x_539_;
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
else
{
lean_dec(v_x_539_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_array_set(v_es_542_, v_j_546_, v___x_543_);
lean_dec(v_j_546_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
case 1:
{
lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_594_; 
lean_inc_ref(v_es_542_);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_x_539_, 0);
lean_dec(v_unused_595_);
v___x_561_ = v_x_539_;
v_isShared_562_ = v_isSharedCheck_594_;
goto v_resetjp_560_;
}
else
{
lean_dec(v_x_539_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_594_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_node_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_593_; 
v_node_563_ = lean_ctor_get(v_entry_547_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v_entry_547_);
if (v_isSharedCheck_593_ == 0)
{
v___x_565_ = v_entry_547_;
v_isShared_566_ = v_isSharedCheck_593_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_node_563_);
lean_dec(v_entry_547_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_593_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
size_t v___x_567_; lean_object* v_entries_568_; size_t v___x_569_; lean_object* v_newNode_570_; lean_object* v___x_571_; 
v___x_567_ = ((size_t)5ULL);
v_entries_568_ = lean_array_set(v_es_542_, v_j_546_, v___x_543_);
v___x_569_ = lean_usize_shift_right(v_x_540_, v___x_567_);
v_newNode_570_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_node_563_, v___x_569_, v_x_541_);
lean_inc_ref(v_newNode_570_);
v___x_571_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_570_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v___x_573_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v_newNode_570_);
v___x_573_ = v___x_565_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_newNode_570_);
v___x_573_ = v_reuseFailAlloc_578_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_574_ = lean_array_set(v_entries_568_, v_j_546_, v___x_573_);
lean_dec(v_j_546_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_574_);
v___x_576_ = v___x_561_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
lean_object* v_val_579_; lean_object* v_fst_580_; lean_object* v_snd_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v_newNode_570_);
lean_del_object(v___x_565_);
v_val_579_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v___x_571_, 1);
v_fst_580_ = lean_ctor_get(v_val_579_, 0);
v_snd_581_ = lean_ctor_get(v_val_579_, 1);
v_isSharedCheck_592_ = !lean_is_exclusive(v_val_579_);
if (v_isSharedCheck_592_ == 0)
{
v___x_583_ = v_val_579_;
v_isShared_584_ = v_isSharedCheck_592_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_snd_581_);
lean_inc(v_fst_580_);
lean_dec(v_val_579_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_592_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_fst_580_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_snd_581_);
v___x_586_ = v_reuseFailAlloc_591_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_array_set(v_entries_568_, v_j_546_, v___x_586_);
lean_dec(v_j_546_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_587_);
v___x_589_ = v___x_561_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_546_);
return v_x_539_;
}
}
}
else
{
lean_object* v_ks_596_; lean_object* v_vs_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_611_; 
v_ks_596_ = lean_ctor_get(v_x_539_, 0);
v_vs_597_ = lean_ctor_get(v_x_539_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_611_ == 0)
{
v___x_599_ = v_x_539_;
v_isShared_600_ = v_isSharedCheck_611_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_vs_597_);
lean_inc(v_ks_596_);
lean_dec(v_x_539_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_611_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; 
v___x_601_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6_spec__11(v_ks_596_, v_x_541_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v___x_603_; 
if (v_isShared_600_ == 0)
{
v___x_603_ = v___x_599_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_ks_596_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_vs_597_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
else
{
lean_object* v_val_605_; lean_object* v_keys_x27_606_; lean_object* v_vals_x27_607_; lean_object* v___x_609_; 
v_val_605_ = lean_ctor_get(v___x_601_, 0);
lean_inc_n(v_val_605_, 2);
lean_dec_ref_known(v___x_601_, 1);
v_keys_x27_606_ = l_Array_eraseIdx___redArg(v_ks_596_, v_val_605_);
v_vals_x27_607_ = l_Array_eraseIdx___redArg(v_vs_597_, v_val_605_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 1, v_vals_x27_607_);
lean_ctor_set(v___x_599_, 0, v_keys_x27_606_);
v___x_609_ = v___x_599_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_keys_x27_606_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_vals_x27_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg___boxed(lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
size_t v_x_1949__boxed_615_; size_t v_x_1950__boxed_616_; lean_object* v_res_617_; 
v_x_1949__boxed_615_ = lean_unbox_usize(v_x_613_);
lean_dec(v_x_613_);
v_x_1950__boxed_616_ = lean_unbox_usize(v_x_614_);
lean_dec(v_x_614_);
v_res_617_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_612_, v_x_1949__boxed_615_, v_x_1950__boxed_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(lean_object* v_x_618_, size_t v_x_619_){
_start:
{
uint64_t v___x_620_; size_t v_h_621_; lean_object* v___x_622_; 
v___x_620_ = lean_usize_to_uint64(v_x_619_);
v_h_621_ = lean_uint64_to_usize(v___x_620_);
v___x_622_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_618_, v_h_621_, v_x_619_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg___boxed(lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
size_t v_x_2087__boxed_625_; lean_object* v_res_626_; 
v_x_2087__boxed_625_ = lean_unbox_usize(v_x_624_);
lean_dec(v_x_624_);
v_res_626_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_623_, v_x_2087__boxed_625_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_627_, lean_object* v_x_628_, size_t v_x_629_, lean_object* v_x_630_){
_start:
{
lean_object* v_ks_631_; lean_object* v_vs_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_659_; 
v_ks_631_ = lean_ctor_get(v_x_627_, 0);
v_vs_632_ = lean_ctor_get(v_x_627_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_627_);
if (v_isSharedCheck_659_ == 0)
{
v___x_634_ = v_x_627_;
v_isShared_635_ = v_isSharedCheck_659_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_vs_632_);
lean_inc(v_ks_631_);
lean_dec(v_x_627_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_659_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = lean_array_get_size(v_ks_631_);
v___x_637_ = lean_nat_dec_lt(v_x_628_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
lean_dec(v_x_628_);
v___x_638_ = lean_box_usize(v_x_629_);
v___x_639_ = lean_array_push(v_ks_631_, v___x_638_);
v___x_640_ = lean_array_push(v_vs_632_, v_x_630_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_640_);
lean_ctor_set(v___x_634_, 0, v___x_639_);
v___x_642_ = v___x_634_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
else
{
lean_object* v_k_x27_644_; size_t v___x_645_; uint8_t v___x_646_; 
v_k_x27_644_ = lean_array_fget_borrowed(v_ks_631_, v_x_628_);
v___x_645_ = lean_unbox_usize(v_k_x27_644_);
v___x_646_ = lean_usize_dec_eq(v_x_629_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_648_; 
if (v_isShared_635_ == 0)
{
v___x_648_ = v___x_634_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_ks_631_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_vs_632_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_x_628_, v___x_649_);
lean_dec(v_x_628_);
v_x_627_ = v___x_648_;
v_x_628_ = v___x_650_;
goto _start;
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_653_ = lean_box_usize(v_x_629_);
v___x_654_ = lean_array_fset(v_ks_631_, v_x_628_, v___x_653_);
v___x_655_ = lean_array_fset(v_vs_632_, v_x_628_, v_x_630_);
lean_dec(v_x_628_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_655_);
lean_ctor_set(v___x_634_, 0, v___x_654_);
v___x_657_ = v___x_634_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
size_t v_x_2098__boxed_664_; lean_object* v_res_665_; 
v_x_2098__boxed_664_ = lean_unbox_usize(v_x_662_);
lean_dec(v_x_662_);
v_res_665_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_660_, v_x_661_, v_x_2098__boxed_664_, v_x_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(lean_object* v_n_666_, size_t v_k_667_, lean_object* v_v_668_){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_n_666_, v___x_669_, v_k_667_, v_v_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_n_671_, lean_object* v_k_672_, lean_object* v_v_673_){
_start:
{
size_t v_k_boxed_674_; lean_object* v_res_675_; 
v_k_boxed_674_ = lean_unbox_usize(v_k_672_);
lean_dec(v_k_672_);
v_res_675_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_671_, v_k_boxed_674_, v_v_673_);
return v_res_675_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(lean_object* v_x_677_, size_t v_x_678_, size_t v_x_679_, size_t v_x_680_, lean_object* v_x_681_){
_start:
{
if (lean_obj_tag(v_x_677_) == 0)
{
lean_object* v_es_682_; size_t v___x_683_; size_t v___x_684_; lean_object* v_j_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_es_682_ = lean_ctor_get(v_x_677_, 0);
v___x_683_ = ((size_t)31ULL);
v___x_684_ = lean_usize_land(v_x_678_, v___x_683_);
v_j_685_ = lean_usize_to_nat(v___x_684_);
v___x_686_ = lean_array_get_size(v_es_682_);
v___x_687_ = lean_nat_dec_lt(v_j_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec(v_j_685_);
lean_dec(v_x_681_);
return v_x_677_;
}
else
{
lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_730_; 
lean_inc_ref(v_es_682_);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_677_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v_x_677_, 0);
lean_dec(v_unused_731_);
v___x_689_ = v_x_677_;
v_isShared_690_ = v_isSharedCheck_730_;
goto v_resetjp_688_;
}
else
{
lean_dec(v_x_677_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_730_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_v_691_; lean_object* v___x_692_; lean_object* v_xs_x27_693_; lean_object* v___y_695_; 
v_v_691_ = lean_array_fget(v_es_682_, v_j_685_);
v___x_692_ = lean_box(0);
v_xs_x27_693_ = lean_array_fset(v_es_682_, v_j_685_, v___x_692_);
switch(lean_obj_tag(v_v_691_))
{
case 0:
{
lean_object* v_key_700_; lean_object* v_val_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_714_; 
v_key_700_ = lean_ctor_get(v_v_691_, 0);
v_val_701_ = lean_ctor_get(v_v_691_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_v_691_);
if (v_isSharedCheck_714_ == 0)
{
v___x_703_ = v_v_691_;
v_isShared_704_ = v_isSharedCheck_714_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_val_701_);
lean_inc(v_key_700_);
lean_dec(v_v_691_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_714_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
size_t v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_unbox_usize(v_key_700_);
v___x_706_ = lean_usize_dec_eq(v_x_680_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_del_object(v___x_703_);
v___x_707_ = lean_box_usize(v_x_680_);
v___x_708_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_700_, v_val_701_, v___x_707_, v_x_681_);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
v___y_695_ = v___x_709_;
goto v___jp_694_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_712_; 
lean_dec(v_val_701_);
lean_dec(v_key_700_);
v___x_710_ = lean_box_usize(v_x_680_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v_x_681_);
lean_ctor_set(v___x_703_, 0, v___x_710_);
v___x_712_ = v___x_703_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_x_681_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
v___y_695_ = v___x_712_;
goto v___jp_694_;
}
}
}
}
case 1:
{
lean_object* v_node_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_727_; 
v_node_715_ = lean_ctor_get(v_v_691_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v_v_691_);
if (v_isSharedCheck_727_ == 0)
{
v___x_717_ = v_v_691_;
v_isShared_718_ = v_isSharedCheck_727_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_node_715_);
lean_dec(v_v_691_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_727_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_719_ = ((size_t)5ULL);
v___x_720_ = lean_usize_shift_right(v_x_678_, v___x_719_);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_x_679_, v___x_721_);
v___x_723_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_node_715_, v___x_720_, v___x_722_, v_x_680_, v_x_681_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_723_);
v___x_725_ = v___x_717_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
v___y_695_ = v___x_725_;
goto v___jp_694_;
}
}
}
default: 
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_box_usize(v_x_680_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
lean_ctor_set(v___x_729_, 1, v_x_681_);
v___y_695_ = v___x_729_;
goto v___jp_694_;
}
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = lean_array_fset(v_xs_x27_693_, v_j_685_, v___y_695_);
lean_dec(v_j_685_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_696_);
v___x_698_ = v___x_689_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
else
{
lean_object* v_ks_732_; lean_object* v_vs_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_753_; 
v_ks_732_ = lean_ctor_get(v_x_677_, 0);
v_vs_733_ = lean_ctor_get(v_x_677_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_x_677_);
if (v_isSharedCheck_753_ == 0)
{
v___x_735_ = v_x_677_;
v_isShared_736_ = v_isSharedCheck_753_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_vs_733_);
lean_inc(v_ks_732_);
lean_dec(v_x_677_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_753_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_ks_732_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_vs_733_);
v___x_738_ = v_reuseFailAlloc_752_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v_newNode_739_; uint8_t v___y_741_; size_t v___x_747_; uint8_t v___x_748_; 
v_newNode_739_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v___x_738_, v_x_680_, v_x_681_);
v___x_747_ = ((size_t)7ULL);
v___x_748_ = lean_usize_dec_le(v___x_747_, v_x_679_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_749_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_739_);
v___x_750_ = lean_unsigned_to_nat(4u);
v___x_751_ = lean_nat_dec_lt(v___x_749_, v___x_750_);
lean_dec(v___x_749_);
v___y_741_ = v___x_751_;
goto v___jp_740_;
}
else
{
v___y_741_ = v___x_748_;
goto v___jp_740_;
}
v___jp_740_:
{
if (v___y_741_ == 0)
{
lean_object* v_ks_742_; lean_object* v_vs_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_ks_742_ = lean_ctor_get(v_newNode_739_, 0);
lean_inc_ref(v_ks_742_);
v_vs_743_ = lean_ctor_get(v_newNode_739_, 1);
lean_inc_ref(v_vs_743_);
lean_dec_ref(v_newNode_739_);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___closed__0);
v___x_746_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_x_679_, v_ks_742_, v_vs_743_, v___x_744_, v___x_745_);
lean_dec_ref(v_vs_743_);
lean_dec_ref(v_ks_742_);
return v___x_746_;
}
else
{
return v_newNode_739_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(size_t v_depth_754_, lean_object* v_keys_755_, lean_object* v_vals_756_, lean_object* v_i_757_, lean_object* v_entries_758_){
_start:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_array_get_size(v_keys_755_);
v___x_760_ = lean_nat_dec_lt(v_i_757_, v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v_i_757_);
return v_entries_758_;
}
else
{
lean_object* v_k_761_; lean_object* v_v_762_; size_t v___x_763_; uint64_t v___x_764_; size_t v_h_765_; size_t v___x_766_; lean_object* v___x_767_; size_t v___x_768_; size_t v___x_769_; size_t v___x_770_; size_t v_h_771_; lean_object* v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v_k_761_ = lean_array_fget_borrowed(v_keys_755_, v_i_757_);
v_v_762_ = lean_array_fget_borrowed(v_vals_756_, v_i_757_);
v___x_763_ = lean_unbox_usize(v_k_761_);
v___x_764_ = l_Lean_Lsp_instHashableRpcRef_hash(v___x_763_);
v_h_765_ = lean_uint64_to_usize(v___x_764_);
v___x_766_ = ((size_t)5ULL);
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = ((size_t)1ULL);
v___x_769_ = lean_usize_sub(v_depth_754_, v___x_768_);
v___x_770_ = lean_usize_mul(v___x_766_, v___x_769_);
v_h_771_ = lean_usize_shift_right(v_h_765_, v___x_770_);
v___x_772_ = lean_nat_add(v_i_757_, v___x_767_);
lean_dec(v_i_757_);
v___x_773_ = lean_unbox_usize(v_k_761_);
lean_inc(v_v_762_);
v___x_774_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_entries_758_, v_h_771_, v_depth_754_, v___x_773_, v_v_762_);
v_i_757_ = v___x_772_;
v_entries_758_ = v___x_774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_776_, lean_object* v_keys_777_, lean_object* v_vals_778_, lean_object* v_i_779_, lean_object* v_entries_780_){
_start:
{
size_t v_depth_boxed_781_; lean_object* v_res_782_; 
v_depth_boxed_781_ = lean_unbox_usize(v_depth_776_);
lean_dec(v_depth_776_);
v_res_782_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_boxed_781_, v_keys_777_, v_vals_778_, v_i_779_, v_entries_780_);
lean_dec_ref(v_vals_778_);
lean_dec_ref(v_keys_777_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg___boxed(lean_object* v_x_783_, lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
size_t v_x_2183__boxed_788_; size_t v_x_2184__boxed_789_; size_t v_x_2185__boxed_790_; lean_object* v_res_791_; 
v_x_2183__boxed_788_ = lean_unbox_usize(v_x_784_);
lean_dec(v_x_784_);
v_x_2184__boxed_789_ = lean_unbox_usize(v_x_785_);
lean_dec(v_x_785_);
v_x_2185__boxed_790_ = lean_unbox_usize(v_x_786_);
lean_dec(v_x_786_);
v_res_791_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_783_, v_x_2183__boxed_788_, v_x_2184__boxed_789_, v_x_2185__boxed_790_, v_x_787_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(lean_object* v_x_792_, size_t v_x_793_, lean_object* v_x_794_){
_start:
{
uint64_t v___x_795_; size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
v___x_795_ = l_Lean_Lsp_instHashableRpcRef_hash(v_x_793_);
v___x_796_ = lean_uint64_to_usize(v___x_795_);
v___x_797_ = ((size_t)1ULL);
v___x_798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_792_, v___x_796_, v___x_797_, v_x_793_, v_x_794_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg___boxed(lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
size_t v_x_2351__boxed_802_; lean_object* v_res_803_; 
v_x_2351__boxed_802_ = lean_unbox_usize(v_x_800_);
lean_dec(v_x_800_);
v_res_803_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_799_, v_x_2351__boxed_802_, v_x_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef(size_t v_r_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___y_807_; lean_object* v_aliveRefs_811_; lean_object* v_refsById_812_; size_t v_nextRef_813_; uint8_t v_wireFormat_814_; lean_object* v___x_815_; 
v_aliveRefs_811_ = lean_ctor_get(v_a_805_, 0);
v_refsById_812_ = lean_ctor_get(v_a_805_, 1);
v_nextRef_813_ = lean_ctor_get_usize(v_a_805_, 2);
v_wireFormat_814_ = lean_ctor_get_uint8(v_a_805_, sizeof(void*)*3);
v___x_815_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_aliveRefs_811_, v_r_804_);
if (lean_obj_tag(v___x_815_) == 1)
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_843_; 
lean_inc_ref(v_refsById_812_);
lean_inc_ref(v_aliveRefs_811_);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_805_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; lean_object* v_unused_845_; 
v_unused_844_ = lean_ctor_get(v_a_805_, 1);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_a_805_, 0);
lean_dec(v_unused_845_);
v___x_817_ = v_a_805_;
v_isShared_818_ = v_isSharedCheck_843_;
goto v_resetjp_816_;
}
else
{
lean_dec(v_a_805_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_843_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_val_819_; lean_object* v_obj_820_; size_t v_id_821_; lean_object* v_rc_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_842_; 
v_val_819_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_val_819_);
lean_dec_ref_known(v___x_815_, 1);
v_obj_820_ = lean_ctor_get(v_val_819_, 0);
v_id_821_ = lean_ctor_get_usize(v_val_819_, 2);
v_rc_822_ = lean_ctor_get(v_val_819_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v_val_819_);
if (v_isSharedCheck_842_ == 0)
{
v___x_824_ = v_val_819_;
v_isShared_825_ = v_isSharedCheck_842_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_rc_822_);
lean_inc(v_obj_820_);
lean_dec(v_val_819_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_842_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_826_ = lean_unsigned_to_nat(1u);
v___x_827_ = lean_nat_sub(v_rc_822_, v___x_826_);
lean_dec(v_rc_822_);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_nat_dec_eq(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_831_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v___x_827_);
v___x_831_ = v___x_824_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_obj_820_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___x_827_);
lean_ctor_set_usize(v_reuseFailAlloc_836_, 2, v_id_821_);
v___x_831_ = v_reuseFailAlloc_836_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_aliveRefs_811_, v_r_804_, v___x_831_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_832_);
v___x_834_ = v___x_817_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_refsById_812_);
lean_ctor_set_usize(v_reuseFailAlloc_835_, 2, v_nextRef_813_);
lean_ctor_set_uint8(v_reuseFailAlloc_835_, sizeof(void*)*3, v_wireFormat_814_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
v___y_807_ = v___x_834_;
goto v___jp_806_;
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
lean_dec(v___x_827_);
lean_del_object(v___x_824_);
lean_dec(v_obj_820_);
v___x_837_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_aliveRefs_811_, v_r_804_);
v___x_838_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_refsById_812_, v_id_821_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_838_);
lean_ctor_set(v___x_817_, 0, v___x_837_);
v___x_840_ = v___x_817_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_838_);
lean_ctor_set_usize(v_reuseFailAlloc_841_, 2, v_nextRef_813_);
lean_ctor_set_uint8(v_reuseFailAlloc_841_, sizeof(void*)*3, v_wireFormat_814_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
v___y_807_ = v___x_840_;
goto v___jp_806_;
}
}
}
}
}
else
{
uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec(v___x_815_);
v___x_846_ = 0;
v___x_847_ = lean_box(v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v_a_805_);
return v___x_848_;
}
v___jp_806_:
{
uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = 1;
v___x_809_ = lean_box(v___x_808_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v___y_807_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_rpcReleaseRef___boxed(lean_object* v_r_849_, lean_object* v_a_850_){
_start:
{
size_t v_r_boxed_851_; lean_object* v_res_852_; 
v_r_boxed_851_ = lean_unbox_usize(v_r_849_);
lean_dec(v_r_849_);
v_res_852_ = l_Lean_Server_rpcReleaseRef(v_r_boxed_851_, v_a_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(lean_object* v_00_u03b2_853_, lean_object* v_x_854_, size_t v_x_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___redArg(v_x_854_, v_x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0___boxed(lean_object* v_00_u03b2_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
size_t v_x_2443__boxed_860_; lean_object* v_res_861_; 
v_x_2443__boxed_860_ = lean_unbox_usize(v_x_859_);
lean_dec(v_x_859_);
v_res_861_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0(v_00_u03b2_857_, v_x_858_, v_x_2443__boxed_860_);
lean_dec_ref(v_x_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(lean_object* v_00_u03b2_862_, lean_object* v_x_863_, size_t v_x_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___redArg(v_x_863_, v_x_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1___boxed(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
size_t v_x_2451__boxed_871_; lean_object* v_res_872_; 
v_x_2451__boxed_871_ = lean_unbox_usize(v_x_869_);
lean_dec(v_x_869_);
v_res_872_ = l_Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1(v_00_u03b2_867_, v_x_868_, v_x_2451__boxed_871_, v_x_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(lean_object* v_00_u03b2_873_, lean_object* v_x_874_, size_t v_x_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___redArg(v_x_874_, v_x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2___boxed(lean_object* v_00_u03b2_877_, lean_object* v_x_878_, lean_object* v_x_879_){
_start:
{
size_t v_x_2462__boxed_880_; lean_object* v_res_881_; 
v_x_2462__boxed_880_ = lean_unbox_usize(v_x_879_);
lean_dec(v_x_879_);
v_res_881_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2(v_00_u03b2_877_, v_x_878_, v_x_2462__boxed_880_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(lean_object* v_00_u03b2_882_, lean_object* v_x_883_, size_t v_x_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___redArg(v_x_883_, v_x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3___boxed(lean_object* v_00_u03b2_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
size_t v_x_2470__boxed_889_; lean_object* v_res_890_; 
v_x_2470__boxed_889_ = lean_unbox_usize(v_x_888_);
lean_dec(v_x_888_);
v_res_890_ = l_Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3(v_00_u03b2_886_, v_x_887_, v_x_2470__boxed_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(lean_object* v_00_u03b2_891_, lean_object* v_x_892_, size_t v_x_893_, size_t v_x_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___redArg(v_x_892_, v_x_893_, v_x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0___boxed(lean_object* v_00_u03b2_896_, lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
size_t v_x_2478__boxed_900_; size_t v_x_2479__boxed_901_; lean_object* v_res_902_; 
v_x_2478__boxed_900_ = lean_unbox_usize(v_x_898_);
lean_dec(v_x_898_);
v_x_2479__boxed_901_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_res_902_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0(v_00_u03b2_896_, v_x_897_, v_x_2478__boxed_900_, v_x_2479__boxed_901_);
lean_dec_ref(v_x_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(lean_object* v_00_u03b2_903_, lean_object* v_x_904_, size_t v_x_905_, size_t v_x_906_, size_t v_x_907_, lean_object* v_x_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___redArg(v_x_904_, v_x_905_, v_x_906_, v_x_907_, v_x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2___boxed(lean_object* v_00_u03b2_910_, lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
size_t v_x_2489__boxed_916_; size_t v_x_2490__boxed_917_; size_t v_x_2491__boxed_918_; lean_object* v_res_919_; 
v_x_2489__boxed_916_ = lean_unbox_usize(v_x_912_);
lean_dec(v_x_912_);
v_x_2490__boxed_917_ = lean_unbox_usize(v_x_913_);
lean_dec(v_x_913_);
v_x_2491__boxed_918_ = lean_unbox_usize(v_x_914_);
lean_dec(v_x_914_);
v_res_919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2(v_00_u03b2_910_, v_x_911_, v_x_2489__boxed_916_, v_x_2490__boxed_917_, v_x_2491__boxed_918_, v_x_915_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(lean_object* v_00_u03b2_920_, lean_object* v_x_921_, size_t v_x_922_, size_t v_x_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___redArg(v_x_921_, v_x_922_, v_x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4___boxed(lean_object* v_00_u03b2_925_, lean_object* v_x_926_, lean_object* v_x_927_, lean_object* v_x_928_){
_start:
{
size_t v_x_2506__boxed_929_; size_t v_x_2507__boxed_930_; lean_object* v_res_931_; 
v_x_2506__boxed_929_ = lean_unbox_usize(v_x_927_);
lean_dec(v_x_927_);
v_x_2507__boxed_930_ = lean_unbox_usize(v_x_928_);
lean_dec(v_x_928_);
v_res_931_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__2_spec__4(v_00_u03b2_925_, v_x_926_, v_x_2506__boxed_929_, v_x_2507__boxed_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(lean_object* v_00_u03b2_932_, lean_object* v_x_933_, size_t v_x_934_, size_t v_x_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___redArg(v_x_933_, v_x_934_, v_x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6___boxed(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
size_t v_x_2517__boxed_941_; size_t v_x_2518__boxed_942_; lean_object* v_res_943_; 
v_x_2517__boxed_941_ = lean_unbox_usize(v_x_939_);
lean_dec(v_x_939_);
v_x_2518__boxed_942_ = lean_unbox_usize(v_x_940_);
lean_dec(v_x_940_);
v_res_943_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Server_rpcReleaseRef_spec__3_spec__6(v_00_u03b2_937_, v_x_938_, v_x_2517__boxed_941_, v_x_2518__boxed_942_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_944_, lean_object* v_keys_945_, lean_object* v_vals_946_, lean_object* v_heq_947_, lean_object* v_i_948_, size_t v_k_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___redArg(v_keys_945_, v_vals_946_, v_i_948_, v_k_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_951_, lean_object* v_keys_952_, lean_object* v_vals_953_, lean_object* v_heq_954_, lean_object* v_i_955_, lean_object* v_k_956_){
_start:
{
size_t v_k_boxed_957_; lean_object* v_res_958_; 
v_k_boxed_957_ = lean_unbox_usize(v_k_956_);
lean_dec(v_k_956_);
v_res_958_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Server_rpcReleaseRef_spec__0_spec__0_spec__1(v_00_u03b2_951_, v_keys_952_, v_vals_953_, v_heq_954_, v_i_955_, v_k_boxed_957_);
lean_dec_ref(v_vals_953_);
lean_dec_ref(v_keys_952_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_959_, lean_object* v_n_960_, size_t v_k_961_, lean_object* v_v_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___redArg(v_n_960_, v_k_961_, v_v_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_964_, lean_object* v_n_965_, lean_object* v_k_966_, lean_object* v_v_967_){
_start:
{
size_t v_k_boxed_968_; lean_object* v_res_969_; 
v_k_boxed_968_ = lean_unbox_usize(v_k_966_);
lean_dec(v_k_966_);
v_res_969_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4(v_00_u03b2_964_, v_n_965_, v_k_boxed_968_, v_v_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_970_, size_t v_depth_971_, lean_object* v_keys_972_, lean_object* v_vals_973_, lean_object* v_heq_974_, lean_object* v_i_975_, lean_object* v_entries_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___redArg(v_depth_971_, v_keys_972_, v_vals_973_, v_i_975_, v_entries_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_978_, lean_object* v_depth_979_, lean_object* v_keys_980_, lean_object* v_vals_981_, lean_object* v_heq_982_, lean_object* v_i_983_, lean_object* v_entries_984_){
_start:
{
size_t v_depth_boxed_985_; lean_object* v_res_986_; 
v_depth_boxed_985_ = lean_unbox_usize(v_depth_979_);
lean_dec(v_depth_979_);
v_res_986_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__5(v_00_u03b2_978_, v_depth_boxed_985_, v_keys_980_, v_vals_981_, v_heq_982_, v_i_983_, v_entries_984_);
lean_dec_ref(v_vals_981_);
lean_dec_ref(v_keys_980_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_987_, lean_object* v_x_988_, lean_object* v_x_989_, size_t v_x_990_, lean_object* v_x_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___redArg(v_x_988_, v_x_989_, v_x_990_, v_x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
size_t v_x_2535__boxed_998_; lean_object* v_res_999_; 
v_x_2535__boxed_998_ = lean_unbox_usize(v_x_996_);
lean_dec(v_x_996_);
v_res_999_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Server_rpcReleaseRef_spec__1_spec__2_spec__4_spec__7(v_00_u03b2_993_, v_x_994_, v_x_995_, v_x_2535__boxed_998_, v_x_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0(lean_object* v_inst_1000_, lean_object* v_a_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_apply_1(v_inst_1000_, v_a_1001_);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___y_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(lean_object* v_inst_1005_, lean_object* v___x_1006_, lean_object* v___x_1007_, lean_object* v_j_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_201__overap_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_apply_1(v_inst_1005_, v_j_1008_);
v___x_201__overap_1011_ = l_MonadExcept_ofExcept___redArg(v___x_1006_, v___x_1007_, v___x_1010_);
lean_inc_ref(v___y_1009_);
v___x_1012_ = lean_apply_1(v___x_201__overap_1011_, v___y_1009_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed(lean_object* v_inst_1013_, lean_object* v___x_1014_, lean_object* v___x_1015_, lean_object* v_j_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1(v_inst_1013_, v___x_1014_, v___x_1015_, v_j_1016_, v___y_1017_);
lean_dec_ref(v___y_1017_);
return v_res_1018_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9));
v___x_1039_ = l_ReaderT_instMonad___redArg(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___f_1041_; 
v___x_1040_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1041_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1041_, 0, v___x_1040_);
return v___f_1041_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___f_1043_; 
v___x_1042_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1043_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1043_, 0, v___x_1042_);
return v___f_1043_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___f_1045_; 
v___x_1044_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1045_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1045_, 0, v___x_1044_);
return v___f_1045_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___f_1047_; 
v___x_1046_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___f_1047_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1047_, 0, v___x_1046_);
return v___f_1047_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1049_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1049_, 0, lean_box(0));
lean_closure_set(v___x_1049_, 1, lean_box(0));
lean_closure_set(v___x_1049_, 2, v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16(void){
_start:
{
lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___f_1050_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__11);
v___x_1051_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__15);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___f_1050_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1054_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1054_, 0, lean_box(0));
lean_closure_set(v___x_1054_, 1, lean_box(0));
lean_closure_set(v___x_1054_, 2, v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18(void){
_start:
{
lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___f_1055_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__14);
v___f_1056_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__13);
v___f_1057_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__12);
v___x_1058_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__17);
v___x_1059_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__16);
v___x_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___x_1058_);
lean_ctor_set(v___x_1060_, 2, v___f_1057_);
lean_ctor_set(v___x_1060_, 3, v___f_1056_);
lean_ctor_set(v___x_1060_, 4, v___f_1055_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1062_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1062_, 0, lean_box(0));
lean_closure_set(v___x_1062_, 1, lean_box(0));
lean_closure_set(v___x_1062_, 2, v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__19);
v___x_1064_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__18);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1067_ = lean_alloc_closure((void*)(l_ExceptT_tryCatch), 6, 3);
lean_closure_set(v___x_1067_, 0, lean_box(0));
lean_closure_set(v___x_1067_, 1, lean_box(0));
lean_closure_set(v___x_1067_, 2, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(lean_object* v_inst_1068_, lean_object* v_inst_1069_){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_toApplicative_1072_; lean_object* v_toPure_1073_; lean_object* v___f_1074_; lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; 
v___x_1070_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__10);
v___x_1071_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v_toApplicative_1072_ = lean_ctor_get(v___x_1070_, 0);
v_toPure_1073_ = lean_ctor_get(v_toApplicative_1072_, 1);
v___f_1074_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1074_, 0, v_inst_1069_);
lean_inc(v_toPure_1073_);
v___f_1075_ = lean_alloc_closure((void*)(l_instMonadExceptOfExceptTOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1075_, 0, v_toPure_1073_);
v___x_1076_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__21);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___f_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = l_instMonadExceptOfMonadExceptOf___redArg(v___x_1077_);
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1079_, 0, v_inst_1068_);
lean_closure_set(v___f_1079_, 1, v___x_1071_);
lean_closure_set(v___f_1079_, 2, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___f_1074_);
lean_ctor_set(v___x_1080_, 1, v___f_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOfFromJsonOfToJson(lean_object* v_00_u03b1_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg(v_inst_1082_, v_inst_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__0(lean_object* v_inst_1085_, lean_object* v___x_1086_, lean_object* v_v_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_fst_1090_; lean_object* v_snd_1091_; 
if (lean_obj_tag(v_v_1087_) == 0)
{
lean_object* v___x_1094_; 
lean_dec_ref(v_inst_1085_);
v___x_1094_ = lean_box(0);
v_fst_1090_ = v___x_1094_;
v_snd_1091_ = v___y_1088_;
goto v___jp_1089_;
}
else
{
lean_object* v_rpcEncode_1095_; lean_object* v_val_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1106_; 
v_rpcEncode_1095_ = lean_ctor_get(v_inst_1085_, 0);
lean_inc_ref(v_rpcEncode_1095_);
lean_dec_ref(v_inst_1085_);
v_val_1096_ = lean_ctor_get(v_v_1087_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_v_1087_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1098_ = v_v_1087_;
v_isShared_1099_ = v_isSharedCheck_1106_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_val_1096_);
lean_dec(v_v_1087_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1106_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v_fst_1101_; lean_object* v_snd_1102_; lean_object* v___x_1104_; 
v___x_1100_ = lean_apply_2(v_rpcEncode_1095_, v_val_1096_, v___y_1088_);
v_fst_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_fst_1101_);
v_snd_1102_ = lean_ctor_get(v___x_1100_, 1);
lean_inc(v_snd_1102_);
lean_dec_ref(v___x_1100_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v_fst_1101_);
v___x_1104_ = v___x_1098_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_fst_1101_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
v_fst_1090_ = v___x_1104_;
v_snd_1091_ = v_snd_1102_;
goto v___jp_1089_;
}
}
}
v___jp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = l_Lean_Option_toJson___redArg(v___x_1086_, v_fst_1090_);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v_snd_1091_);
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1(lean_object* v___f_1109_, lean_object* v_inst_1110_, lean_object* v_j_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_Option_fromJson_x3f___redArg(v___f_1109_, v_j_1111_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec_ref(v_inst_1110_);
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
else
{
lean_object* v_a_1122_; 
v_a_1122_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1113_, 1);
if (lean_obj_tag(v_a_1122_) == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v_inst_1110_);
v___x_1123_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___closed__0));
return v___x_1123_;
}
else
{
lean_object* v_rpcDecode_1124_; lean_object* v_val_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1149_; 
v_rpcDecode_1124_ = lean_ctor_get(v_inst_1110_, 1);
lean_inc_ref(v_rpcDecode_1124_);
lean_dec_ref(v_inst_1110_);
v_val_1125_ = lean_ctor_get(v_a_1122_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_a_1122_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1127_ = v_a_1122_;
v_isShared_1128_ = v_isSharedCheck_1149_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_val_1125_);
lean_dec(v_a_1122_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1149_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; 
lean_inc_ref(v___y_1112_);
v___x_1129_ = lean_apply_2(v_rpcDecode_1124_, v_val_1125_, v___y_1112_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_del_object(v___x_1127_);
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1148_; 
v_a_1138_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1140_ = v___x_1129_;
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1129_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v_a_1138_);
v___x_1143_ = v___x_1127_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed(lean_object* v___f_1150_, lean_object* v_inst_1151_, lean_object* v_j_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Server_instRpcEncodableOption___redArg___lam__1(v___f_1150_, v_inst_1151_, v_j_1152_, v___y_1153_);
lean_dec_ref(v___y_1153_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption___redArg(lean_object* v_inst_1157_){
_start:
{
lean_object* v___x_1158_; lean_object* v___f_1159_; lean_object* v___f_1160_; lean_object* v___f_1161_; lean_object* v___x_1162_; 
v___x_1158_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1157_);
v___f_1159_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1159_, 0, v_inst_1157_);
lean_closure_set(v___f_1159_, 1, v___x_1158_);
v___f_1160_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableOption___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1161_, 0, v___f_1160_);
lean_closure_set(v___f_1161_, 1, v_inst_1157_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___f_1159_);
lean_ctor_set(v___x_1162_, 1, v___f_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableOption(lean_object* v_00_u03b1_1163_, lean_object* v_inst_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Server_instRpcEncodableOption___redArg(v_inst_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__0(lean_object* v_inst_1166_, lean_object* v___x_1167_, lean_object* v___x_1168_, lean_object* v_a_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_rpcEncode_1171_; size_t v_sz_1172_; size_t v___x_1173_; lean_object* v___x_648__overap_1174_; lean_object* v___x_1175_; lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1185_; 
v_rpcEncode_1171_ = lean_ctor_get(v_inst_1166_, 0);
lean_inc_ref(v_rpcEncode_1171_);
lean_dec_ref(v_inst_1166_);
v_sz_1172_ = lean_array_size(v_a_1169_);
v___x_1173_ = ((size_t)0ULL);
v___x_648__overap_1174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1167_, v_rpcEncode_1171_, v_sz_1172_, v___x_1173_, v_a_1169_);
v___x_1175_ = lean_apply_1(v___x_648__overap_1174_, v___y_1170_);
v_fst_1176_ = lean_ctor_get(v___x_1175_, 0);
v_snd_1177_ = lean_ctor_get(v___x_1175_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1179_ = v___x_1175_;
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_snd_1177_);
lean_inc(v_fst_1176_);
lean_dec(v___x_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = l_Lean_Array_toJson___redArg(v___x_1168_, v_fst_1176_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1181_);
v___x_1183_ = v___x_1179_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_snd_1177_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1(lean_object* v___f_1186_, lean_object* v_inst_1187_, lean_object* v___x_1188_, lean_object* v_b_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Array_fromJson_x3f___redArg(v___f_1186_, v_b_1189_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v___x_1188_);
lean_dec_ref(v_inst_1187_);
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v_rpcDecode_1201_; size_t v_sz_1202_; size_t v___x_1203_; lean_object* v___x_662__overap_1204_; lean_object* v___x_1205_; 
v_a_1200_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1191_, 1);
v_rpcDecode_1201_ = lean_ctor_get(v_inst_1187_, 1);
lean_inc_ref(v_rpcDecode_1201_);
lean_dec_ref(v_inst_1187_);
v_sz_1202_ = lean_array_size(v_a_1200_);
v___x_1203_ = ((size_t)0ULL);
v___x_662__overap_1204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1188_, v_rpcDecode_1201_, v_sz_1202_, v___x_1203_, v_a_1200_);
lean_inc_ref(v___y_1190_);
v___x_1205_ = lean_apply_1(v___x_662__overap_1204_, v___y_1190_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed(lean_object* v___f_1206_, lean_object* v_inst_1207_, lean_object* v___x_1208_, lean_object* v_b_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_Server_instRpcEncodableArray___redArg___lam__1(v___f_1206_, v_inst_1207_, v___x_1208_, v_b_1209_, v___y_1210_);
lean_dec_ref(v___y_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray___redArg(lean_object* v_inst_1238_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___f_1241_; lean_object* v___x_1242_; lean_object* v___f_1243_; lean_object* v___f_1244_; lean_object* v___x_1245_; 
v___x_1239_ = ((lean_object*)(l_Lean_Server_instRpcEncodableArray___redArg___closed__9));
v___x_1240_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1238_);
v___f_1241_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1241_, 0, v_inst_1238_);
lean_closure_set(v___f_1241_, 1, v___x_1239_);
lean_closure_set(v___f_1241_, 2, v___x_1240_);
v___x_1242_ = lean_obj_once(&l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20, &l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20_once, _init_l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__20);
v___f_1243_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1244_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableArray___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1244_, 0, v___f_1243_);
lean_closure_set(v___f_1244_, 1, v_inst_1238_);
lean_closure_set(v___f_1244_, 2, v___x_1242_);
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___f_1241_);
lean_ctor_set(v___x_1245_, 1, v___f_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableArray(lean_object* v_00_u03b1_1246_, lean_object* v_inst_1247_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Server_instRpcEncodableArray___redArg(v_inst_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__0(lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v___x_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v_rpcEncode_1256_; lean_object* v___x_1257_; lean_object* v_fst_1258_; lean_object* v_snd_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1278_; 
v_fst_1254_ = lean_ctor_get(v_x_1252_, 0);
lean_inc(v_fst_1254_);
v_snd_1255_ = lean_ctor_get(v_x_1252_, 1);
lean_inc(v_snd_1255_);
lean_dec_ref(v_x_1252_);
v_rpcEncode_1256_ = lean_ctor_get(v_inst_1249_, 0);
lean_inc_ref(v_rpcEncode_1256_);
lean_dec_ref(v_inst_1249_);
v___x_1257_ = lean_apply_2(v_rpcEncode_1256_, v_fst_1254_, v___y_1253_);
v_fst_1258_ = lean_ctor_get(v___x_1257_, 0);
v_snd_1259_ = lean_ctor_get(v___x_1257_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1261_ = v___x_1257_;
v_isShared_1262_ = v_isSharedCheck_1278_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_snd_1259_);
lean_inc(v_fst_1258_);
lean_dec(v___x_1257_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1278_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v_rpcEncode_1263_; lean_object* v___x_1264_; lean_object* v_fst_1265_; lean_object* v_snd_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1277_; 
v_rpcEncode_1263_ = lean_ctor_get(v_inst_1250_, 0);
lean_inc_ref(v_rpcEncode_1263_);
lean_dec_ref(v_inst_1250_);
v___x_1264_ = lean_apply_2(v_rpcEncode_1263_, v_snd_1255_, v_snd_1259_);
v_fst_1265_ = lean_ctor_get(v___x_1264_, 0);
v_snd_1266_ = lean_ctor_get(v___x_1264_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1268_ = v___x_1264_;
v_isShared_1269_ = v_isSharedCheck_1277_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snd_1266_);
lean_inc(v_fst_1265_);
lean_dec(v___x_1264_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1277_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v_fst_1265_);
lean_ctor_set(v___x_1268_, 0, v_fst_1258_);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_fst_1258_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_fst_1265_);
v___x_1271_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
lean_inc_ref(v___x_1251_);
v___x_1272_ = l_Lean_Prod_toJson___redArg(v___x_1251_, v___x_1251_, v___x_1271_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_snd_1266_);
lean_ctor_set(v___x_1261_, 0, v___x_1272_);
v___x_1274_ = v___x_1261_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_snd_1266_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1(lean_object* v___f_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_j_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1284_; 
lean_inc_ref(v___f_1279_);
v___x_1284_ = l_Lean_Prod_fromJson_x3f___redArg(v___f_1279_, v___f_1279_, v_j_1282_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_inst_1281_);
lean_dec_ref(v_inst_1280_);
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
lean_object* v_a_1293_; lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1331_; 
v_a_1293_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1284_, 1);
v_fst_1294_ = lean_ctor_get(v_a_1293_, 0);
v_snd_1295_ = lean_ctor_get(v_a_1293_, 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_a_1293_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1297_ = v_a_1293_;
v_isShared_1298_ = v_isSharedCheck_1331_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_snd_1295_);
lean_inc(v_fst_1294_);
lean_dec(v_a_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1331_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v_rpcDecode_1299_; lean_object* v___x_1300_; 
v_rpcDecode_1299_ = lean_ctor_get(v_inst_1280_, 1);
lean_inc_ref(v_rpcDecode_1299_);
lean_dec_ref(v_inst_1280_);
lean_inc_ref(v___y_1283_);
v___x_1300_ = lean_apply_2(v_rpcDecode_1299_, v_fst_1294_, v___y_1283_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_del_object(v___x_1297_);
lean_dec(v_snd_1295_);
lean_dec_ref(v_inst_1281_);
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v_rpcDecode_1310_; lean_object* v___x_1311_; 
v_a_1309_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1300_, 1);
v_rpcDecode_1310_ = lean_ctor_get(v_inst_1281_, 1);
lean_inc_ref(v_rpcDecode_1310_);
lean_dec_ref(v_inst_1281_);
lean_inc_ref(v___y_1283_);
v___x_1311_ = lean_apply_2(v_rpcDecode_1310_, v_snd_1295_, v___y_1283_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_a_1309_);
lean_del_object(v___x_1297_);
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1330_; 
v_a_1320_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1322_ = v___x_1311_;
v_isShared_1323_ = v_isSharedCheck_1330_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1311_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1330_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 1, v_a_1320_);
lean_ctor_set(v___x_1297_, 0, v_a_1309_);
v___x_1325_ = v___x_1297_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1309_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1327_; 
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1325_);
v___x_1327_ = v___x_1322_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed(lean_object* v___f_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_j_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Server_instRpcEncodableProd___redArg___lam__1(v___f_1332_, v_inst_1333_, v_inst_1334_, v_j_1335_, v___y_1336_);
lean_dec_ref(v___y_1336_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd___redArg(lean_object* v_inst_1338_, lean_object* v_inst_1339_){
_start:
{
lean_object* v___x_1340_; lean_object* v___f_1341_; lean_object* v___f_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; 
v___x_1340_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__0));
lean_inc_ref(v_inst_1339_);
lean_inc_ref(v_inst_1338_);
v___f_1341_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1341_, 0, v_inst_1338_);
lean_closure_set(v___f_1341_, 1, v_inst_1339_);
lean_closure_set(v___f_1341_, 2, v___x_1340_);
v___f_1342_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOption___redArg___closed__1));
v___f_1343_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableProd___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1343_, 0, v___f_1342_);
lean_closure_set(v___f_1343_, 1, v_inst_1338_);
lean_closure_set(v___f_1343_, 2, v_inst_1339_);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___f_1341_);
lean_ctor_set(v___x_1344_, 1, v___f_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableProd(lean_object* v_00_u03b1_1345_, lean_object* v_00_u03b2_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Server_instRpcEncodableProd___redArg(v_inst_1347_, v_inst_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0(lean_object* v_inst_1350_, lean_object* v_fn_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_rpcEncode_1353_; lean_object* v___x_1354_; lean_object* v_fst_1355_; lean_object* v_snd_1356_; lean_object* v___x_1357_; 
v_rpcEncode_1353_ = lean_ctor_get(v_inst_1350_, 0);
lean_inc_ref(v_rpcEncode_1353_);
lean_dec_ref(v_inst_1350_);
v___x_1354_ = lean_apply_1(v_fn_1351_, v___y_1352_);
v_fst_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_fst_1355_);
v_snd_1356_ = lean_ctor_get(v___x_1354_, 1);
lean_inc(v_snd_1356_);
lean_dec_ref(v___x_1354_);
v___x_1357_ = lean_apply_2(v_rpcEncode_1353_, v_fst_1355_, v_snd_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(lean_object* v_inst_1358_, lean_object* v___x_1359_, lean_object* v_j_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_rpcDecode_1362_; lean_object* v___x_1363_; 
v_rpcDecode_1362_ = lean_ctor_get(v_inst_1358_, 1);
lean_inc_ref(v_rpcDecode_1362_);
lean_dec_ref(v_inst_1358_);
lean_inc_ref(v___y_1361_);
v___x_1363_ = lean_apply_2(v_rpcDecode_1362_, v_j_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v___x_1359_);
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1380_; 
v_a_1372_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1374_ = v___x_1363_;
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1363_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 5);
lean_closure_set(v___x_1376_, 0, lean_box(0));
lean_closure_set(v___x_1376_, 1, lean_box(0));
lean_closure_set(v___x_1376_, 2, v___x_1359_);
lean_closure_set(v___x_1376_, 3, lean_box(0));
lean_closure_set(v___x_1376_, 4, v_a_1372_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1376_);
v___x_1378_ = v___x_1374_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed(lean_object* v_inst_1381_, lean_object* v___x_1382_, lean_object* v_j_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1(v_inst_1381_, v___x_1382_, v_j_1383_, v___y_1384_);
lean_dec_ref(v___y_1384_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(lean_object* v_inst_1386_){
_start:
{
lean_object* v___f_1387_; lean_object* v___x_1388_; lean_object* v___f_1389_; lean_object* v___x_1390_; 
lean_inc_ref(v_inst_1386_);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1387_, 0, v_inst_1386_);
v___x_1388_ = ((lean_object*)(l_Lean_Server_instRpcEncodableOfFromJsonOfToJson___redArg___closed__9));
v___f_1389_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1389_, 0, v_inst_1386_);
lean_closure_set(v___f_1389_, 1, v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___f_1387_);
lean_ctor_set(v___x_1390_, 1, v___f_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableStateMRpcObjectStore(lean_object* v_00_u03b1_1391_, lean_object* v_inst_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Server_instRpcEncodableStateMRpcObjectStore___redArg(v_inst_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(lean_object* v_inst_1394_, lean_object* v_r_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v___x_1397_; lean_object* v_fst_1398_; lean_object* v_snd_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1418_; 
v___x_1397_ = l_Lean_Server_rpcStoreRef___redArg(v_inst_1394_, v_r_1395_, v_a_1396_);
v_fst_1398_ = lean_ctor_get(v___x_1397_, 0);
v_snd_1399_ = lean_ctor_get(v___x_1397_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1401_ = v___x_1397_;
v_isShared_1402_ = v_isSharedCheck_1418_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_snd_1399_);
lean_inc(v_fst_1398_);
lean_dec(v___x_1397_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1418_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___y_1404_; uint8_t v_wireFormat_1415_; 
v_wireFormat_1415_ = lean_ctor_get_uint8(v_snd_1399_, sizeof(void*)*3);
if (v_wireFormat_1415_ == 0)
{
lean_object* v___x_1416_; 
v___x_1416_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
v___y_1404_ = v___x_1416_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1417_; 
v___x_1417_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
v___y_1404_ = v___x_1417_;
goto v___jp_1403_;
}
v___jp_1403_:
{
size_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1405_ = lean_unbox_usize(v_fst_1398_);
lean_dec(v_fst_1398_);
v___x_1406_ = lean_usize_to_nat(v___x_1405_);
v___x_1407_ = l_Lean_bignumToJson(v___x_1406_);
lean_inc_ref(v___y_1404_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v___x_1407_);
lean_ctor_set(v___x_1401_, 0, v___y_1404_);
v___x_1409_ = v___x_1401_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___y_1404_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1410_ = lean_box(0);
v___x_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1409_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = l_Lean_Json_mkObj(v___x_1411_);
lean_dec_ref_known(v___x_1411_, 2);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v_snd_1399_);
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg___boxed(lean_object* v_inst_1419_, lean_object* v_r_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1419_, v_r_1420_, v_a_1421_);
lean_dec_ref(v_r_1420_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(lean_object* v_00_u03b1_1423_, lean_object* v_inst_1424_, lean_object* v_r_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(v_inst_1424_, v_r_1425_, v_a_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed(lean_object* v_00_u03b1_1428_, lean_object* v_inst_1429_, lean_object* v_r_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode(v_00_u03b1_1428_, v_inst_1429_, v_r_1430_, v_a_1431_);
lean_dec_ref(v_r_1430_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(lean_object* v_inst_1434_, lean_object* v_j_1435_, lean_object* v_a_1436_){
_start:
{
uint8_t v_wireFormat_1437_; lean_object* v___x_1438_; lean_object* v___y_1440_; 
v_wireFormat_1437_ = lean_ctor_get_uint8(v_a_1436_, sizeof(void*)*3);
v___x_1438_ = ((lean_object*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___closed__0));
if (v_wireFormat_1437_ == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__0));
v___y_1440_ = v___x_1453_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = ((lean_object*)(l_Lean_Lsp_RpcWireFormat_refFieldName___closed__1));
v___y_1440_ = v___x_1454_;
goto v___jp_1439_;
}
v___jp_1439_:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1435_, v___x_1438_, v___y_1440_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_inst_1434_);
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
else
{
lean_object* v_a_1450_; size_t v___x_1451_; lean_object* v___x_1452_; 
v_a_1450_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1451_ = lean_unbox_usize(v_a_1450_);
lean_dec(v_a_1450_);
v___x_1452_ = l_Lean_Server_rpcGetRef___redArg(v_inst_1434_, v___x_1451_, v_a_1436_);
return v___x_1452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg___boxed(lean_object* v_inst_1455_, lean_object* v_j_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v_inst_1455_, v_j_1456_, v_a_1457_);
lean_dec_ref(v_a_1457_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(lean_object* v_00_u03b1_1459_, lean_object* v_inst_1460_, lean_object* v_j_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v_inst_1460_, v_j_1461_, v_a_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed(lean_object* v_00_u03b1_1464_, lean_object* v_inst_1465_, lean_object* v_j_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode(v_00_u03b1_1464_, v_inst_1465_, v_j_1466_, v_a_1467_);
lean_dec_ref(v_a_1467_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(lean_object* v_inst_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_inc(v_inst_1469_);
v___x_1470_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___boxed), 4, 2);
lean_closure_set(v___x_1470_, 0, lean_box(0));
lean_closure_set(v___x_1470_, 1, v_inst_1469_);
v___x_1471_ = lean_alloc_closure((void*)(l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___boxed), 4, 2);
lean_closure_set(v___x_1471_, 0, lean_box(0));
lean_closure_set(v___x_1471_, 1, v_inst_1469_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName(lean_object* v_00_u03b1_1473_, lean_object* v_inst_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName___redArg(v_inst_1474_);
return v___x_1475_;
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Rpc_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instInhabitedRpcRef_default = _init_l_Lean_Lsp_instInhabitedRpcRef_default();
l_Lean_Lsp_instInhabitedRpcRef = _init_l_Lean_Lsp_instInhabitedRpcRef();
res = l___private_Lean_Server_Rpc_Basic_0__Lean_Server_initFn_00___x40_Lean_Server_Rpc_Basic_1605303199____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_freshWithRpcRefId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_freshWithRpcRefId);
lean_dec_ref(res);
l_Lean_Server_rpcStoreRef___redArg___boxed__const__1 = _init_l_Lean_Server_rpcStoreRef___redArg___boxed__const__1();
lean_mark_persistent(l_Lean_Server_rpcStoreRef___redArg___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Rpc_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Dynamic(uint8_t builtin);
lean_object* initialize_Lean_Data_Json_FromToJson_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_FromToJson_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Rpc_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Rpc_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Rpc_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
